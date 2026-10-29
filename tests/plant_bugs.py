#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Ntp/Packet.lean, or to Ntp/Time.lean
or Main.lean where its entry says so. The script copies the project to a
temporary folder, without .lake/build, .lake/oracles and .git, plants
one bug at a time, runs tests/run_tests.py there with a small count and
without the oracles, and records how many failures the tests report. So
every failure counted is the tool disagreeing with the model of RFC 5905
and RFC 7822. Every planted bug must give at least one failure. The
unchanged copy must give none. A bug that stops the executable from
building is not a catch: the tests then give up, and the bug counts as
missed. So is any run that gives up (its record shows `- Failures: 1
(why)`), a run that dies without writing its record, and one whose exit
status does not match the failures it records. Every run must also test
the same inputs as the unchanged copy: its record must give the same
`- Inputs SHA-256:` line, or the bug counts as missed, since its
failures might come from inputs the unchanged copy was not run on. The
tests build only the executable (`lake build ntp`), so a bug that breaks
a proof still runs.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Ntp/Packet.lean"
TIME = "Ntp/Time.lean"
MAIN = "Main.lean"

# (what the bug does, the text as written, the text with the bug[, file])
BUGS = [
    ("an input shorter than asked for is taken whole, as a reader that runs off the end",
     "  if c.length = w then some (c, b.drop w) else none",
     "  if c.length ≤ w then some (c, b.drop w) else none"),
    ("numbers are read little-endian",
     "  bs.foldl (fun n b => n * 256 + b.toNat) 0",
     "  bs.foldr (fun b n => n * 256 + b.toNat) 0"),
    ("numbers are written little-endian",
     "  | w + 1, n => writeBE w (n / 256) ++ [(n % 256).toUInt8]",
     "  | w + 1, n => [(n % 256).toUInt8] ++ writeBE w (n / 256)"),
    ("the octet 128 is read as +128, not -128",
     "  if n < 128 then n else (n : Int) - 256",
     "  if n ≤ 128 then n else (n : Int) - 256"),
    ("a negative number is written one less",
     "  if z < 0 then (z + 256).toNat else z.toNat",
     "  if z < 0 then (z + 255).toNat else z.toNat"),
    ("the version is read from two bits",
     "  let version := lvm / 8 % 8",
     "  let version := lvm / 8 % 4"),
    ("the mode is read from two bits",
     "  let mode := lvm % 8",
     "  let mode := lvm % 4"),
    ("version 2 is accepted",
     "  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)",
     "  guard ((version == 2 || version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)"),
    ("version 5 is accepted",
     "  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)",
     "  guard (3 ≤ version && version ≤ 5 && 1 ≤ mode && mode ≤ 5)"),
    ("mode 0 is accepted",
     "  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)",
     "  guard ((version == 3 || version == 4) && 0 ≤ mode && mode ≤ 5)"),
    ("mode 6 is accepted",
     "  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)",
     "  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 6)"),
    ("mode 7 is accepted",
     "  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)",
     "  guard ((version == 3 || version == 4) && (1 ≤ mode && mode ≤ 5 || mode == 7))"),
    ("the leap indicator keeps only its low bit",
     "  pure ({ leap := lvm / 64, version, mode, stratum, poll := toSigned poll,",
     "  pure ({ leap := lvm / 64 % 2, version, mode, stratum, poll := toSigned poll,"),
    ("Poll is read as unsigned, as NTPsec and ntplib read it",
     "  pure ({ leap := lvm / 64, version, mode, stratum, poll := toSigned poll,",
     "  pure ({ leap := lvm / 64, version, mode, stratum, poll := poll,"),
    ("Precision is read as unsigned",
     "          precision := toSigned precision, rootDelay, rootDispersion, refId, reference,",
     "          precision := precision, rootDelay, rootDispersion, refId, reference,"),
    ("the root delay and the root dispersion are swapped",
     "          precision := toSigned precision, rootDelay, rootDispersion, refId, reference,",
     "          precision := toSigned precision, rootDelay := rootDispersion, rootDispersion := rootDelay, "
     "refId, reference,"),
    ("the origin and receive timestamps are swapped",
     "          origin, receive, transmit }, r)",
     "          origin := receive, receive := origin, transmit }, r)"),
    ("16 octets after the fields are taken as a MAC",
     "  t.length == 0 || t.length == 20 || t.length == 24",
     "  t.length == 0 || t.length == 16 || t.length == 20 || t.length == 24"),
    ("21 to 23 octets after the fields are taken as a MAC, as chrony's 20 to 24 would",
     "  t.length == 0 || t.length == 20 || t.length == 24",
     "  t.length == 0 || (20 ≤ t.length && t.length ≤ 24)"),
    ("a field is read while 20 octets are left, not 24, so 24 octets are a field",
     "    if longer 24 t then do",
     "    if longer 20 t then do"),
    ("a field is read only while 28 octets are left, so 28 octets are a MAC",
     "    if longer 24 t then do",
     "    if longer 28 t then do"),
    ("a field is read while 16 or more octets are left, as Wireshark reads them, so a last field "
     "without a MAC may be 16 octets",
     "    if longer 24 t then do",
     "    if longer 15 t then do"),
    ("a field of Length 12 is accepted",
     "      guard (16 ≤ len && len % 4 == 0)",
     "      guard (12 ≤ len && len % 4 == 0)"),
    ("a field of Length 4 is accepted, as ntpd-rs accepts it",
     "      guard (16 ≤ len && len % 4 == 0)",
     "      guard (4 ≤ len && len % 4 == 0)"),
    ("a field Length need not be a multiple of 4",
     "      guard (16 ≤ len && len % 4 == 0)",
     "      guard (16 ≤ len && len % 2 == 0)"),
    ("a field Length past the end is cut short at the end, as a clamping reader would",
     "      let (body, r) ← take? (len - 4) r",
     "      let (body, r) := (r.take (len - 4), r.drop (len - 4))"),
    ("a field's body is taken as Length less 8",
     "      let (body, r) ← take? (len - 4) r",
     "      let (body, r) ← take? (len - 8) r"),
    ("the fields come back in reverse order",
     "      pure ({ type, body } :: fields, mac)",
     "      pure (fields ++ [{ type, body }], mac)"),
    ("a crypto-NAK is taken after fields too",
     "    else if macLength t then some ([], t) else none",
     "    else if macLength t || t = [0, 0, 0, 0] then some ([], t) else none"),
    ("four octets of any value are a crypto-NAK",
     "  if t = [0, 0, 0, 0] then some ([], t)",
     "  if t.length = 4 then some ([], t)"),
    ("version 3 packets get extension fields, as ntpd reads a tail of more than 24 octets",
     "  else if version = 4 then readFields (t.length + 1) t",
     "  else if version = 4 || version = 3 then readFields (t.length + 1) t"),
    ("at most two extension fields are read",
     "  else if version = 4 then readFields (t.length + 1) t",
     "  else if version = 4 then readFields 3 t"),
    ("in version 3, any 24 octets or fewer are the MAC, as ntpd-rs reads them",
     "  else if macLength t then some ([], t)\n",
     "  else if t.length ≤ 24 then some ([], t)\n"),
    ("version 3 is read with the version 4 rule",
     "  let (exts, mac) ← readTail header.version t",
     "  let (exts, mac) ← readTail 4 t"),
    ("a field's Length is written without its four header octets",
     "  writeBE 2 e.type ++ writeBE 2 (e.body.length + 4) ++ e.body",
     "  writeBE 2 e.type ++ writeBE 2 e.body.length ++ e.body"),
    ("the mode is written from two bits",
     "  writeBE 1 (h.leap * 64 + h.version * 8 + h.mode) ++ writeBE 1 h.stratum ++",
     "  writeBE 1 (h.leap * 64 + h.version * 8 + h.mode % 4) ++ writeBE 1 h.stratum ++"),
    ("the root dispersion is written before the root delay",
     "  writeBE 4 h.rootDelay ++ writeBE 4 h.rootDispersion ++ writeBE 4 h.refId ++",
     "  writeBE 4 h.rootDispersion ++ writeBE 4 h.rootDelay ++ writeBE 4 h.refId ++"),
    ("the MAC is not written",
     "  p.exts.flatMap writeField ++ p.mac",
     "  p.exts.flatMap writeField"),
    ("the raw value 0 converts to 1900, in Ntp/Time.lean",
     "  if raw = 0 ∨ 18446744073709551616 ≤ raw then none",
     "  if 18446744073709551616 ≤ raw then none", TIME),
    ("a raw value of 2^64 converts, in Ntp/Time.lean",
     "  if raw = 0 ∨ 18446744073709551616 ≤ raw then none",
     "  if raw = 0 ∨ 18446744073709551617 ≤ raw then none", TIME),
    ("the era is left out of the conversion, in Ntp/Time.lean",
     "  else some (era * 4294967296 + (raw / 4294967296 : Nat) - 2208988800, raw % 4294967296)",
     "  else some ((raw / 4294967296 : Nat) - 2208988800, raw % 4294967296)", TIME),
    ("the epoch is a day off, in Ntp/Time.lean",
     "  else some (era * 4294967296 + (raw / 4294967296 : Nat) - 2208988800, raw % 4294967296)",
     "  else some (era * 4294967296 + (raw / 4294967296 : Nat) - 2208902400, raw % 4294967296)", TIME),
    ("the fraction is taken modulo 2^32 - 1, in Ntp/Time.lean",
     "  else some (era * 4294967296 + (raw / 4294967296 : Nat) - 2208988800, raw % 4294967296)",
     "  else some (era * 4294967296 + (raw / 4294967296 : Nat) - 2208988800, raw % 4294967295)", TIME),
    ("a fraction of 2^32 is taken, in Ntp/Time.lean",
     "  if 4294967296 ≤ fraction then none",
     "  if 4294967297 ≤ fraction then none", TIME),
    ("the era is found by division rounding toward zero, in Ntp/Time.lean",
     "    let raw := (s % 4294967296).toNat * 4294967296 + fraction",
     "    let raw := (s.tmod 4294967296).toNat * 4294967296 + fraction", TIME),
    ("the first instant of an era gets the timestamp 0, in Ntp/Time.lean",
     "    if raw = 0 then none else some (s / 4294967296, raw)",
     "    some (s / 4294967296, raw)", TIME),
    ("Main.lean: upper-case hex digits are read",
     "  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)",
     "  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)", MAIN),
    ("Main.lean: an empty hex field is read as no octets",
     "  if f = \"-\" then some [] else if f.isEmpty then none else (hexBytes f.toList #[]).map (·.toList)",
     "  if f = \"-\" ∨ f.isEmpty then some [] else (hexBytes f.toList #[]).map (·.toList)", MAIN),
    ("Main.lean: hex is printed in upper case",
     "  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)",
     "  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)", MAIN),
    ("Main.lean: the two hex digits of an octet are printed the wrong way round",
     "  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])",
     "  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat % 16), hexDigit (b.toNat / 16)])", MAIN),
    ("Main.lean: the sign of a negative number is dropped",
     "  | '-' :: cs => (decimal (String.ofList cs)).map fun n => -(n : Int)",
     "  | '-' :: cs => (decimal (String.ofList cs)).map fun n => (n : Int)", MAIN),
    ("Main.lean: Poll and Precision are printed the wrong way round",
     "    toString h.poll, toString h.precision, toString h.rootDelay, toString h.rootDispersion,",
     "    toString h.precision, toString h.poll, toString h.rootDelay, toString h.rootDispersion,", MAIN),
    ("Main.lean: `-` for no extension fields is not read",
     "  if s = \"-\" then some [] else (s.splitOn \",\").mapM readField",
     "  (s.splitOn \",\").mapM readField", MAIN),
    ("Main.lean: `encode` reads the root delay and dispersion the wrong way round",
     "        rootDelay := ← decimal rd, rootDispersion := ← decimal rs, refId := ← decimal ri,",
     "        rootDelay := ← decimal rs, rootDispersion := ← decimal rd, refId := ← decimal ri,", MAIN),
    ("Main.lean: `encode` answers OK for a packet that is not valid",
     "    pure (if decode b = some p then s!\"OK {toHex b}\" else \"FAIL\")",
     "    pure s!\"OK {toHex b}\"", MAIN),
    ("Main.lean: the CR of a CR LF line ending is kept",
     "    String.ofList (if cs.getLast? = some '\\r' then cs.dropLast else cs)",
     "    String.ofList cs", MAIN),
    ("Main.lean: wrong arguments exit with 0",
     "  | _ => IO.eprintln usage; return 2",
     "  | _ => IO.eprintln usage; return 0", MAIN),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish; and the SHA-256 of the inputs the run made. A run that
    dies writes no record, so the old one is removed first rather than
    read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count), "--no-oracles"],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}", None
    text = record.read_text(encoding="utf-8")
    m = re.search(r"^- Failures: (\d+)(.*)$", text, re.M)
    if m is None or m.group(2).strip():
        return None, out, None  # the run gave up, for example the bug did not build: not a catch
    d = re.search(r"^- Inputs SHA-256: ([0-9a-f]{64})", text, re.M)
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}", None
    return n, None, d and d.group(1)


def ignore(folder, names):
    """Leave out the build, the oracle builds, the git folder and old
    records: the copy builds its own executable."""
    leave = {"PLANTED-BUGS.md", "__pycache__", ".git"}
    if Path(folder).resolve() == (ROOT / ".lake").resolve():
        leave |= {"build", "oracles"}
    return [n for n in names if n in leave]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=2000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "ntp"
        shutil.copytree(ROOT, copy, symlinks=True, ignore=ignore)
        n, err, inputs = failures(copy, args.count)
        rows.append(("none", n, ""))
        if n != 0 or inputs is None:
            missed += 1
        print(f"none: {n} failures, inputs {inputs}" + (" (did not build or did not finish)" if err else ""),
              flush=True)
        if err:
            print(err[-2000:], flush=True)
        for what, line, bug, *where in BUGS:
            name = where[0] if where else CODE
            code = copy / name
            original = code.read_text(encoding="utf-8")
            if original.count(line) != 1:
                sys.exit(f"{name} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err, got = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            note = "" if err or got == inputs else " (other inputs than the unchanged copy's)"
            rows.append((what, n, note))
            if not n or note:
                missed += 1
            print(f"{what}: {n} failures{note}" + (" (did not build or did not finish)" if err else ""),
                  flush=True)
            if err:
                print(err[-2000:], flush=True)
    counts = {f: sum(1 for b in BUGS if (b[3] if len(b) > 3 else CODE) == f) for f in (CODE, TIME, MAIN)}
    lines = ["# Planted bugs", "",
             f"Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `{CODE}` "
             f"({counts[CODE]} bugs), `{TIME}` ({counts[TIME]}) or `{MAIN}` ({counts[MAIN]}), tested with "
             f"`tests/run_tests.py --count {args.count} --no-oracles`, which builds only the executable and "
             "compares it with the model alone. Every bug must give failures, and the unchanged code none. "
             "A bug that does not build, or a run that gives up or dies, counts as missed. So does a run on "
             "other inputs than the unchanged code's: every run must give the same `- Inputs SHA-256:` line, "
             f"which here is {inputs or 'missing'}.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n}{note} |"
              for what, n, note in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n, note in rows[1:] if n and not note)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
