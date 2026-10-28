# ntp: reading the NTP packet, proved

NTP, the Network Time Protocol, sets the clocks of computers across the internet, and its packets come from anyone who can send a UDP datagram to port 123. A program that reads them takes lengths from the packet and follows them: extension fields carry their own Length, and a MAC may or may not follow them. ntpd has followed lengths from the packet that it did not check, such as the Autokey value length of CVE-2014-9750, which could leak its memory, and readers still disagree on what follows the header of a version 3 packet.

This library reads and writes one NTP packet, the whole of one UDP payload, in Lean:

- the 48-octet header of RFC 5905 (Figure 8): leap indicator, version, mode, stratum, poll, precision, root delay, root dispersion, reference ID and the four timestamps;
- the extension fields after it (RFC 7822), each as its Field Type and its octets, and the MAC at the end, told apart by the rule RFC 7822 sets for that;
- timestamps, converted to Unix time and back given their era (RFC 5905 section 6).

Machine-checked proofs show:

- **The reader accepts exactly the packets of the specification, and gives back what they hold.** It accepts a payload exactly when it is the octets of a packet that `Spec/Defs.lean` writes down from RFC 5905 and RFC 7822, and gives that packet. So it reads each payload one way only.
- **Lengths in the packet are checked.** A payload shorter than the header is refused, and so is an extension field whose Length runs past the end of the packet, wherever it is. So are versions other than 3 and 4, and modes 0, 6 and 7.
- **Writing and reading agree.** The writer writes each valid packet as the RFCs lay it out, and reading what it wrote gives the packet back.
- **Timestamp conversion is exact.** A timestamp in a given era converts to the exact Unix time, and back. The timestamp 0, which means unknown, converts to nothing in every era, never to 1900.

It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there. Differential tests against other NTP implementations are not in the repo yet.

This reads and writes NTP packets. It does not keep time: it is not an NTP client or server, and it does not check MACs.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and the differential tests are still to come, so this is not verified.

## Use it

From Lean, on `List UInt8`, with the structures of `Spec/Defs.lean`:

- `Ntp.decode : List UInt8 → Option Packet`: the packet in one UDP payload: its header, its extension fields and its MAC.
- `Ntp.encode : Packet → List UInt8`: the octets of a packet.
- `Ntp.toUnix : Int → Nat → Option (Int × Nat)`: the Unix time of a 64-bit timestamp in an era, as whole seconds and a fraction in units of 2^-32 seconds.
- `Ntp.fromUnix : Int → Nat → Option (Int × Nat)`: the era and the 64-bit timestamp of a Unix time.

`SPEC.md` says what each function does.

## What is proved

The statements are in `Spec.lean`. The definitions they use are in `Spec/Defs.lean`, written from RFC 5905 (Figure 8 and sections 6 and 7.3) and RFC 7822 (section 3), and the proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The decoder accepts exactly the octets of a valid packet, and gives that packet. | `Spec.decode_iff` |
| The encoder writes every valid packet as RFC 5905 Figure 8 and RFC 7822 Figure 14 lay it out. | `Spec.encode_eq` |
| Encoding a packet and decoding the octets gives the packet back exactly when it is valid. | `Spec.decode_encode` |
| Encoding a decoded packet gives back the octets it was read from. | `Spec.encode_decode` |
| A payload shorter than the 48-octet header is refused. | `Spec.decode_short` |
| A packet whose version is not 3 or 4 is refused. | `Spec.decode_version` |
| A packet of mode 0, 6 or 7 is refused. | `Spec.decode_mode` |
| An extension field whose Length runs past the end of the packet is refused, wherever it is and whatever the rest of the packet holds. | `Spec.decode_ext_overrun` |
| The timestamp 0 converts to no Unix time, in any era. | `Spec.toUnix_zero` |
| A timestamp in an era converts to exactly its Unix time: `era * 2^32` plus its seconds and fraction, less 2,208,988,800 seconds. | `Spec.toUnix_spec` |
| Converting a timestamp to Unix time and back gives it back, and so does converting a Unix time to a timestamp and back. | `Spec.fromUnix_toUnix`, `Spec.toUnix_fromUnix` |
| A client request and a server reply captured on a network, read field by field; a captured reply with two extension fields; packets with a MAC, a crypto-NAK, and version 3; the end of era 0 in 2036, worked by hand. Fourteen packets that each break one rule are refused. | `Spec.examples`, `Spec.rejects` |

The packets this reader accepts are those of version 3 or 4 and mode 1 to 5, whose extension fields each have a Length that is a multiple of 4 from 16 to 65532, whose MAC is none, 20 or 24 octets, or four zero octets (the crypto-NAK) with no extension field, whose last extension field is at least 28 octets when there is no MAC, and which, in version 3, have no extension field. `SPEC.md` gives the RFC text for each rule, and says where chrony and ntpd choose differently.

## What is not proved

- **The MAC.** It is given as its octets. No digest is computed or checked.
- **What extension fields hold.** Autokey, Network Time Security and every other field are given as their Field Type and octets. Lengths inside a field, such as the Autokey value length of CVE-2014-9750, are not read.
- **The meaning of the header.** The reference ID, root delay and root dispersion are given as their bits, and nothing checks that the timestamps fit together.
- **Which era a timestamp is in.** The caller gives it, from its own clock. Leap seconds are outside the conversion.
- **The protocol.** No on-wire exchange, clock filter, peer selection or clock discipline. Modes 6 and 7 are refused, not read.
- **Encoding a packet that is not valid.** What the encoder writes for one is not specified.
- **Time and memory.** No proof bounds them.
- **Reading requests and printing answers in `Main.lean`.** The differential tests will cover them.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number and integer arithmetic, `UInt8`, and lists.
- The operating system and hardware it runs on.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`) and Python 3.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean. The two test scripts come with the differential tests, which are not in the repo yet.

## Layout

- `Ntp/Packet.lean` and `Ntp/Time.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the RFCs.
- `Spec/Examples.lean`: the inputs of the examples: three captured packets, and packets written by hand from them.
- `Proofs.lean` and `Proofs/`: the proofs.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
