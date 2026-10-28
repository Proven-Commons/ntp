# ntp

A Lean parser for the NTP wire packet. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. The first parser slice is claimed in plan issue 1 and remains under its author's ownership. The specification has not been approved by a reviewer.

## Wire contract under review

[WIRE-CONTRACT.md](WIRE-CONTRACT.md) proposes a contract for the parser author to review. It comes with 79 fixed packet vectors, a Python reference oracle, and a JSON adapter runner. It adds no Lean implementation or proof. The protocol contract still needs independent review before integration.

Run the fixtures and boundary checks:

```
python3 -m unittest discover -s tests -v
python3 tests/check_vectors.py
```

A future parser adapter can consume the same fixtures with `python3 tests/check_vectors.py -- COMMAND ARGUMENTS`. The runner checks every response and fails on a missing answer, wrong answer, nonzero exit, or timeout.

## First slice

The NTP packet header, 48 bytes, plus extension fields parsed as length framed items. Fields are leap indicator, version, mode, stratum, poll, precision, root delay, root dispersion, reference id, and four timestamps. Timestamps convert to seconds since the epoch, with era handling written in the plan.

This is distinct from the rfc repo, which parses RFC 3339 text timestamps. NTP is a binary wire format, not a text format.

## Main claim

Decoding a packet gives the same timestamps back. A packet shorter than its header is rejected. An extension field that runs past the end of the packet is rejected. A version outside the supported set is rejected.

## Test oracles

- ntpd and chrony.
- Python ntplib.
- Wireshark captures.

## Score

16 out of 18, first pass score in mission issue 19, the round 4 sheet. Created at the org owner's direction on that sheet, on the judgement that the slice, claim, and oracles are sound and that it duplicates no existing repo.

## What is not in this slice

- Clock discipline.
- Peer selection.
- Network Time Security.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
