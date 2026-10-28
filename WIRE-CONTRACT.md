# Draft wire contract

This is a review target for the existing parser author. Python fixtures and an executable oracle are included; no Lean parser or proof is added. Issue 1 remains open.

The header follows [RFC 5905 sections 6 and 7.3](https://www.rfc-editor.org/rfc/rfc5905.html#section-7.3). Offsets are bytes, integers are big endian, and timestamp order is reference, origin, receive, transmit.

| Offset | Bytes | Field |
|---|---|---|
| 0 | 1 | Leap: bits 7–6; version: 5–3; mode: 2–0 |
| 1 | 1 | Stratum |
| 2 | 1 | Signed poll exponent |
| 3 | 1 | Signed precision exponent |
| 4 | 4 | Root delay bits |
| 8 | 4 | Root dispersion bits |
| 12 | 4 | Reference identifier bytes |
| 16, 24, 32, 40 | 8 each | Seconds (32 bits), fraction (32 bits) |

Version 3 or 4 is this draft's supported set. All modes and strata are preserved; clock-selection validity is separate. Root fixed-point fields remain raw bits. A zero 64-bit timestamp means unknown. A nonzero fraction with zero seconds is known. Conversion requires an external integer era and returns exact rational Unix seconds. No era is guessed from the clock or packet.

Extension framing follows [RFC 7822 section 3](https://www.rfc-editor.org/rfc/rfc7822.html#section-3). Each extension includes its four-byte header in its length, is at least 16 bytes, has four-byte alignment, and stays before the MAC. Without a MAC, the final extension is at least 28 bytes. Unknown types remain opaque, including padding.

The caller supplies `mac_length`: 0, 4, 20, or 24. The oracle preserves those bytes, including a four-byte crypto-NAK, without authenticating them. It does not guess whether a 20-byte tail is an extension or MAC. Negotiated longer MACs and extension-specific requirements need separate context and are outside this contract.

Run `python3 -m unittest discover -s tests -v`. Feed JSON lines to `python3 tests/wire_oracle.py`. Each fixture has `id`, `request`, and a complete `expect` response. A future parser adapter can use this schema unchanged. Independent review of this contract is required before integration.
