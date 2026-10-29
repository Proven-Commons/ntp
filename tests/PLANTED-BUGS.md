# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `Ntp/Packet.lean` (38 bugs), `Ntp/Time.lean` (8) or `Main.lean` (11), tested with `tests/run_tests.py --count 2000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed. So does a run on other inputs than the unchanged code's: every run must give the same `- Inputs SHA-256:` line, which here is dc7c1a52625cf15fff32335937e7c1700b512af3c4a3332b0d5ff65a24316f23.

| Planted bug | Failures |
|---|---|
| none | 0 |
| an input shorter than asked for is taken whole, as a reader that runs off the end | 3164 |
| numbers are read little-endian | 31206 |
| numbers are written little-endian | 15461 |
| the octet 128 is read as +128, not -128 | 72 |
| a negative number is written one less | 14670 |
| the version is read from two bits | 29740 |
| the mode is read from two bits | 27022 |
| version 2 is accepted | 135 |
| version 5 is accepted | 131 |
| mode 0 is accepted | 73 |
| mode 6 is accepted | 77 |
| mode 7 is accepted | 71 |
| the leap indicator keeps only its low bit | 3056 |
| Poll is read as unsigned, as NTPsec and ntplib read it | 2975 |
| Precision is read as unsigned | 28329 |
| the root delay and the root dispersion are swapped | 31194 |
| the origin and receive timestamps are swapped | 31198 |
| 16 octets after the fields are taken as a MAC | 81 |
| 21 to 23 octets after the fields are taken as a MAC, as chrony's 20 to 24 would | 241 |
| a field is read while 20 octets are left, not 24, so 24 octets are a field | 1111 |
| a field is read only while 28 octets are left, so 28 octets are a MAC | 521 |
| a field is read while 16 or more octets are left, as Wireshark reads them, so a last field without a MAC may be 16 octets | 2266 |
| a field of Length 12 is accepted | 9 |
| a field of Length 4 is accepted, as ntpd-rs accepts it | 26 |
| a field Length need not be a multiple of 4 | 71 |
| a field Length past the end is cut short at the end, as a clamping reader would | 1839 |
| a field's body is taken as Length less 8 | 4012 |
| the fields come back in reverse order | 2456 |
| a crypto-NAK is taken after fields too | 33 |
| four octets of any value are a crypto-NAK | 72 |
| version 3 packets get extension fields, as ntpd reads a tail of more than 24 octets | 103 |
| at most two extension fields are read | 1110 |
| in version 3, any 24 octets or fewer are the MAC, as ntpd-rs reads them | 150 |
| version 3 is read with the version 4 rule | 103 |
| a field's Length is written without its four header octets | 1841 |
| the mode is written from two bits | 13368 |
| the root dispersion is written before the root delay | 15455 |
| the MAC is not written | 1561 |
| the raw value 0 converts to 1900, in Ntp/Time.lean | 11 |
| a raw value of 2^64 converts, in Ntp/Time.lean | 2 |
| the era is left out of the conversion, in Ntp/Time.lean | 882 |
| the epoch is a day off, in Ntp/Time.lean | 1108 |
| the fraction is taken modulo 2^32 - 1, in Ntp/Time.lean | 1075 |
| a fraction of 2^32 is taken, in Ntp/Time.lean | 7 |
| the era is found by division rounding toward zero, in Ntp/Time.lean | 835 |
| the first instant of an era gets the timestamp 0, in Ntp/Time.lean | 10 |
| Main.lean: upper-case hex digits are read | 5 |
| Main.lean: an empty hex field is read as no octets | 3 |
| Main.lean: hex is printed in upper case | 17991 |
| Main.lean: the two hex digits of an octet are printed the wrong way round | 18029 |
| Main.lean: the sign of a negative number is dropped | 16027 |
| Main.lean: Poll and Precision are printed the wrong way round | 15734 |
| Main.lean: `-` for no extension fields is not read | 13666 |
| Main.lean: `encode` reads the root delay and dispersion the wrong way round | 15455 |
| Main.lean: `encode` answers OK for a packet that is not valid | 88 |
| Main.lean: the CR of a CR LF line ending is kept | 6014 |
| Main.lean: wrong arguments exit with 0 | 8 |

Bugs caught: 57 of 57
