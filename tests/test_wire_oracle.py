import json
from pathlib import Path
import random
import struct
import subprocess
import sys
import unittest
from fractions import Fraction

from wire_oracle import WireError, answer, decode, read_header, timestamp_unix

HERE = Path(__file__).parent


class WireContractTests(unittest.TestCase):
    def test_fixed_vectors(self):
        for line in (HERE / 'wire_vectors.jsonl').read_text().splitlines():
            case = json.loads(line)
            with self.subTest(case=case['id']):
                self.assertEqual(answer(case['request']), case['expect'])

    def test_header_against_struct_unpack(self):
        rng = random.Random(20261028)
        for _ in range(2000):
            raw = bytearray(rng.randbytes(48))
            raw[0] = (raw[0] & 0xc7) | (rng.choice([3, 4]) << 3)
            first, stratum, poll, precision, delay, dispersion, ref, *stamps = struct.unpack('!BBbbII4s4Q', raw)
            got = read_header(raw)
            self.assertEqual([got[k] for k in ('leap','version','mode','stratum','poll','precision')],
                             [first >> 6, (first >> 3) & 7, first & 7, stratum, poll, precision])
            self.assertEqual((got['root_delay_bits'], got['root_dispersion_bits'], got['reference_id_hex']),
                             (delay, dispersion, ref.hex()))
            self.assertEqual([s['raw'] for s in got['timestamps']], stamps)

    def test_explicit_era_and_unknown(self):
        for era in (-1, 0, 1, 2):
            self.assertIsNone(timestamp_unix(0, era))
            self.assertEqual(timestamp_unix(1, era), Fraction(era * 2**32 - 2208988800) + Fraction(1, 2**32))
        self.assertEqual(timestamp_unix(2208988800 << 32, 0), 0)
        self.assertEqual(timestamp_unix(1, 1)-timestamp_unix(1, 0), 2**32)
        for era in (None, True, 1.5):
            with self.assertRaises(WireError):
                timestamp_unix(1, era)
        for raw in (-1, 2**64, True):
            with self.assertRaises(WireError):
                timestamp_unix(raw, 0)

    def test_all_extension_lengths_at_boundary(self):
        header = bytes.fromhex('23' + '00'*47)
        for length in range(0, 81):
            field = b'\xfe\xfe' + length.to_bytes(2, 'big') + bytes(max(0, length-4))
            for mac in (0, 4, 20, 24):
                packet = header + field + bytes(mac)
                expected = length >= (16 if mac else 28) and length % 4 == 0
                try:
                    got = decode(packet, mac)
                except WireError:
                    self.assertFalse(expected, (length, mac))
                else:
                    self.assertTrue(expected, (length, mac))
                    self.assertEqual(got['extensions'][0]['length'], length)
                    self.assertEqual(got['mac_length'], mac)
        # A maximum-size aligned extension; no heuristic 24-byte-tail cutoff.
        field = b'\xfe\xfe\xff\xfc' + bytes(65528)
        self.assertEqual(decode(header + field, 0)['extensions'][0]['length'], 65532)

    def test_mac_ambiguity_is_context(self):
        header = bytes.fromhex('23' + '00'*47)
        tail = b'\xfe\xfe\x00\x14' + bytes(16)
        self.assertEqual(decode(header+tail, 20)['mac_hex'], tail.hex())
        with self.assertRaisesRegex(WireError, 'short_final_extension_without_mac'):
            decode(header+tail, 0)
        for n in (-1, 8, 16, 28, None, True):
            self.assertEqual(answer({'packet_hex':header.hex(), 'mac_length':n}),
                             {'error':'unsupported_mac_length'})

    def test_cli_and_adapter_failure_detection(self):
        good = subprocess.run([sys.executable, str(HERE/'check_vectors.py')], capture_output=True)
        self.assertEqual(good.returncode, 0, good.stderr)
        bad = subprocess.run([sys.executable, str(HERE/'check_vectors.py'), '--', sys.executable,
                              '-c', 'print("{}")'], capture_output=True)
        self.assertNotEqual(bad.returncode, 0)
        self.assertIn(b'answers for', bad.stderr)
        wrong = subprocess.run([sys.executable, str(HERE/'check_vectors.py'), '--', sys.executable,
                                '-c', 'import sys; [print("{}") for line in sys.stdin]'],
                               capture_output=True)
        self.assertNotEqual(wrong.returncode, 0)
        self.assertIn(b'header-distinct-fields', wrong.stderr)

    def test_malformed_requests(self):
        for request in (None, [], {}, {'packet_hex':'xx','mac_length':0}):
            self.assertEqual(answer(request), {'error':'malformed_request'})


if __name__ == '__main__':
    unittest.main()
