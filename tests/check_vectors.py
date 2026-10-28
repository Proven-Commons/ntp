#!/usr/bin/env python3
"""Run the fixed contract vectors against a JSON-line parser adapter."""

import argparse
import json
from pathlib import Path
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('command', nargs=argparse.REMAINDER,
                    help='adapter command, optionally after --')
    args = ap.parse_args()
    command = args.command
    if command[:1] == ['--']:
        command = command[1:]
    if not command:
        command = [sys.executable, str(Path(__file__).with_name('wire_oracle.py'))]
    cases = [json.loads(line) for line in Path(__file__).with_name('wire_vectors.jsonl').read_text().splitlines()]
    try:
        run = subprocess.run(command, input=''.join(json.dumps(c['request'])+'\n' for c in cases),
                             capture_output=True, text=True, timeout=30)
        if run.returncode:
            raise ValueError(f'adapter exit {run.returncode}: {run.stderr[:300]}')
        answers = [json.loads(line) for line in run.stdout.splitlines()]
        if len(answers) != len(cases):
            raise ValueError(f'{len(answers)} answers for {len(cases)} vectors')
        failures = [c['id'] for c, got in zip(cases, answers) if got != c['expect']]
    except (OSError, subprocess.TimeoutExpired, ValueError) as e:
        print(f'FAIL: {e}', file=sys.stderr)
        return 1
    for name in failures:
        print(f'FAIL: {name}', file=sys.stderr)
    print(f'{len(cases)-len(failures)}/{len(cases)} wire vectors agree')
    return bool(failures)


if __name__ == '__main__':
    sys.exit(main())
