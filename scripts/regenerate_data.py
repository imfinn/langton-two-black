#!/usr/bin/env python3
"""Regenerate candidate Lean literals from preserved dumps, without touching the proof checkout."""
import argparse
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--calc', type=Path, default=Path('code/calc'))
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    calc = args.calc.resolve()
    if not calc.is_file():
        parser.error('compile code/calc first, or pass --calc pointing to the compiled checker')
    dest = args.output.resolve()
    dest.mkdir(parents=True, exist_ok=False)
    lean = dest / 'lean'
    shutil.copytree(repo / 'lean', lean, ignore=shutil.ignore_patterns('.lake', '__pycache__'))
    raw = dest / 'raw'
    raw.mkdir()
    for mode in ('leandump', 'chandump', 'perpdump', 'pardump'):
        with gzip.open(repo / 'runs' / (mode + '.txt.gz'), 'rb') as src:
            (raw / (mode + '.txt')).write_bytes(src.read())
    seeds = raw / 'level1-seeds.txt'
    rows = []
    for line in (raw / 'chandump.txt').read_text().splitlines():
        if line.startswith('P '):
            _, x, y, base = line.split()
            rows.append(f'-2 -2 {x} {y} {base}\n')
    if len(rows) != 22:
        raise RuntimeError(f'expected 22 channel seeds, found {len(rows)}')
    seeds.write_text(''.join(rows))
    env = os.environ.copy()
    env['CALC'] = str(calc)
    code = repo / 'code'
    commands = [
        ['gen_lean_hints.py', str(seeds), str(lean / 'TwoBlack/Level1Data.lean'), 'level1Families'],
        ['gen_lean_parents.py', str(raw / 'leandump.txt'), str(lean), '32'],
        ['gen_lean_channels.py', str(raw / 'chandump.txt'), str(lean)],
        ['gen_lean_perp.py', str(raw / 'chandump.txt'), str(raw / 'perpdump.txt'), str(lean)],
        ['gen_lean_par.py', str(raw / 'chandump.txt'), str(raw / 'pardump.txt'), str(lean)],
        ['gen_lean_part.py', str(raw / 'chandump.txt'), str(lean)],
    ]
    for argv in commands:
        cmd = [sys.executable, str(code / argv[0]), *argv[1:]]
        print('Running', argv[0], flush=True)
        with (dest / (argv[0] + '.log')).open('w') as log:
            subprocess.run(cmd, cwd=code, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    def normalize(text):
        return re.sub(r'^set_option maxHeartbeats 0\n', '', text, flags=re.M)
    results = []
    for file in sorted(lean.rglob('*.lean')):
        rel = file.relative_to(lean)
        original = repo / 'lean' / rel
        a, b = original.read_bytes(), file.read_bytes()
        results.append({'path': rel.as_posix(), 'byte_identical': a == b,
                        'equal_ignoring_resource_option': normalize(a.decode()) == normalize(b.decode())})
    (dest / 'comparison.json').write_text(json.dumps(results, indent=2) + '\n')
    bad = [x['path'] for x in results if not x['equal_ignoring_resource_option']]
    if bad:
        raise SystemExit('Unexpected regeneration differences: ' + ', '.join(bad))
    changed = [x['path'] for x in results if not x['byte_identical']]
    print(f'All {len(results)} Lean files agree after resource-option normalization; '
          f'{len(changed)} files differ only by maxHeartbeats settings.')
    print('Candidate data regenerated. Validate with a clean Lean build in', lean)


if __name__ == '__main__':
    main()
