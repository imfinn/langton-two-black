#!/usr/bin/env python3
"""Rerun optional cross-checks and reject failure summaries even when the original exit code is zero."""
import argparse
import gzip
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def main():
    repo = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=repo / 'audit/local-crosscheck')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    code = repo / 'code'
    for name in ('calc', 'indep'):
        if not (code / name).is_file():
            parser.error(f'compile code/{name} first; see REPRODUCIBILITY.md')
    with gzip.open(repo / 'runs/childdump.txt.gz', 'rb') as f:
        childdump = out / 'childdump.txt'
        childdump.write_bytes(f.read())
    env = os.environ.copy()
    env['XVAL'] = '1'
    jobs = [
        ('level1', [str(code / 'calc'), 'level1'],
         r'LEVEL1 families ok=22 fail=0 direct ok=2433 fail=0 slabs=0 xval=44 bad=0', env),
        ('independent-detector', [str(code / 'indep'), 'file', str(repo / 'runs/v2dump.txt')],
         r'independent detector: 3004 configs, \d+ simulated updates, 0 mismatches', None),
    ]
    for name, count in [('famdump_all', 311), ('famdump_conc', 269), ('famdump2', 506)]:
        jobs.append((name, [sys.executable, 'indep_family.py', str(repo / 'runs' / (name + '.txt'))],
                     rf'independent family checker: {count} families, python accepts {count}, rejects 0, data mismatches 0', None))
    jobs += [
        ('coverage', [sys.executable, 'indep_cover.py', str(childdump), '80'],
         r'INDEPENDENT COVERTEST: parents 174, members 350, new cells checked 962875, uncovered 0, multiply covered 0', None),
        ('mutations', [sys.executable, 'mutation_test.py', str(childdump), '20'],
         r'MUTATION TEST: PASS \(0 unexpected outcomes\)', None),
    ]
    results = []
    for name, cmd, pattern, job_env in jobs:
        print('Running', name, flush=True)
        t = time.monotonic()
        log = out / (name + '.log')
        with log.open('w') as f:
            p = subprocess.run(cmd, cwd=code, env=job_env, stdout=f, stderr=subprocess.STDOUT)
        text = log.read_text()
        ok = p.returncode == 0 and re.search(pattern, text) is not None
        if name == 'coverage' and 'PARENT MEMBER DOES NOT CERTIFY' in text:
            ok = False
        results.append({'name': name, 'command': cmd, 'exit_code': p.returncode,
                        'passed_summary_check': ok, 'elapsed_seconds': round(time.monotonic() - t, 3), 'log': str(log)})
        (out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if not ok:
            raise SystemExit('Cross-check failed or summary changed: inspect ' + str(log))
    print('All optional finite cross-checks passed. They are not premises of theoremA.')


if __name__ == '__main__':
    main()
