#!/usr/bin/env python3
"""Lean data for the perpendicular two-parameter channel children (from chandump.txt and perpdump.txt).

Usage: python3 gen_lean_perp.py chandump.txt perpdump.txt <lean_dir>
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_lean_channels import parse as parse_chan, kid2, pt


def trp(s):
    m = re.match(r'\s*(-?\d+) (-?\d+) \[([\d,]*)\]', s)
    return int(m[1]), int(m[2]), [int(x) for x in m[3].split(',') if x]


def main():
    chan, perp, ldir = sys.argv[1], sys.argv[2], sys.argv[3]
    ps = parse_chan(chan)
    entries = []; cur = None
    for line in open(perp):
        line = line.strip()
        if line.startswith('K '):
            parts = line.split('|')
            _, pi, kj = parts[0].split()
            a0, b0 = map(int, parts[1].split())
            D1, C1, ms1 = trp(parts[2]); D2, C2, ms2 = trp(parts[3])
            s, ux, uy, A = map(int, parts[4].split())
            cur = {'kid': ps[int(pi)]['k2'][int(kj)], 'H': (a0, b0, D1, C1, ms1, D2, C2, ms2, s, (ux, uy), A), 'slabs': []}
            entries.append(cur)
        elif line.startswith('S '):
            parts = line.split('|')
            i, val, vx, vy = map(int, parts[0].split()[1:])
            assert i == 0, 'only slabs in parameter 1 are supported'
            base, nbG = map(int, parts[1].split())
            D, C, ms = trp(parts[3])
            s, ux, uy, A = map(int, parts[4].split())
            cur['slabs'].append((val, (nbG, D, C, ms, s, (ux, uy), A)))
    out = []
    for e in entries:
        a0, b0, D1, C1, ms1, D2, C2, ms2, s, u, A = e['H']
        n1 = e['kid'][2][0]
        sl = sorted(e['slabs'])
        assert [v for v, _ in sl] == list(range(n1, a0)), (n1, a0, [v for v, _ in sl])
        slabs = ', '.join(f'⟨{n}, {D}, {C}, {ms}, {s_}, {pt(u_)}, {A_}⟩' for _, (n, D, C, ms, s_, u_, A_) in sl)
        out.append(f'  ({kid2(e["kid"])}, ⟨{a0}, {b0}, {D1}, {C1}, {ms1}, {D2}, {C2}, {ms2}, {s}, {pt(u)}, {A}⟩, [{slabs}])')
    with open(os.path.join(ldir, 'TwoBlack', 'PerpData.lean'), 'w') as f:
        f.write('import TwoBlack.PerpKids\nimport TwoBlack.Chan.All\n\nnamespace TwoBlack\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n')
        f.write('def perpTable : List ((FamD × List Nat) × Hint2 × List Hint1) := [\n' + ',\n'.join(out) + '\n]\n\n')
        f.write('theorem perp_covered : perpCovered chanTable perpTable = true := by native_decide\n\nend TwoBlack\n')
    print(f'{len(entries)} perpendicular children, {sum(len(e["slabs"]) for e in entries)} slabs')


if __name__ == '__main__':
    main()
