#!/usr/bin/env python3
"""Lean data for the parallel two-parameter channel children (from chandump.txt and pardump.txt).

Usage: python3 gen_lean_par.py chandump.txt pardump.txt <lean_dir> [exclude_indices]
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_lean_channels import parse as parse_chan, kid2, pt
from gen_lean_perp import trp


def main():
    chan, par, ldir = sys.argv[1], sys.argv[2], sys.argv[3]
    excl = set(int(x) for x in sys.argv[4].split(',')) if len(sys.argv) > 4 and sys.argv[4] else set()
    ps = parse_chan(chan)
    entries = []; cur = None
    for line in open(par):
        line = line.strip()
        if line.startswith('K '):
            parts = line.split('|')
            _, pi, kj = parts[0].split()
            a0, b0 = map(int, parts[1].split())
            D1, C1, ms1 = trp(parts[2]); D2, C2, ms2 = trp(parts[3])
            s, ux, uy, A = map(int, parts[4].split())
            kid = ps[int(pi)]['k2'][int(kj)]
            vs = kid[0]
            same = vs[0] == vs[1]
            if same:
                far = D2 + 9 >= C1; near = C2 - 9 <= D1
            else:
                far = -C2 + 9 >= C1; near = -D2 - 9 <= D1
            cur = {'kid': kid, 'far': far, 'side_ok': far or near,
                   'H': (a0, b0, D1, C1, ms1, D2, C2, ms2, s, (ux, uy), A), 's1': [], 's2': []}
            entries.append(cur)
        elif line.startswith('S '):
            parts = line.split('|')
            i, val, vx, vy = map(int, parts[0].split()[1:])
            base, nbG = map(int, parts[1].split())
            D, C, ms = trp(parts[3])
            s, ux, uy, A = map(int, parts[4].split())
            (cur['s1'] if i == 0 else cur['s2']).append((val, (nbG, D, C, ms, s, (ux, uy), A)))
    out = []; skipped = []
    for idx, e in enumerate(entries):
        if idx in excl or not e['side_ok']:
            skipped.append(idx); continue
        a0, b0, D1, C1, ms1, D2, C2, ms2, s, u, A = e['H']
        n1, n2 = e['kid'][2]
        s1 = sorted(e['s1']); s2 = sorted(e['s2'])
        assert [v for v, _ in s1] == list(range(n1, a0)) and [v for v, _ in s2] == list(range(n2, b0))
        f = lambda sl: ', '.join(f'⟨{n}, {D}, {C}, {ms}, {s_}, {pt(u_)}, {A_}⟩' for _, (n, D, C, ms, s_, u_, A_) in sl)
        out.append(f'  ({kid2(e["kid"])}, {"true" if e["far"] else "false"}, '
                   f'⟨{a0}, {b0}, {D1}, {C1}, {ms1}, {D2}, {C2}, {ms2}, {s}, {pt(u)}, {A}⟩, [{f(s1)}], [{f(s2)}])')
    with open(os.path.join(ldir, 'TwoBlack', 'ParData.lean'), 'w') as fh:
        fh.write('import TwoBlack.Check2Par\nimport TwoBlack.Chan.All\n\nnamespace TwoBlack\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n')
        fh.write('def parTable : List ((FamD × List Nat) × Bool × Hint2 × List Hint1 × List Hint1) := [\n' + ',\n'.join(out) + '\n]\n\n')
        fh.write('theorem par_covered : parCovered chanTable parTable = true := by native_decide\n\nend TwoBlack\n')
    print(f'{len(out)} parallel children written; skipped {skipped}; slabs {sum(len(e["s1"]) + len(e["s2"]) for e in entries)}')


if __name__ == '__main__':
    main()
