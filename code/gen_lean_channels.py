#!/usr/bin/env python3
"""Turn `calc_cov chandump` output into Lean data for the 22 channel parents' children.

Usage: python3 gen_lean_channels.py chandump.txt <lean_dir>
Writes TwoBlack/Chan/Data<k>.lean (one per channel parent, with a native_decide check of its one-parameter
children) and TwoBlack/Chan/All.lean (the table and its combined check).
"""
import sys, os, re

DIAG = {(2, 2): 'pp', (2, -2): 'pm', (-2, 2): 'mp', (-2, -2): 'mm'}


def pt(p):
    return f'⟨{p[0]}, {p[1]}⟩'


def parse(path):
    parents = []; cur = None
    for line in open(path):
        line = line.strip()
        if line.startswith('P '):
            _, x, y, nb = line.split()
            cur = {'z0': (int(x), int(y)), 'base': int(nb), 'k1': [], 'k2': []}
        elif line == 'E':
            parents.append(cur); cur = None
        elif line.startswith('C '):
            parts = line[2:].split('|')
            a = list(map(int, parts[0].split())); k = 0
            d = a[k]; k += 1
            vs = [(a[k + 2 * i], a[k + 2 * i + 1]) for i in range(d)]; k += 2 * d
            nb = a[k]; k += 1
            blks = [(a[k + 3 * q], a[k + 3 * q + 1], a[k + 3 * q + 2]) for q in range(nb)]
            n0 = list(map(int, parts[1].split()))
            if d == 1:
                h = parts[2].strip()
                assert h != 'FAIL', line
                m = re.match(r'(\d+) (-?\d+) (-?\d+) \[([\d,]*)\] (\d+) (-?\d+) (-?\d+) (-?\d+)', h)
                n, D, C = int(m[1]), int(m[2]), int(m[3])
                ms = [int(x) for x in m[4].split(',') if x]
                s, ux, uy, A = int(m[5]), int(m[6]), int(m[7]), int(m[8])
                near = [(b[0], b[1]) for b in blks if b[2] == 0]
                far = [(b[0], b[1]) for b in blks if b[2] == 1]
                assert all(b[2] in (0, 1) for b in blks)
                cur['k1'].append((DIAG[vs[0]], near, far, n0[0], (n, D, C, ms, s, (ux, uy), A)))
            else:
                bl = [((b[0], b[1]), [i for i in range(d) if b[2] >> i & 1]) for b in blks]
                cur['k2'].append(([DIAG[v] for v in vs], bl, n0))
    return parents


def kid1(k):
    dg, near, far, base, (n, D, C, ms, s, u, A) = k
    return (f'⟨⟨.{dg}, [{", ".join(pt(b) for b in near)}], [{", ".join(pt(b) for b in far)}]⟩, {base}, '
            f'⟨{n}, {D}, {C}, {ms}, {s}, {pt(u)}, {A}⟩⟩')


def kid2(k):
    vs, bl, n0 = k
    blocks = ', '.join(f'({pt(b)}, {idx})' for b, idx in bl)
    return f'(⟨[{", ".join("." + v for v in vs)}], [{blocks}]⟩, {n0})'


def main():
    src, ldir = sys.argv[1], sys.argv[2]
    ps = parse(src)
    d = os.path.join(ldir, 'TwoBlack', 'Chan'); os.makedirs(d, exist_ok=True)
    for i, p in enumerate(ps):
        with open(os.path.join(d, f'Data{i}.lean'), 'w') as f:
            f.write('import TwoBlack.Channels\n\nnamespace TwoBlack\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n')
            f.write(f'def chan{i} : ChanEntry := ⟨{pt(p["z0"])}, [\n  ' + ',\n  '.join(kid1(k) for k in p['k1']) + '],\n  [')
            f.write(',\n  '.join(kid2(k) for k in p['k2']) + ']⟩\n\n')
            f.write(f'theorem chan{i}_ok : chan{i}.kids1.all Kid1.ok = true := by native_decide\n\nend TwoBlack\n')
    with open(os.path.join(d, 'All.lean'), 'w') as f:
        for i in range(len(ps)):
            f.write(f'import TwoBlack.Chan.Data{i}\n')
        f.write('\nnamespace TwoBlack\n\n')
        f.write('def chanTable : List ChanEntry := [' + ', '.join(f'chan{i}' for i in range(len(ps))) + ']\n\n')
        f.write('theorem chanTable_ok : chanTable.all (fun e => e.kids1.all Kid1.ok) = true := by\n')
        f.write('  simp only [chanTable, List.all_cons, List.all_nil, ' + ', '.join(f'chan{i}_ok' for i in range(len(ps))) + ', Bool.and_true, Bool.true_and]\n\n')
        f.write('end TwoBlack\n')
    print(f'{len(ps)} channel parents; one-parameter children {sum(len(p["k1"]) for p in ps)}; '
          f'two-parameter children {sum(len(p["k2"]) for p in ps)}')


if __name__ == '__main__':
    main()
