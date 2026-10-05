#!/usr/bin/env python3
"""Turn `calc_cov leandump` output into Lean data chunks for the concrete-parent checks.

Usage: python3 gen_lean_parents.py leandump.txt <lean_dir> <nchunks> [limit]
Writes TwoBlack/Parents/Chunk<k>.lean (data + native_decide theorem) and TwoBlack/Parents/Table.lean.
"""
import sys, os, re

DIAG = {(2, 2): 'pp', (2, -2): 'pm', (-2, 2): 'mp', (-2, -2): 'mm'}


def parse(path, limit=None):
    out = []
    for line in open(path):
        if not line.startswith('F '): continue
        head, cert, fams = line.split('|', 2)
        _, fx, fy, tau = head.split()
        s, ux, uy, A, t1, psi, tdiv, periods = map(int, cert.split())
        fl = []
        for item in fams.split(';'):
            item = item.strip()
            if not item: continue
            m = re.match(r'(-?\d+) (-?\d+) (-?\d+) (-?\d+) (\d+) \d+ (-?\d+) (-?\d+) \[([\d,]*)\] (\d+) (-?\d+) (-?\d+) (-?\d+)', item)
            z0x, z0y, vx, vy, n, D, C = (int(m[i]) for i in range(1, 8))
            ms = [int(x) for x in m[8].split(',') if x]
            s3, ux3, uy3, A3 = int(m[9]), int(m[10]), int(m[11]), int(m[12])
            fl.append((DIAG[(vx, vy)], (z0x, z0y), n, D, C, ms, s3, (ux3, uy3), A3))
        out.append(((int(fx), int(fy)), int(tau), (s, DIAG[(ux, uy)], A, t1, psi, tdiv, periods), fl))
        if limit and len(out) >= limit: break
    return out


def pt(p):
    return f'⟨{p[0]}, {p[1]}⟩'


def entry(e):
    F, tau, (s, du, A, t1, psi, tdiv, periods), fl = e
    fams = ', '.join(f'(⟨.{dg}, [{pt(F)}], [{pt(z0)}]⟩, ⟨{n}, {D}, {C}, {ms}, {s3}, {pt(u3)}, {A3}⟩)'
                     for (dg, z0, n, D, C, ms, s3, u3, A3) in fl)
    return f'  ⟨{pt(F)}, {tau}, ⟨{s}, .{du}, {A}, {t1}, {psi}, {tdiv}, {periods}⟩, [{fams}]⟩'


def main():
    src, ldir, nch = sys.argv[1], sys.argv[2], int(sys.argv[3])
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else None
    es = parse(src, limit)
    os.makedirs(os.path.join(ldir, 'TwoBlack', 'Parents'), exist_ok=True)
    size = (len(es) + nch - 1) // nch
    names = []
    for k in range(nch):
        part = es[k * size:(k + 1) * size]
        if not part: break
        name = f'chunk{k}'
        names.append(name)
        with open(os.path.join(ldir, 'TwoBlack', 'Parents', f'Chunk{k}.lean'), 'w') as f:
            f.write('import TwoBlack.ParentTable\n\nnamespace TwoBlack\n\n')
            f.write('set_option maxRecDepth 1000000\n\n')
            f.write(f'def {name} : List PEntry := [\n' + ',\n'.join(entry(e) for e in part) + '\n]\n\n')
            f.write(f'theorem {name}_ok : {name}.all PEntry.ok = true := by native_decide\n\nend TwoBlack\n')
    with open(os.path.join(ldir, 'TwoBlack', 'Parents', 'All.lean'), 'w') as f:
        for k in range(len(names)):
            f.write(f'import TwoBlack.Parents.Chunk{k}\n')
        f.write('\nnamespace TwoBlack\n\n')
        f.write('def parentTable : List PEntry := ' + ' ++ '.join(names) + '\n\n')
        f.write('theorem parentTable_ok : parentTable.all PEntry.ok = true := by\n')
        f.write('  simp only [parentTable, List.all_append, ' + ', '.join(f'{n}_ok' for n in names) + ', Bool.and_self, Bool.true_and, Bool.and_true]\n\n')
        f.write('end TwoBlack\n')
    print(f'{len(es)} parents in {len(names)} chunks of up to {size}')


if __name__ == '__main__':
    main()
