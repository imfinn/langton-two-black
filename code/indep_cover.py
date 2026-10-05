#!/usr/bin/env python3
"""Independent coverage test for Lemma 6.2 (Python, numpy).

Reads parents and children written by `calc_cov childdump`.  For each parent family P (proved base n_b) and several
members n' >= n_b, it simulates the member with its own simulator, finds every *new cell* z (first read after the
last first read of a parent block, not a block, up to a horizon well past the certificate), and checks that the
two-cell configuration P(n') + {z} is, as a SET of cells, equal to some child member C(m) with m >= n0(C).

Nothing here uses the C++ classification (site / footprint / split / tail): membership is decided by solving the
child's affine block equations in exact integer arithmetic, over every bijection between child blocks and\nconfiguration cells.
The certificate time is computed with the independent Python certifier of indep_family.py.
"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, '.')
from indep_family import certify

DX = (0, 1, 0, -1); DY = (1, 0, -1, 0)


def parse(path):
    parents = []; cur = None
    for line in open(path):
        if line.strip() == 'E':
            parents.append(cur); cur = None; continue
        if not (line.startswith('P ') or line.startswith('C ')): continue
        left, right = line[2:].split('|')
        a = list(map(int, left.split())); k = 0
        d = a[k]; k += 1
        v = [(a[k + 2 * i], a[k + 2 * i + 1]) for i in range(d)]; k += 2 * d
        nb = a[k]; k += 1
        blk = [(a[k + 3 * q], a[k + 3 * q + 1], a[k + 3 * q + 2]) for q in range(nb)]
        n = list(map(int, right.split()))
        fam = (v, blk, n)
        if line[0] == 'P': cur = {'P': fam, 'C': []}
        else: cur['C'].append(fam)
    return parents


def cells_of(v, blk, n):
    out = []
    for (bx, by, m) in blk:
        x, y = bx, by
        for i in range(len(v)):
            if m >> i & 1: x += n[i] * v[i][0]; y += n[i] * v[i][1]
        out.append((x, y))
    return out


def first_reads(cells, steps):
    black = set(cells); x = y = 0; h = 0; fr = {}
    for t in range(steps):
        p = (x, y)
        if p not in fr: fr[p] = t
        if p in black: black.discard(p); h = (h + 3) & 3
        else: black.add(p); h = (h + 1) & 3
        x += DX[h]; y += DY[h]
    return fr


class ChildIndex:
    """Exact membership test 'Q == C(m) for some integer m >= n0' for all children with the same block count.

    All arithmetic is in exact integers (numpy int64 with values far below 2**31).  For a child with d <= 2
    parameters and a bijection between its blocks and the cells of Q, the block equations read A m = r with A an
    integer (2B x d) matrix.  We pick d rows of A with nonzero determinant det and integer adjugate adj; any solution
    must satisfy det * m = adj * r_S, so we test divisibility, recover m by exact division, and then verify the
    whole system A m = r exactly.  This decides solvability exactly; the solution is unique since rank A = d."""

    def __init__(self, children, nblocks):
        self.concrete = {}
        self.groups = {}
        for ci, (v, blk, n0) in enumerate(children):
            if len(blk) != nblocks: continue
            d = len(v)
            if d == 0:
                self.concrete.setdefault(frozenset((b[0], b[1]) for b in blk), []).append(ci); continue
            if d > 2: raise SystemExit(f'child {ci}: only d <= 2 is implemented')
            for perm in itertools.permutations(range(nblocks)):
                A = [[0] * d for _ in range(2 * nblocks)]; b0 = [0] * (2 * nblocks)
                for k, (bx, by, m) in enumerate(blk):
                    row = perm[k]               # child block k  ->  configuration cell number row
                    b0[2 * row] = bx; b0[2 * row + 1] = by
                    for i in range(d):
                        if m >> i & 1: A[2 * row][i] = v[i][0]; A[2 * row + 1][i] = v[i][1]
                sel = None
                if d == 1:
                    for j in range(2 * nblocks):
                        if A[j][0] != 0: sel = ([j], A[j][0], [[1]]); break
                else:
                    for j1 in range(2 * nblocks):
                        for j2 in range(j1 + 1, 2 * nblocks):
                            a, b, c, e = A[j1][0], A[j1][1], A[j2][0], A[j2][1]
                            det = a * e - b * c
                            if det != 0 and sel is None: sel = ([j1, j2], det, [[e, -b], [-c, a]])
                if sel is None:
                    raise SystemExit(f'child {ci} has a parameter that moves no block (rank deficient)')
                rows, det, adj = sel
                g = self.groups.setdefault(d, {'A': [], 'rows': [], 'det': [], 'adj': [], 'b0': [], 'n0': [], 'id': []})
                g['A'].append(A); g['rows'].append(rows); g['det'].append(det); g['adj'].append(adj)
                g['b0'].append(b0); g['n0'].append(n0); g['id'].append(ci)
        for d, g in self.groups.items():
            for key in ('A', 'rows', 'det', 'adj', 'b0', 'n0'): g[key] = np.array(g[key], dtype=np.int64)
            g['id'] = np.array(g['id'])

    def matches(self, Q):
        """Q: list of cells (ordered).  Returns the set of child ids with a member equal to set(Q)."""
        hit = set(self.concrete.get(frozenset(Q), []))
        q = np.array([c for cell in Q for c in cell], dtype=np.int64)
        for d, g in self.groups.items():
            r = q[None, :] - g['b0']                                   # (N, 2B) exact integers
            rS = np.take_along_axis(r, g['rows'], axis=1)              # (N, d)
            num = np.einsum('nij,nj->ni', g['adj'], rS)                # det * m
            det = g['det'][:, None]
            ok = np.all(num % det == 0, axis=1)
            m = num // det                                             # exact where ok
            ok &= np.all(np.einsum('nij,nj->ni', g['A'], m) == r, axis=1)
            ok &= np.all(m >= g['n0'], axis=1)
            hit.update(g['id'][ok].tolist())
        return hit


def main():
    path = sys.argv[1]; reps_offsets = [0, 1, 2, 3, 5, 9, 17, 33, 61]
    extra = int(sys.argv[2]) if len(sys.argv) > 2 else 80      # horizon: certificate time + 104*extra
    shard, nshard = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
    parents = parse(path)
    members = cells_tot = gaps = multi = 0
    for pi, par in enumerate(parents):
        if pi % nshard != shard: continue
        v, blk, nb = par['P']; d = len(v)
        idx = ChildIndex(par['C'], len(blk) + 1)
        offs = reps_offsets if d else [0]
        for off in offs:
            npr = [x + off for x in nb]
            pc = cells_of(v, blk, npr)
            c = certify(set(pc))
            if not c.ok: print('PARENT MEMBER DOES NOT CERTIFY', pi, npr); continue
            horizon = c.T + 104 * extra
            fr = first_reads(pc, horizon)
            tdiv = max([fr[p] for p in pc if p in fr], default=-1)
            pcs = set(pc); members += 1
            for z, t in fr.items():
                if t <= tdiv or z in pcs: continue
                cells_tot += 1
                h = idx.matches(pc + [z])
                if not h:
                    gaps += 1
                    if gaps <= 10: print('GAP parent', pi, 'member', npr, 'cell', z, 'first read', t)
                elif len(h) > 1:
                    multi += 1
        print(f'parent {pi} done: members {members} cells {cells_tot} gaps {gaps} multi {multi}', flush=True)
    print(f'INDEPENDENT COVERTEST: parents {sum(1 for i in range(len(parents)) if i % nshard == shard)}, members {members}, '
          f'new cells checked {cells_tot}, uncovered {gaps}, multiply covered {multi}')


if __name__ == '__main__':
    main()
