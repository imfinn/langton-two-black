#!/usr/bin/env python3
"""Mutation test for indep_cover.py: damaging the child list must make the coverage test report gaps.

Usage: python3 mutation_test.py childdump.txt [n_single_drops]

For the first concrete parent and the first family parent in the dump it runs:
  * baseline (no mutation)                          -> expect 0 gaps
  * drop every one-parameter child (the tail rays)  -> expect many gaps
  * drop one child, for n random children           -> expect >= 1 gap each
  * move one child's new block by one cell          -> expect >= 1 gap each
"""
import sys, random
sys.path.insert(0, '.')
import indep_cover as ic
from indep_family import certify


def coverage(parent, children, offsets, extra=80):
    v, blk, nb = parent; d = len(v)
    idx = ic.ChildIndex(children, len(blk) + 1)
    cells = gaps = 0
    for off in (offsets if d else [0]):
        npr = [x + off for x in nb]
        pc = ic.cells_of(v, blk, npr)
        c = certify(set(pc)); assert c.ok
        fr = ic.first_reads(pc, c.T + 104 * extra)
        tdiv = max([fr[p] for p in pc if p in fr], default=-1); pcs = set(pc)
        for z, t in fr.items():
            if t <= tdiv or z in pcs: continue
            cells += 1
            if not idx.matches(pc + [z]): gaps += 1
    return cells, gaps


def main():
    parents = ic.parse(sys.argv[1]); nsingle = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    rng = random.Random(2026)
    picks = [next(p for p in parents if len(p['P'][0]) == 0), next(p for p in parents if len(p['P'][0]) == 1)]
    offsets = [0, 7]
    bad = 0
    for par in picks:
        P, C = par['P'], par['C']
        kind = 'family' if P[0] else 'concrete'
        cells, g = coverage(P, C, offsets)
        print(f'[{kind}] baseline: {cells} new cells, {g} gaps (expect 0)'); bad += g != 0
        C2 = [c for c in C if len(c[0]) != len(P[0]) + 1 or c[1][-1][2] >> len(P[0]) & 1 == 0]
        cells, g = coverage(P, C2, offsets)
        print(f'[{kind}] drop all {len(C) - len(C2)} new-corridor children: {g} gaps (expect > 0)'); bad += g == 0
        for k in rng.sample(range(len(C)), nsingle):
            cells, g = coverage(P, C[:k] + C[k + 1:], offsets)
            print(f'[{kind}] drop child {k}: {g} gaps (expect > 0)'); bad += g == 0
        for k in rng.sample(range(len(C)), nsingle):
            v, blk, n0 = C[k]; b = blk[-1]
            Cm = C[:k] + [(v, blk[:-1] + [(b[0] + 1, b[1], b[2])], n0)] + C[k + 1:]
            cells, g = coverage(P, Cm, offsets)
            print(f'[{kind}] move child {k} by (1,0): {g} gaps (expect > 0)'); bad += g == 0
    print(f'MUTATION TEST: {"PASS" if bad == 0 else "FAIL"} ({bad} unexpected outcomes)')


if __name__ == '__main__':
    main()
