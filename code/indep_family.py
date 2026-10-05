#!/usr/bin/env python3
"""Independent re-implementation (Python) of the corridor-family checks of the two-cell paper.

Written from the paper's definitions, not translated from calculus.cpp. Reads families
(one per line) with the C++ verdict and data, re-derives everything, and compares.

Line format (written by calculus.cpp with FAMDUMP):
  d  vx vy ...  nb  bx by mask ...  n_0..n_{d-1}  | T  ntrans_0..  D_0 C_0 ..  m_0,1 .. (switch times)
"""
import sys

DX = (0, 1, 0, -1); DY = (1, 0, -1, 0)          # headings N E S W


def run(cells, Tmax, stop=None):
    """Simulate from the origin heading north. Returns positions/headings/reads lists and the board."""
    black = set(cells); x = y = 0; h = 0
    X = []; Y = []; H = []; Rd = []; first_touch = {}
    for c in cells: first_touch[c] = 0
    for t in range(Tmax):
        X.append(x); Y.append(y); H.append(h)
        p = (x, y)
        if p not in first_touch: first_touch[p] = t
        b = 1 if p in black else 0
        Rd.append(b)
        if b: black.discard(p)
        else: black.add(p)
        h = (h + (3 if b else 1)) % 4
        x += DX[h]; y += DY[h]
        if stop and stop(t + 1, X, Y, H, Rd, black, first_touch, x, y, h):
            return X, Y, H, Rd, black, first_touch, (x, y, h), t + 1
    return X, Y, H, Rd, black, first_touch, (x, y, h), Tmax


def canon(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


class Cert:
    pass


def certify(cells, cap=40_000_000):
    """First time T (multiple of 104, T >= 520) at which an exact Lemma-1 certificate holds:
    positions/reads 104-periodic on [T-416, T], equal headings at s=T-104 and T, displacement u != 0,
    every cell touched before T-416 lies outside G = {u.z > A} with A = min_{[s,T]} u.p - 1, and the
    complete black sets satisfy B_T cap {u.z > A + u.u} = (B_s cap G) + u.  B_s is reconstructed by
    undoing the reads of [s, T)."""
    res = Cert(); res.ok = False

    def stop(T, X, Y, H, Rd, black, ft, x, y, h):
        if T % 104 or T < 520: return False
        PX = lambda w: x if w == T else X[w]
        PY = lambda w: y if w == T else Y[w]
        ux = PX(T) - PX(T - 104); uy = PY(T) - PY(T - 104)
        if ux == 0 and uy == 0: return False
        for w in range(T - 416, T - 104):
            if PX(w + 104) - PX(w) != ux or PY(w + 104) - PY(w) != uy or Rd[w + 104] != Rd[w]: return False
        s = T - 104
        if H[s] != h: return False
        A = min(ux * PX(w) + uy * PY(w) for w in range(s, T + 1)) - 1
        for c, t0 in ft.items():
            if t0 < T - 416 and ux * c[0] + uy * c[1] > A: return False
        flips = {}
        for w in range(s, T): flips[(X[w], Y[w])] = flips.get((X[w], Y[w]), 0) ^ 1
        Bs = set(black) ^ {c for c, f in flips.items() if f}
        uu = ux * ux + uy * uy
        S1 = {c for c in black if ux * c[0] + uy * c[1] > A + uu}
        S2 = {(c[0] + ux, c[1] + uy) for c in Bs if ux * c[0] + uy * c[1] > A}
        if S1 != S2: return False
        res.ok = True; res.T = T; res.s = s; res.ux = ux; res.uy = uy; res.A = A
        res.word = ''.join(str(Rd[w]) for w in range(s, T)); res.final = (x, y)
        return True

    X, Y, H, Rd, black, ft, fin, T = run(cells, cap, stop)
    res.X, res.Y, res.H = X, Y, H
    return res


def snapshots(cells, times):
    want = sorted(set(times)); out = {}
    black = set(cells); x = y = 0; h = 0; k = 0; t = 0
    while k < len(want):
        while k < len(want) and want[k] == t:
            out[t] = set(black); k += 1
        if k >= len(want): break
        p = (x, y); b = 1 if p in black else 0
        if b: black.discard(p)
        else: black.add(p)
        h = (h + (3 if b else 1)) % 4; x += DX[h]; y += DY[h]; t += 1
    return out


def phi_of(v):
    sx = 1 if v[0] > 0 else -1; sy = 1 if v[1] > 0 else -1
    return lambda x, y: sx * x + sy * y


def check_family(v, blocks, n, CW):
    """Return (ok, why, data) for the family at member n, following the paper's conditions."""
    d = len(v)
    cells = set()
    for (bx, by, m) in blocks:
        x, y = bx, by
        for i in range(d):
            if m >> i & 1: x += n[i] * v[i][0]; y += n[i] * v[i][1]
        cells.add((x, y))
    c = certify(cells)
    if not c.ok: return False, 'nocert', None
    if canon(c.word) != CW: return False, 'nonstandard', None
    T = c.T; X = c.X[:T]; Y = c.Y[:T]; H = c.H[:T]
    P = lambda w: (X[w], Y[w]) if w < T else c.final
    data = {'T': T, 'P': []}
    snapt = []
    for i in range(d):
        phi = phi_of(v[i]); vx, vy = v[i]
        D0 = phi(0, 0); C0 = None
        for (bx, by, m) in blocks:
            x, y = bx, by
            for j in range(d):
                if m >> j & 1: x += n[j] * v[j][0]; y += n[j] * v[j][1]
            if m >> i & 1: C0 = phi(x, y) if C0 is None else min(C0, phi(x, y))
            else: D0 = max(D0, phi(x, y))
        if C0 is None or C0 - D0 < 60: return False, 'short', None
        mu = (D0 + C0) // 2 if (D0 + C0) >= 0 else -((-(D0 + C0)) // 2)   # C++ integer division truncates
        f = [0] * T
        for w in range(T - 104):
            if H[w + 104] != H[w]: continue
            dx = X[w + 104] - X[w]; dy = Y[w + 104] - Y[w]
            if (dx, dy) == (vx, vy): f[w] = 1
            elif (dx, dy) == (-vx, -vy): f[w] = -1
        runs = []; w = 0
        while w + 104 < T:
            if not f[w]: w += 1; continue
            b = w; sg = f[w]
            while w + 104 < T and f[w] == sg: w += 1
            if w - b >= 520: runs.append([b, w - 1, sg])
        cnt = [0] * len(runs)
        for w in range(T):
            a = phi(*P(w)) < mu; bb = phi(*P(w + 1)) < mu
            if a == bb: continue
            which = None
            for r, (b, e, sg) in enumerate(runs):
                if b <= w < e + 104: which = r; break
            if which is None:
                sgf = 1 if (c.ux, c.uy) == (vx, vy) else (-1 if (c.ux, c.uy) == (-vx, -vy) else 0)
                if w >= c.s and sgf:
                    runs.append([c.s, T - 1, sgf]); cnt.append(0); which = len(runs) - 1
                else: return False, 'cross_outside_transit', None
            cnt[which] += 1
        trs = []
        for r in range(len(runs)):
            if cnt[r] == 0: continue
            if cnt[r] % 2 == 0: return False, 'even_crossings', None
            trs.append(runs[r])
        trs.sort(); side = -1
        for t in trs:
            if t[2] != -side: return False, 'transit_direction', None
            side = -side
        final_side = side
        TR = []
        for (b, e, sg) in trs:
            best = None; bd = None
            for w in range(max(b, 0), e + 1):
                if w + 104 >= T: break
                dd = abs(phi(*P(w)) - mu)
                if bd is None or dd < bd: bd = dd; best = w
            if best is None: return False, 'no_switch', None
            inr = lambda w: D0 - 16 <= phi(*P(w)) <= C0 + 16
            b2 = best
            while b2 - 1 >= b and inr(b2 - 1): b2 -= 1
            end = e + 104; e2 = best
            while e2 + 1 <= end and inr(e2 + 1): e2 += 1
            if e2 < best + 104: return False, 'short_transit', None
            TR.append((b2, e2, sg, best))          # span [b2, e2]
        def intr(w): return any(b <= w <= e for (b, e, sg, m) in TR)
        Dt = D0; Cb = C0; sd = -1; k = 0
        for w in range(T):
            while k < len(TR) and w > TR[k][1]: sd = -sd; k += 1
            if intr(w): continue
            p = phi(*P(w))
            if sd < 0: Dt = max(Dt, p)
            else: Cb = min(Cb, p)
        if not (Dt + 40 < Cb): return False, 'zones_overlap', None
        for (b, e, sg, m) in TR:
            pm = phi(*P(m))
            if not (Dt + 16 < pm < Cb - 16): return False, 'switch_outside_band', None
            if P(m + 104) != (P(m)[0] + sg * vx, P(m)[1] + sg * vy) or H[m + 104] != H[m]: return False, 'switch_pose', None
            snapt += [m, m + 104]
        M = [0] + [t[3] for t in TR]
        for j in range(len(M)):
            r = -1 if j % 2 == 0 else 1
            lo = M[j]; hi = M[j + 1] + 104 if j + 1 < len(M) else T
            for w in range(lo, min(hi, T)):
                p = phi(*P(w))
                if (r < 0 and not p < Cb - 16) or (r > 0 and not p > Dt + 16): return False, 'relation_region', None
        du = phi(c.ux, c.uy)
        rng = [phi(*P(w)) for w in range(c.s, T)]
        if final_side < 0 and (du > 0 or max(rng) >= Cb - 16): return False, 'final_highway_region', None
        if final_side > 0 and (du < 0 or min(rng) <= Dt + 16): return False, 'final_highway_region', None
        data['P'].append({'D': Dt, 'C': Cb, 'TR': TR, 'final': final_side, 'phi': phi, 'D0': D0, 'C0': C0})
    # S8 parallel bands disjoint
    for i in range(d):
        for j in range(i + 1, d):
            same = v[i] == v[j]; opp = (v[i][0] == -v[j][0] and v[i][1] == -v[j][1])
            if not (same or opp): continue
            a0, a1 = data['P'][i]['D'], data['P'][i]['C']
            b0, b1 = (data['P'][j]['D'], data['P'][j]['C']) if same else (-data['P'][j]['C'], -data['P'][j]['D'])
            if not (a1 <= b0 or b1 <= a0): return False, 'parallel_bands', None
    # H1': insertion windows of i avoid transit spans of j
    for i in range(d):
        for j in range(d):
            if i == j: continue
            for (_, _, _, m) in data['P'][i]['TR']:
                for (b, e, _, _) in data['P'][j]['TR']:
                    if not (m + 104 < b or e < m): return False, 'H1_window_in_transit', None
    # H3 parallel pairs
    for i in range(d):
        for j in range(d):
            if i == j: continue
            same = v[i] == v[j]; opp = (v[i][0] == -v[j][0] and v[i][1] == -v[j][1])
            if not (same or opp): continue
            Pi = data['P'][i]; Pj = data['P'][j]; phii = Pi['phi']; phij = Pj['phi']
            Delta = 4 if same else -4
            blo, bhi = (Pj['D'], Pj['C']) if same else (-Pj['C'], -Pj['D'])
            if blo >= Pi['C']: sigma = 1
            elif bhi <= Pi['D']: sigma = -1
            else: return False, 'H3_side', None
            rho = Delta if sigma < 0 else -Delta
            def sideI(t): return -1 if sum(1 for tr in Pi['TR'] if t > tr[3] + 104) % 2 == 0 else 1
            def inWinI(t): return any(tr[3] <= t <= tr[3] + 104 for tr in Pi['TR'])
            def inTrJ(t): return any(tr[0] <= t <= tr[1] for tr in Pj['TR'])
            for (b, e, _, _) in Pj['TR']:
                for t in range(b, min(e, T - 1) + 1):
                    if inWinI(t) or sideI(t) != sigma: return False, 'H3_jtransit_side', None
            F = []; nfFar = []; nfNear = []; nfFarBlk = []; nfNearBlk = []; fFarBlk = []; fNearBlk = []
            sdj = -1; kk = 0
            for t in range(T):
                while kk < len(Pj['TR']) and t > Pj['TR'][kk][1]: sdj = -sdj; kk += 1
                pj = phij(*P(t))
                if inWinI(t) or sideI(t) != sigma: F.append(pj); continue
                if inTrJ(t): continue
                (nfNear if sdj < 0 else nfFar).append(pj)
            duj = phij(c.ux, c.uy)
            if Pi['final'] != sigma and ((rho > 0 and duj < 0) or (rho < 0 and duj > 0)): return False, 'H3_foreign_future', None
            o = phij(0, 0)
            if sigma > 0: F.append(o); fNearBlk.append(o)
            else: nfNearBlk.append(o)
            for (bx, by, m) in blocks:
                x, y = bx, by
                for q in range(d):
                    if m >> q & 1: x += n[q] * v[q][0]; y += n[q] * v[q][1]
                bI = m >> i & 1; bJ = m >> j & 1; foreign = (not bI) if sigma > 0 else bool(bI); pj = phij(x, y)
                if foreign:
                    F.append(pj); (fFarBlk if bJ else fNearBlk).append(pj)
                else:
                    if bJ: nfFarBlk.append(pj); nfFar.append(pj)
                    else: nfNearBlk.append(pj); nfNear.append(pj)
            if F:
                if rho > 0:
                    if min(F) < Pj['C']: return False, 'H3_foreign_zone', None
                    if (min(nfFar) if nfFar else None) != Pj['C']: return False, 'H3_extremum', None
                    if fFarBlk and (not nfFarBlk or min(fFarBlk) < min(nfFarBlk)): return False, 'H3_mu_block', None
                else:
                    if max(F) > Pj['D']: return False, 'H3_foreign_zone', None
                    if max(nfNear + nfNearBlk) != Pj['D']: return False, 'H3_extremum', None
                    if fNearBlk and (not nfNearBlk or max(fNearBlk) > max(nfNearBlk)): return False, 'H3_mu_block', None
    # C3 board periodicity at every switch
    if snapt:
        snaps = snapshots(cells, snapt)
        for i in range(d):
            phi = data['P'][i]['phi']; vx, vy = v[i]; Dt = data['P'][i]['D']; Cb = data['P'][i]['C']
            for (b, e, sg, m) in data['P'][i]['TR']:
                A0 = snaps[m]; A1 = snaps[m + 104]
                inS = lambda p: Dt + 8 < p < Cb - 8
                for w in A1:
                    if inS(phi(*w)) and (w[0] - sg * vx, w[1] - sg * vy) not in A0: return False, 'Bcheck', None
                for w0 in A0:
                    w = (w0[0] + sg * vx, w0[1] + sg * vy)
                    if inS(phi(*w)) and w not in A1: return False, 'Bcheck', None
    return True, '', data


def main():
    blank = certify(set()); CW = canon(blank.word)
    path = sys.argv[1]; agree = disagree = 0; datamismatch = 0; total = 0
    for line in open(path):
        line = line.strip()
        if not line: continue
        left, right = line.split('|')
        a = list(map(int, left.split())); k = 0
        d = a[k]; k += 1
        v = [(a[k + 2 * i], a[k + 2 * i + 1]) for i in range(d)]; k += 2 * d
        nb = a[k]; k += 1
        blocks = [(a[k + 3 * q], a[k + 3 * q + 1], a[k + 3 * q + 2]) for q in range(nb)]; k += 3 * nb
        n = a[k:k + d]
        cpp = list(map(int, right.split()))
        cT = cpp[0]; cnt = cpp[1:1 + d]; zones = cpp[1 + d:1 + 3 * d]; sw = cpp[1 + 3 * d:]
        ok, why, data = check_family(v, blocks, n, CW)
        total += 1
        if not ok:
            disagree += 1; print('DISAGREE (python rejects):', why, line); continue
        agree += 1
        mine = [data['T']] + [len(p['TR']) for p in data['P']] + sum([[p['D'], p['C']] for p in data['P']], []) + sum([[t[3] for t in p['TR']] for p in data['P']], [])
        if mine != cpp:
            datamismatch += 1; print('DATA MISMATCH', mine, 'vs', cpp, line)
    print(f'independent family checker: {total} families, python accepts {agree}, rejects {disagree}, data mismatches {datamismatch}')


if __name__ == '__main__':
    main()
