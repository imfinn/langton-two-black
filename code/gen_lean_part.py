#!/usr/bin/env python3
"""Generate TwoBlack/PartData.lean: hints for the partition check (Lemma 6.3) of the 22 channel parents.

Usage: python3 gen_lean_part.py chandump.txt <lean_dir>

For each channel parent (one far block z0 on drift (-2,-2), member 40) this script
  * takes the corridor hint from TwoBlack/Level1Data.lean; for the two-switch parent it replaces D by
    Dtop + 4*LS - 13 (= 52), so that the near/far threshold D + 16 of the one-step lemma is exactly the
    checker's split index LS = 10;
  * simulates member 40 and computes the block's first read tau, the tail window start t1 and margin psi
    (as in calculus.cpp's extend);
  * replays the Lean check `checkPart` in Python: every cell first read after tau and before
    t1 + 104*40 must have its prescribed child in the C++ child list (fixed / split / moving by phi), and
    every cell first read in [t1, t1+104) a tail child.  It also reports that the prescribed children are
    exactly the C++ children (no child unused).
The hints are not trusted by Lean: `checkPart` recomputes and verifies everything.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_lean_channels import parse

DX = [0, 1, 0, -1]; DY = [1, 0, -1, 0]          # N E S W; north = +y
LS = 10
V = (-2, -2)
DIAGN = {(2, 2): 'pp', (2, -2): 'pm', (-2, 2): 'mp', (-2, -2): 'mm'}


def runpos(cells, T):
    B = set(cells); x = y = 0; h = 0; P = []
    for _ in range(T):
        P.append((x, y))
        if (x, y) in B: B.remove((x, y)); h = (h + 3) % 4
        else: B.add((x, y)); h = (h + 1) % 4
        x += DX[h]; y += DY[h]
    return P


def phi(z): return -z[0] - z[1]                    # Diag.mm.phi
def dphi(u): return lambda z: (1 if u[0] > 0 else -1) * z[0] + (1 if u[1] > 0 else -1) * z[1]
def add(a, b, k=1): return (a[0] + k * b[0], a[1] + k * b[1])


def level1_hints(ldir):
    src = open(os.path.join(ldir, 'TwoBlack', 'Level1Data.lean')).read()
    pat = (r'\(⟨\.mm, \[\], \[⟨(-?\d+), (-?\d+)⟩\]⟩, ⟨(\d+), (-?\d+), (-?\d+), \[([\d, ]+)\], (\d+), '
           r'⟨(-?\d+), (-?\d+)⟩, (-?\d+)⟩\)')
    out = []
    for h in re.findall(pat, src):
        out.append(dict(z0=(int(h[0]), int(h[1])), n=int(h[2]), D=int(h[3]), C=int(h[4]),
                        ms=[int(x) for x in h[5].split(',')], s=int(h[6]), u=(int(h[7]), int(h[8])), A=int(h[9])))
    assert len(out) == 22
    return out


def main():
    src, ldir = sys.argv[1], sys.argv[2]
    parents = parse(src)
    hints = level1_hints(ldir)
    rows = []; allok = True
    for p, H in zip(parents, hints):
        assert p['z0'] == H['z0'] and H['n'] == 40
        z0, C, ms, s, u = H['z0'], H['C'], H['ms'], H['s'], H['u']
        J = len(ms)
        D = H['D'] if J == 1 else H['D'] + 4 * LS - 13
        k1 = {(dg, tuple(near), tuple(far), base) for (dg, near, far, base, _) in p['k1']}
        k2 = {(tuple(vs), tuple((b, tuple(i)) for b, i in bl), tuple(n0)) for (vs, bl, n0) in p['k2']}
        b = add(z0, V, 40)
        psu = dphi(u)
        P = runpos([b], s + 104 * 120)
        psi = max(psu(P[w]) for w in range(s))
        L = 1
        while min(psu(P[w]) for w in range(s + 104 * L, s + 104 * (L + 1))) <= psi + 4: L += 1
        t1 = s + 104 * L; T2 = t1 + 104 * 40
        tau = P.index(b)
        ok = ms[0] + 104 <= tau < t1 and (J == 1 or tau < ms[1]) and D >= 19
        du = DIAGN[u]; used1 = set(); used2 = set(); seen = set()
        for t in range(T2):
            z = P[t]
            if z not in seen and t > tau:
                f = phi(z)
                if f <= D + 12: key = ('mm', (z,), (z0,), 40); good = key in k1; used1.add(key)
                elif f <= D + 16:
                    key = (('mm', 'mm'), ((z0, (0, 1)), (add(z, V, -LS), (0,))), (LS, 40 - LS)); good = key in k2; used2.add(key)
                else: key = ('mm', (), (z0, add(z, V, -40)), 40); good = key in k1; used1.add(key)
                ok &= good
                if t1 <= t < t1 + 104:
                    fu = phi(u)
                    if f > D + 16 and fu >= 0: key = (('mm', du), ((z0, (0,)), (add(z, V, -40), (0, 1))), (40, 40))
                    elif f <= D + 12 and fu <= 0: key = (('mm', du), ((z0, (0,)), (z, (1,))), (40, 40))
                    else: key = None
                    ok &= key in k2; used2.add(key)
            seen.add(z)
        exact = used1 == k1 and used2 == k2
        print(f"{z0}: J={J} D={D} tau={tau} t1={t1} psi={psi} children {len(k1)}+{len(k2)} "
              f"{'OK' if ok else 'FAIL'}{' exact' if exact else ' (some children unused)'}")
        allok &= ok
        msl = ', '.join(map(str, ms))
        rows.append(f"  (⟨{z0[0]}, {z0[1]}⟩, ⟨40, {D}, {C}, [{msl}], {s}, ⟨{u[0]}, {u[1]}⟩, {H['A']}⟩, "
                    f"⟨{tau}, {t1}, {psi}, .{du}⟩)")
    if not allok:
        sys.exit('partition replay FAILED')
    with open(os.path.join(ldir, 'TwoBlack', 'PartData.lean'), 'w') as f:
        f.write('''/-
  Lemma 6.3 for the 22 channel parents, discharged by the partition check on member 40 of each parent
  (generated by gen_lean_part.py).  The corridor hints are those of `level1Families`, except that the
  two-switch parent uses D = 52, so that the near/far threshold D + 16 = 68 of the one-step lemma is the
  checker's split index 10.
-/
import TwoBlack.PartCheck
import TwoBlack.Chan.All

namespace TwoBlack

/-- Block, corridor hint, partition hint. -/
def partHints : List (Pt × Hint1 × PartHint) := [
''')
        f.write(',\n'.join(rows))
        f.write('''
]

def partHintFor (F : Fam1) : Option (Hint1 × PartHint) :=
  match partHints.find? (fun e => [e.1] == F.far) with
  | some e => some e.2
  | none => none

def partOK (F : Fam1) : Bool :=
  match partHintFor F with
  | some (H, P) => checkPart F H P (kidsIn chanTable F)
  | none => false

theorem part_checks : level1Families.all (fun p => partOK p.1) = true := by native_decide

/-- **Lemma 6.3 for the 22 channel parents** (the hypothesis `hpart` of `two_black_final`). -/
theorem hpart_proved : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kidsIn chanTable p.1) := by
  intro p hp
  have h := List.all_eq_true.mp part_checks p hp
  unfold partOK at h
  split at h
  · next H P _ => exact checkPart_sound p.1 H P _ h
  · exact absurd h (by simp)

end TwoBlack
''')
    print('wrote PartData.lean')


if __name__ == '__main__':
    main()
