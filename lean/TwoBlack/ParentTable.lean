/-
  Concrete level-1 parents for the two-cell theorem: one entry per cell `F` first read by the blank run
  before its tail cutoff, with hints for `check0 [F]` and its 22 tail families.
-/
import TwoBlack.Parent0

namespace TwoBlack

structure PEntry where
  F : Pt
  tau : Nat
  H : Hint0
  fs : List (Fam1 × Hint1)

def PEntry.ok (e : PEntry) : Bool := check0 [e.F] e.H e.fs

end TwoBlack
