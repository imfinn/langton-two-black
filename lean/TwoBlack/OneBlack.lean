/-
  The one-black theorem, proved with the corridor calculus (an independent route to Ke's theorem).

  Canonical pose: the ant at the origin heading north, one black cell anywhere.  The blank run is the
  d = 0 parent: every cell is either never read, first read before the tail cutoff (2,432 cells, each
  certified by a certificate search inside Lean), or deep on one of the 22 channels (a verified
  one-corridor family).
-/
import TwoBlack.Level1
import TwoBlack.Parent0

namespace TwoBlack

/-- Hints for the blank parent: certificate at s = 10504 with drift (−2,−2), tail window at t1 = 10816. -/
def blankHint : Hint0 := ⟨10504, .mm, 49, 10816, 31, 0, 4000⟩

theorem blank_check : check0 [] blankHint level1Families = true := by native_decide

/-- **One black cell, canonical pose.**  With the ant at the origin heading north, a single black cell
anywhere leads to the period-104 highway. -/
theorem one_black_canonical : ∀ z, ReachesP104 (initState [z]) := by
  intro z
  have := check0_sound [] blankHint level1Families blank_check z
    (by intro t ht; simp [blankHint] at ht)
  simpa using this

/-- The blank start reaches the highway. -/
theorem blank_reaches : ReachesP104 (initState []) := certB_sound [] 200 (by native_decide)

end TwoBlack
