/-
  The one-black theorem for any ant position and heading, in Ke's form.
-/
import TwoBlack.OneBlack
import TwoBlack.Pose

namespace TwoBlack

def ExactlyOneBlack (s : State) : Prop := ∃ q, ∀ z, s.black z = decide (z = q)

/-- **One-black theorem.**  Every Langton's-ant state with exactly one black cell, at any ant position
and heading, reaches the period-104 highway. -/
theorem one_black : ∀ s, ExactlyOneBlack s → ReachesP104 s := by
  intro s ⟨q, hq⟩
  apply reaches_of_canonical s (initState [canonCell s q]) rfl rfl _ (one_black_canonical _)
  intro z
  simp only [initState, hq, canonCell]
  apply bool_eq_of_iff
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h, Pt.unrotN_rotN]; apply Pt.ext' <;> simp <;> omega
  · intro h
    rw [← h, show Pt.unrotN s.dir.toN z + s.pos + -s.pos = Pt.unrotN s.dir.toN z by
      apply Pt.ext' <;> simp <;> omega, Pt.rotN_unrotN]

end TwoBlack
