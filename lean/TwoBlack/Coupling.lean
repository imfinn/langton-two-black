/-
  Lemma 2.1 (first-difference coupling) and the "untouched cells keep their colour" lemma.
-/
import TwoBlack.Basic

namespace TwoBlack

/-- `Agree G τ s s'`: the pose of `s'` is the pose of `s` translated by `τ`, and the colours of `s'` on
`G + τ` are the colours of `s` on `G`. -/
def Agree (G : Pt → Prop) (τ : Pt) (s s' : State) : Prop :=
  s'.pos = s.pos + τ ∧ s'.dir = s.dir ∧ ∀ z, G z → s'.black (z + τ) = s.black z

theorem agree_step {G : Pt → Prop} {τ : Pt} {s s' : State}
    (h : Agree G τ s s') (hp : G s.pos) : Agree G τ (step s) (step s') := by
  obtain ⟨hpos, hdir, hb⟩ := h
  have hc : s'.black (s.pos + τ) = s.black s.pos := hb _ hp
  refine ⟨?_, ?_, ?_⟩
  · simp only [step_pos, hpos, hdir, hc]
    exact Pt.ext' (by simp; omega) (by simp; omega)
  · simp only [step_dir, hpos, hdir, hc]
  · intro z hz
    simp only [step_black, hpos]
    by_cases e : z = s.pos
    · subst e; simp [hc]
    · have e' : ¬ (z + τ = s.pos + τ) := fun h => e (Pt.add_right_cancel h)
      simp [e, e', hb z hz]

/-- **Lemma 2.1.** Two states related by `Agree G τ` stay related for as long as the first run reads only
cells of `G`. -/
theorem agree_run {G : Pt → Prop} {τ : Pt} {s s' : State} (k : Nat)
    (h : Agree G τ s s') (hG : ∀ j, j < k → G (run j s).pos) :
    Agree G τ (run k s) (run k s') := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [run_succ, run_succ]
    exact agree_step (ih (fun j hj => hG j (Nat.lt_succ_of_lt hj))) (hG k (Nat.lt_succ_self k))

/-- A cell the run does not visit keeps its colour. -/
theorem black_untouched (s : State) (z : Pt) (k : Nat)
    (h : ∀ j, j < k → (run j s).pos ≠ z) : (run k s).black z = s.black z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_succ, step_black]
    have hne : ¬ (z = (run k s).pos) := fun e => h k (Nat.lt_succ_self k) e.symm
    simp only [hne, if_false]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))

/-- Interval form: between times `t₀` and `t₀ + k`, a cell not visited keeps its colour. -/
theorem black_untouched_from (s : State) (z : Pt) (t₀ k : Nat)
    (h : ∀ j, j < k → (run (t₀ + j) s).pos ≠ z) :
    (run (t₀ + k) s).black z = (run t₀ s).black z := by
  rw [run_add]
  apply black_untouched
  intro j hj; rw [← run_add]; exact h j hj

/-- Interval form of Lemma 2.1. -/
theorem agree_run_from {G : Pt → Prop} {τ : Pt} {s s' : State} (t₀ t₀' k : Nat)
    (h : Agree G τ (run t₀ s) (run t₀' s'))
    (hG : ∀ j, j < k → G (run (t₀ + j) s).pos) :
    Agree G τ (run (t₀ + k) s) (run (t₀' + k) s') := by
  rw [run_add, run_add]
  apply agree_run k h
  intro j hj; rw [← run_add]; exact hG j hj

end TwoBlack
