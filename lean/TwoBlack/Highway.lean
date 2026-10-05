/-
  The period-104 highway predicate and Lemma 2.2 (half-plane certificate).
-/
import TwoBlack.Coupling

namespace TwoBlack

/-- The four drifts of the standard highway: the quarter-turn rotations of (−2,−2). -/
def StdDrift (v : Pt) : Prop :=
  v = ⟨-2, -2⟩ ∨ v = ⟨2, -2⟩ ∨ v = ⟨2, 2⟩ ∨ v = ⟨-2, 2⟩

/-- From state `s` on, the ant's observations are 104-periodic up to a standard drift. -/
def PermanentP104 (s : State) : Prop :=
  ∃ v, StdDrift v ∧ ∀ c ph, ph < 104 →
    observe (run (c * 104 + ph) s) = (observe (run ph s)).shift (Pt.smul c v)

def ReachesP104 (s : State) : Prop := ∃ n, PermanentP104 (run n s)

def dot (u z : Pt) : Int := u.x * z.x + u.y * z.y

theorem Obs.shift_shift (o : Obs) (a b : Pt) : (o.shift a).shift b = o.shift (a + b) := by
  cases o; simp [Obs.shift, Pt.add_assoc]

/-- **Lemma 2.2 (half-plane certificate), general form.**  `G` is any set with `G + u ⊆ G`.  If the
states at `s` and `s + P` agree on `G` up to translation by `u`, and the run reads only cells of `G` during
`[s, s+P)`, then the run reads only cells of `G` forever after `s`, and every later pair of states `P`
apart agrees in the same way. -/
theorem halfplane_forever (s0 : State) (G : Pt → Prop) (u : Pt) (s P : Nat) (hP : 0 < P)
    (hGu : ∀ z, G z → G (z + u))
    (hag : Agree G u (run s s0) (run (s + P) s0))
    (hin : ∀ j, j < P → G (run (s + j) s0).pos) :
    ∀ j, G (run (s + j) s0).pos ∧ Agree G u (run (s + j) s0) (run (s + P + j) s0) := by
  -- Q j : the run stays in G on [s, s + j)
  have Q : ∀ j, ∀ i, i < j → G (run (s + i) s0).pos := by
    intro j
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      intro i hi
      by_cases hij : i < j
      · exact ih i hij
      · have hi' : i = j := by omega
        subst hi'
        by_cases hjP : i < P
        · exact hin i hjP
        · -- use the agreement at s + (i - P)
          have hk : ∀ l, l < i - P → G (run (s + l) s0).pos := fun l hl => ih l (by omega)
          have hA := agree_run_from s (s + P) (i - P) hag hk
          have e1 : s + P + (i - P) = s + i := by omega
          rw [e1] at hA
          rw [hA.1]
          exact hGu _ (ih (i - P) (by omega))
  intro j
  refine ⟨Q (j + 1) j (by omega), ?_⟩
  exact agree_run_from s (s + P) j hag (fun l hl => Q j l hl)

/-- Observations repeat with period `P` and drift `u` after the certificate time. -/
theorem halfplane_obs (s0 : State) (G : Pt → Prop) (u : Pt) (s P : Nat) (hP : 0 < P)
    (hGu : ∀ z, G z → G (z + u))
    (hag : Agree G u (run s s0) (run (s + P) s0))
    (hin : ∀ j, j < P → G (run (s + j) s0).pos) :
    ∀ c j, observe (run (s + c * P + j) s0) = (observe (run (s + j) s0)).shift (Pt.smul c u) := by
  have H := halfplane_forever s0 G u s P hP hGu hag hin
  intro c
  induction c with
  | zero =>
    intro j; simp [observe, Obs.shift]
    exact Pt.ext' (by simp) (by simp)
  | succ c ih =>
    intro j
    have e : s + (c + 1) * P + j = s + P + (c * P + j) := by rw [Nat.succ_mul]; omega
    rw [e]
    obtain ⟨hG, hpos, hdir, hb⟩ := H (c * P + j)
    have step1 : observe (run (s + P + (c * P + j)) s0) =
        (observe (run (s + (c * P + j)) s0)).shift u := by
      simp only [observe, Obs.shift]
      rw [hpos, hdir, hb _ hG]
    rw [step1, ← Nat.add_assoc, ih j, Obs.shift_shift]
    congr 1
    apply Pt.ext' <;> simp [Int.add_mul] <;> omega

theorem stdDrift_dot_pos {u : Pt} (hu : StdDrift u) (z : Pt) (A : Int) :
    dot u z > A → dot u (z + u) > A := by
  rcases hu with h | h | h | h <;> subst h <;> simp [dot] <;> omega

/-- A half-plane certificate with a standard drift and period 104 proves that the run reaches the
period-104 highway. -/
theorem reaches_of_certificate (s0 : State) (s : Nat) (u : Pt) (A : Int) (hu : StdDrift u)
    (hag : Agree (fun z => dot u z > A) u (run s s0) (run (s + 104) s0))
    (hin : ∀ j, j < 104 → dot u (run (s + j) s0).pos > A) : ReachesP104 s0 := by
  refine ⟨s, u, hu, ?_⟩
  intro c ph _
  have H := halfplane_obs s0 (fun z => dot u z > A) u s 104 (by decide)
    (fun z hz => stdDrift_dot_pos hu z A hz) hag hin c ph
  rw [← run_add, ← run_add, ← Nat.add_assoc]
  exact H

/-- Reaching the highway is invariant under running forward. -/
theorem reaches_of_run (s : State) (n : Nat) (h : ReachesP104 (run n s)) : ReachesP104 s := by
  obtain ⟨m, hm⟩ := h
  exact ⟨n + m, by rw [run_add]; exact hm⟩

end TwoBlack
