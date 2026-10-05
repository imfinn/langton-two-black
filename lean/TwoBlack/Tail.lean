/-
  First reads, the never-read coupling, and Lemma 6.1 (descent along the tail).
-/
import TwoBlack.Check

namespace TwoBlack

/-- `z` is first read by the run from `x` at time `m`. -/
def FirstRead (x : State) (z : Pt) (m : Nat) : Prop :=
  (run m x).pos = z ∧ ∀ t, t < m → (run t x).pos ≠ z

theorem exists_first (P : Nat → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
  obtain ⟨n, hn⟩ := h
  have : ∀ n, (∃ k, k ≤ n ∧ P k) → ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
    intro n
    induction n with
    | zero =>
      intro ⟨k, hk, hp⟩
      have : k = 0 := by omega
      subst this
      exact ⟨0, hp, fun k hk => by omega⟩
    | succ n ih =>
      intro ⟨k, hk, hp⟩
      by_cases hex : ∃ k, k ≤ n ∧ P k
      · exact ih hex
      · have hk' : k = n + 1 := by
          rcases Nat.lt_or_ge k (n + 1) with h | h
          · exact absurd ⟨k, by omega, hp⟩ hex
          · omega
        subst hk'
        refine ⟨n + 1, hp, fun j hj hpj => hex ⟨j, by omega, hpj⟩⟩
  exact this n ⟨n, Nat.le_refl n, hn⟩

/-- Every cell the run visits has a first read. -/
theorem firstRead_of_visit (x : State) (z : Pt) (h : ∃ t, (run t x).pos = z) : ∃ m, FirstRead x z m := by
  obtain ⟨m, hm, hmin⟩ := exists_first (fun t => (run t x).pos = z) h
  exact ⟨m, hm, hmin⟩

/-- A permanent highway transfers along an observation-preserving coupling. -/
theorem reaches_of_obs_eq (x y : State) (h : ∀ t, observe (run t y) = observe (run t x))
    (hx : ReachesP104 x) : ReachesP104 y := by
  obtain ⟨n, v, hv, hp⟩ := hx
  refine ⟨n, v, hv, fun c ph hph => ?_⟩
  rw [← run_add n (c * 104 + ph) y, ← run_add n ph y, h, h, run_add n (c * 104 + ph) x, run_add n ph x]
  exact hp c ph hph

/-- **Never-read coupling.**  If the run from `initState P` never visits `z`, then adding `z` as a black
cell changes nothing the ant observes, so the highway transfers. -/
theorem reaches_add_unread (P : List Pt) (z : Pt) (hz : ∀ t, (run t (initState P)).pos ≠ z)
    (hP : ReachesP104 (initState P)) : ReachesP104 (initState (P ++ [z])) := by
  apply reaches_of_obs_eq (initState P) (initState (P ++ [z])) _ hP
  have h0 : Agree (fun w => w ≠ z) Pt.zero (initState P) (initState (P ++ [z])) := by
    refine ⟨by simp [initState]; exact (Pt.add_zero _).symm, rfl, ?_⟩
    intro w hw
    simp only [initState, Pt.add_zero]
    apply bool_eq_of_iff
    rw [contains_iff, contains_iff]
    simp [hw]
  intro t
  have A := agree_run t h0 (fun j _ => hz j)
  obtain ⟨hpos, hdir, hb⟩ := A
  simp only [observe]
  rw [hpos, hdir, Pt.add_zero]
  have := hb _ (hz t)
  rw [Pt.add_zero] at this
  rw [this]

/-- Periodic positions after `s` with drift `v`. -/
def PeriodicAfter (x : State) (s : Nat) (v : Pt) : Prop :=
  ∀ t, s ≤ t → (run (t + 104) x).pos = (run t x).pos + v

theorem periodicAfter_iter {x : State} {s : Nat} {v : Pt} (h : PeriodicAfter x s v) :
    ∀ c t, s ≤ t → (run (t + c * 104) x).pos = (run t x).pos + Pt.smul (c : Int) v := by
  intro c
  induction c with
  | zero => intro t _; simp; apply Pt.ext' <;> simp
  | succ c ih =>
    intro t ht
    rw [show t + (c + 1) * 104 = (t + c * 104) + 104 by rw [Nat.succ_mul]; omega]
    rw [h _ (by omega), ih t ht]
    apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega

/-- **Lemma 6.1 (descent along the tail), one step.**  Suppose the run is periodic after `s` with drift
`v = δ.v` (so φ = δ.phi increases by 4 per period), every read before `s` has φ ≤ ψ, and every read in the
window `[t1, t1 + 104)` (with `s ≤ t1`) has φ > ψ + 4.  If `z` is first read at `m ≥ t1 + 104`, then
`z − v` is first read at `m − 104`. -/
theorem descent_step (x : State) (δ : Diag) (s t1 : Nat) (ψ : Int)
    (hper : PeriodicAfter x s δ.v) (hst : s ≤ t1)
    (hpre : ∀ t, t < s → δ.phi (run t x).pos ≤ ψ)
    (hwin : ∀ j, j < 104 → δ.phi (run (t1 + j) x).pos > ψ + 4)
    (z : Pt) (m : Nat) (hz : FirstRead x z m) (hm : t1 + 104 ≤ m) :
    FirstRead x (z - δ.v) (m - 104) := by
  obtain ⟨hzm, hmin⟩ := hz
  -- every read at a time ≥ t1 + 104 has φ > ψ + 8
  have late : ∀ t, t1 + 104 ≤ t → δ.phi (run t x).pos > ψ + 8 := by
    intro t ht
    obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = (t1 + j) + c * 104 :=
      ⟨(t - t1) / 104, (t - t1) % 104, Nat.mod_lt _ (by decide), by omega⟩
    have hc : 1 ≤ c := by omega
    rw [periodicAfter_iter hper c (t1 + j) (by omega), Diag.phi_add, Diag.phi_smul, Diag.phi_v]
    have := hwin j hj
    omega
  have hprev : (run (m - 104) x).pos = z - δ.v := by
    have := hper (m - 104) (by omega)
    rw [show m - 104 + 104 = m by omega, hzm] at this
    rw [this, Pt.add_sub_cancel]
  refine ⟨hprev, fun r hr e => ?_⟩
  rcases Nat.lt_or_ge r s with hrs | hrs
  · have h1 := hpre r hrs
    have h2 := late m hm
    rw [e, Diag.phi_sub, Diag.phi_v, ← hzm] at h1
    omega
  · have := hper r hrs
    rw [e, Pt.sub_add_cancel] at this
    exact hmin (r + 104) (by omega) this

/-- **Lemma 6.1, iterated.**  If `z` is first read at `m ≥ t1 + 104·j`, then `z − j·v` is first read at
`m − 104·j`. -/
theorem descent (x : State) (δ : Diag) (s t1 : Nat) (ψ : Int)
    (hper : PeriodicAfter x s δ.v) (hst : s ≤ t1)
    (hpre : ∀ t, t < s → δ.phi (run t x).pos ≤ ψ)
    (hwin : ∀ j, j < 104 → δ.phi (run (t1 + j) x).pos > ψ + 4) :
    ∀ j z m, FirstRead x z m → t1 + 104 * j ≤ m →
      FirstRead x (z - Pt.smul (j : Int) δ.v) (m - 104 * j) := by
  intro j
  induction j with
  | zero =>
    intro z m hz _
    have e : z - Pt.smul ((0 : Nat) : Int) δ.v = z := by apply Pt.ext' <;> simp
    rw [e, show m - 104 * 0 = m by omega]; exact hz
  | succ j ih =>
    intro z m hz hm
    have h1 := ih z m hz (by omega)
    have h2 := descent_step x δ s t1 ψ hper hst hpre hwin _ _ h1 (by omega)
    have e1 : z - Pt.smul (j : Int) δ.v - δ.v = z - Pt.smul ((j + 1 : Nat) : Int) δ.v := by
      apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
    rw [e1, show m - 104 * j - 104 = m - 104 * (j + 1) by omega] at h2
    exact h2

end TwoBlack
