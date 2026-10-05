/-
  Consequences of the corridor lemma:
  * transfer of the highway from member n to member n + eᵢ;
  * Lemma 5.1(a) for one corridor: the hypotheses hold again for the pair (n + eᵢ, n + 2eᵢ), with the
    far zone moved out by 4 and switch j delayed by 104·j;
  * Proposition 5.2 for one corridor: every member n + k eᵢ reaches the highway.
-/
import TwoBlack.Corridor

namespace TwoBlack

theorem Pt.smul_add (a b : Int) (v : Pt) : Pt.smul a v + Pt.smul b v = Pt.smul (a + b) v := by
  apply Pt.ext' <;> simp [Int.add_mul]

theorem Obs.shift_comm (o : Obs) (a b : Pt) : (o.shift a).shift b = (o.shift b).shift a := by
  rw [Obs.shift_shift, Obs.shift_shift, Pt.add_comm]

/-- A permanent highway is periodic at every phase, not just the first 104. -/
theorem permanent_all {s : State} {v : Pt}
    (hper : ∀ c ph, ph < 104 → observe (run (c * 104 + ph) s) = (observe (run ph s)).shift (Pt.smul c v)) :
    ∀ c t, observe (run (c * 104 + t) s) = (observe (run t s)).shift (Pt.smul c v) := by
  intro c t
  have ht : t = (t / 104) * 104 + t % 104 := by omega
  have hb := Nat.mod_lt t (show 104 > 0 by decide)
  have e1 : c * 104 + t = (c + t / 104) * 104 + t % 104 := by rw [Nat.add_mul]; omega
  rw [e1, hper _ _ hb]
  conv => rhs; rw [ht, hper _ _ hb]
  rw [Obs.shift_shift, Pt.smul_add]
  congr 2
  omega

theorem obs_of_Rid {δ : Diag} {C : Int} {s s' : State} (h : Rid δ C s s') (hp : δ.phi s.pos < C - 4) :
    observe s' = observe s := by
  obtain ⟨⟨hpos, hdir, hb⟩, _⟩ := h
  simp only [observe]
  rw [hpos, hdir, hb _ hp, Pt.add_zero]

theorem obs_of_Rtr {δ : Diag} {D : Int} {s s' : State} (h : Rtr δ D s s') (hp : δ.phi s.pos > D + 8) :
    observe s' = (observe s).shift δ.v := by
  obtain ⟨⟨hpos, hdir, hb⟩, _⟩ := h
  simp only [observe, Obs.shift]
  rw [hpos, hdir, hb _ hp]

/-- **Highway transfer.**  Under the corridor hypotheses, if member n reaches the highway, so does
member n + eᵢ (with certificate time delayed by 104·J). -/
theorem corridor_reaches (cd : CorridorData) (x x' : State) (h : CorridorHyp cd x x')
    (hx : ReachesP104 x) : ReachesP104 x' := by
  obtain ⟨n, v, hv, hper⟩ := hx
  have hall := permanent_all hper
  let n0 := n + cd.start cd.J
  -- observation relation after the start of the last interval
  have key : ∀ t, cd.start cd.J ≤ t →
      observe (run (t + 104 * cd.J) x') =
        (observe (run t x)).shift (if cd.J % 2 = 0 then Pt.zero else cd.δ.v) := by
    intro t ht
    have R := corridor cd x x' h cd.J (Nat.le_refl _) t ht (fun hlt => absurd hlt (Nat.lt_irrefl _))
    have c4 := h.c4 cd.J (Nat.le_refl _) t ⟨ht, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
    unfold Rq at R
    split
    · next he =>
      rw [if_pos he] at R
      rw [obs_of_Rid R (by have := c4.1 he; omega)]
      simp [observe, Obs.shift, Pt.add_zero]
    · next he =>
      rw [if_neg he] at R
      exact obs_of_Rtr R (by have := c4.2 (by omega); omega)
  refine ⟨n0 + 104 * cd.J, v, hv, ?_⟩
  intro c ph _
  rw [← run_add, ← run_add]
  have e1 : n0 + 104 * cd.J + (c * 104 + ph) = (n0 + c * 104 + ph) + 104 * cd.J := by omega
  have e2 : n0 + 104 * cd.J + ph = (n0 + ph) + 104 * cd.J := by omega
  rw [e1, e2, key _ (by omega), key _ (by omega)]
  have p1 : observe (run (n0 + c * 104 + ph) x) = (observe (run (n0 + ph) x)).shift (Pt.smul c v) := by
    have := hall c (cd.start cd.J + ph)
    rw [← run_add, ← run_add] at this
    rw [show n0 + c * 104 + ph = n + (c * 104 + (cd.start cd.J + ph)) by omega,
        show n0 + ph = n + (cd.start cd.J + ph) by omega]
    exact this
  rw [p1, Obs.shift_comm]

/-- Corridor data for the next member: far zone moved out by 4, switch j delayed by 104·j. -/
def CorridorData.succ (cd : CorridorData) : CorridorData :=
  { cd with C := cd.C + 4, m := fun j => cd.m j + 104 * j }

/-- **Lemma 5.1(a), one corridor.**  If the corridor hypotheses hold for the pair (x, x') and the initial
states x', x'' are related by R_id with the far zone moved out by 4, then the hypotheses hold for the pair
(x', x'') with the successor data. -/
theorem corridor_succ (cd : CorridorData) (x x' x'' : State) (h : CorridorHyp cd x x')
    (hinit : Rid cd.δ (cd.C + 4) x' x'') : CorridorHyp cd.succ x' x'' := by
  have R := corridor cd x x' h
  have hDC := h.hDC
  -- relation at the two ends of switch j's window
  have atSwitch : ∀ j, 1 ≤ j → j ≤ cd.J →
      Rq cd.δ cd.D cd.C j (run (cd.m j) x) (run (cd.m j + 104 * j) x') ∧
      Rq cd.δ cd.D cd.C j (run (cd.m j + 104) x) (run (cd.m j + 104 + 104 * j) x') := by
    intro j hj1 hj2
    have hs : cd.start j = cd.m j := by simp [CorridorData.start]; omega
    refine ⟨R j hj2 (cd.m j) (by omega) (fun hlt => ?_), R j hj2 (cd.m j + 104) (by omega) (fun hlt => ?_)⟩
    · have := h.gap j hj1 hlt; omega
    · have := h.gap j hj1 hlt; omega
  refine ⟨by simp [CorridorData.succ]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gap
    intro j hj1 hj2
    simp only [CorridorData.succ]
    have := h.gap j hj1 hj2
    rw [Nat.mul_succ]; omega
  · -- C2, position
    intro j hj1 hj2
    simp only [CorridorData.succ] at hj2 ⊢
    obtain ⟨A, B⟩ := atSwitch j hj1 hj2
    have hp := h.c2pos j hj1 hj2
    have esv : CorridorData.sv { cd with C := cd.C + 4, m := fun j => cd.m j + 104 * j } j = cd.sv j := rfl
    rw [esv, show cd.m j + 104 * j + 104 = cd.m j + 104 + 104 * j by omega]
    unfold Rq at A B
    split at A
    · next he =>
      rw [if_pos he] at B
      rw [B.1.1, A.1.1, hp]; pt_ext
    · next he =>
      rw [if_neg he] at B
      rw [B.1.1, A.1.1, hp]; pt_ext
  · -- C2, heading
    intro j hj1 hj2
    simp only [CorridorData.succ] at hj2 ⊢
    obtain ⟨A, B⟩ := atSwitch j hj1 hj2
    rw [show cd.m j + 104 * j + 104 = cd.m j + 104 + 104 * j by omega]
    unfold Rq at A B
    split at A
    · next he => rw [if_pos he] at B; rw [B.1.2.1, A.1.2.1, h.c2dir j hj1 hj2]
    · next he => rw [if_neg he] at B; rw [B.1.2.1, A.1.2.1, h.c2dir j hj1 hj2]
  · -- C3
    intro j hj1 hj2 w hw1 hw2
    simp only [CorridorData.succ] at hj2 hw1 hw2 ⊢
    obtain ⟨A, B⟩ := atSwitch j hj1 hj2
    have esv : CorridorData.sv { cd with C := cd.C + 4, m := fun j => cd.m j + 104 * j } j = cd.sv j := rfl
    rw [esv, show cd.m j + 104 * j + 104 = cd.m j + 104 + 104 * j by omega]
    have hw : ∀ i, i < 104 → cd.D + 16 < cd.δ.phi (run (cd.m j + i) x).pos ∧
        cd.δ.phi (run (cd.m j + i) x).pos < cd.C - 16 := by
      have := h.window (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      exact this
    have unt := untouched_phi cd.δ x (cd.m j) 104 (cd.D + 16) (cd.C - 16) hw
    have c3 := h.c3 j hj1 hj2
    unfold Rq at A B
    split at A
    · next he =>
      -- inward switch (j even): R_id at both ends, sv = −v
      rw [if_pos he] at B
      have hsv : cd.sv j = -cd.δ.v := by simp [CorridorData.sv]; omega
      rw [hsv] at c3 ⊢
      have ewv : w - -cd.δ.v = w + cd.δ.v := by pt_ext
      rw [ewv]
      have eB := B.1.2.2 w (by omega)
      rw [Pt.add_zero] at eB
      rw [eB]
      by_cases hc : cd.δ.phi w < cd.C - 8
      · rw [c3 w hw1 hc, ewv]
        have eA := A.1.2.2 (w + cd.δ.v) (by simp; omega)
        rw [Pt.add_zero] at eA
        rw [eA]
      · rw [unt w (Or.inr (by omega))]
        have eA := A.2 (w + cd.δ.v) (by simp; omega)
        rw [eA, Pt.add_sub_cancel]
    · next he =>
      -- outward switch (j odd): R_tr at both ends, sv = v
      rw [if_neg he] at B
      have hsv : cd.sv j = cd.δ.v := by simp [CorridorData.sv]; omega
      rw [hsv] at c3 ⊢
      by_cases hc : cd.δ.phi w > cd.D + 16
      · have eB := B.1.2.2 (w - cd.δ.v) (by simp; omega)
        rw [Pt.sub_add_cancel] at eB
        rw [eB, c3 (w - cd.δ.v) (by simp; omega) (by simp; omega)]
        have eA := A.1.2.2 (w - cd.δ.v - cd.δ.v) (by simp; omega)
        rw [Pt.sub_add_cancel] at eA
        rw [eA]
      · have eB := B.2 w (by omega)
        rw [eB, unt w (Or.inl (by omega))]
        have eA := A.2 (w - cd.δ.v) (by simp; omega)
        rw [eA]
        -- run n's board at the switch is v-periodic just above D + 8
        have := c3 w hw1 (by omega)
        rw [unt w (Or.inl (by omega))] at this
        exact this
  · -- C4
    intro q hq t' ht'
    simp only [CorridorData.succ] at hq ht' ⊢
    obtain ⟨hs', hlt'⟩ := ht'
    simp only [CorridorData.start] at hs' hlt'
    by_cases hcase : q < cd.J ∧ cd.m (q + 1) + 104 * (q + 1) ≤ t'
    · -- inside the stretched window of switch q + 1: use relation q + 1
      obtain ⟨hqJ, hge⟩ := hcase
      have hlt := hlt' hqJ
      obtain ⟨i, rfl⟩ : ∃ i, t' = cd.m (q + 1) + i + 104 * (q + 1) := ⟨t' - cd.m (q + 1) - 104 * (q + 1), by omega⟩
      have hi : i < 104 := by omega
      have Rn := R (q + 1) (by omega) (cd.m (q + 1) + i) (by simp [CorridorData.start])
        (fun hlt2 => by have := h.gap (q + 1) (by omega) hlt2; omega)
      have hw := h.window q hqJ i hi
      unfold Rq at Rn
      rcases Nat.mod_two_eq_zero_or_one q with he | he
      · have he' : ¬ ((q + 1) % 2 = 0) := by omega
        rw [if_neg he'] at Rn
        rw [Rn.1.1]
        exact ⟨fun _ => by simp; omega, fun h2 => by omega⟩
      · have he' : (q + 1) % 2 = 0 := by omega
        rw [if_pos he'] at Rn
        rw [Rn.1.1, Pt.add_zero]
        exact ⟨fun h2 => by omega, fun _ => by omega⟩
    · -- an image of a time in relation interval q
      have hst : cd.start q + 104 * q ≤ t' := by
        unfold CorridorData.start; split
        · omega
        · next hq0 => have := hs'; simp [hq0] at this; omega
      obtain ⟨t, rfl⟩ : ∃ t, t' = t + 104 * q := ⟨t' - 104 * q, by omega⟩
      have hin : cd.InInt q t := by
        refine ⟨by omega, fun hqJ => ?_⟩
        have : ¬ (cd.m (q + 1) + 104 * (q + 1) ≤ t + 104 * q) := fun hh => hcase ⟨hqJ, hh⟩
        rw [Nat.mul_succ] at this; omega
      have Rn := R q hq t hin.1 (fun hqJ => by have := hin.2 hqJ; omega)
      have c4 := h.c4 q hq t hin
      unfold Rq at Rn
      split at Rn
      · next he =>
        rw [Rn.1.1, Pt.add_zero]
        exact ⟨fun _ => by have := c4.1 he; omega, fun h2 => by omega⟩
      · next he =>
        rw [Rn.1.1]
        exact ⟨fun h2 => by omega, fun h2 => by have := c4.2 h2; simp; omega⟩
  · exact hinit

/-- Iterated successor data: the corridor data for the pair (n + k eᵢ, n + (k+1) eᵢ). -/
def CorridorData.iter (cd : CorridorData) : Nat → CorridorData
  | 0 => cd
  | k + 1 => (cd.iter k).succ

theorem CorridorData.iter_C (cd : CorridorData) (k : Nat) : (cd.iter k).C = cd.C + 4 * (k : Int) := by
  induction k with
  | zero => simp [iter]
  | succ k ih => simp [iter, succ, ih]; omega

theorem CorridorData.iter_δ (cd : CorridorData) (k : Nat) : (cd.iter k).δ = cd.δ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iter, succ, ih]

/-- **Proposition 5.2, one corridor.**  Let `X k` be the initial state of member n + k eᵢ.  If the
corridor hypotheses hold for (X 0, X 1), consecutive members are related initially by R_id with the far
zone at `C + 4k`, and member n reaches the highway, then every member reaches the highway. -/
theorem corridor_family (cd : CorridorData) (X : Nat → State) (h0 : CorridorHyp cd (X 0) (X 1))
    (hinit : ∀ k : Nat, Rid cd.δ (cd.C + 4 * ((k : Int) + 1)) (X (k + 1)) (X (k + 2)))
    (hx : ReachesP104 (X 0)) : ∀ k, ReachesP104 (X k) := by
  have H : ∀ k, CorridorHyp (cd.iter k) (X k) (X (k + 1)) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      apply corridor_succ (cd.iter k) (X k) (X (k + 1)) (X (k + 2)) ih
      rw [CorridorData.iter_δ, CorridorData.iter_C]
      have := hinit k
      rw [show cd.C + 4 * (k : Int) + 4 = cd.C + 4 * ((k : Int) + 1) by omega]
      exact this
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => exact corridor_reaches (cd.iter k) (X k) (X (k + 1)) (H k) ih

end TwoBlack
