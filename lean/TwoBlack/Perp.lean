/-
  Lemma 5.1(b): structure preservation for a perpendicular corridor.

  Corridor 1 (data `c1`) relates the runs from `x` (member n) and `x'` (member n + e₁).  Corridor 2 (data
  `c2`, perpendicular to corridor 1) satisfies the corridor hypotheses on the run from `x`.  If every
  switch window of corridor 2 lies inside the non-window part of one relation interval `qOf j` of
  corridor 1 (condition H1′), then corridor 2 satisfies the corridor hypotheses on the run from `x'`, with
  switch j delayed by the corridor-1 lag `104 · qOf j`.  H1′ persists, so the step iterates.
-/
import TwoBlack.Channels

namespace TwoBlack

/-- H1′: switch window j of corridor 2 lies strictly between the windows of corridor 1 around interval
`qOf j`. -/
structure H1p (c1 c2 : CorridorData) (qOf : Nat → Nat) : Prop where
  qle : ∀ j, 1 ≤ j → j ≤ c2.J → qOf j ≤ c1.J
  lo : ∀ j, 1 ≤ j → j ≤ c2.J → 1 ≤ qOf j → c1.m (qOf j) + 104 ≤ c2.m j
  hi : ∀ j, 1 ≤ j → j ≤ c2.J → qOf j < c1.J → c2.m j + 104 ≤ c1.m (qOf j + 1)

/-- corridor 2's data on the next member: switch j delayed by the lag of its corridor-1 interval -/
def CorridorData.shiftBy (c2 : CorridorData) (qOf : Nat → Nat) : CorridorData :=
  { c2 with m := fun j => c2.m j + 104 * qOf j }

/-- Every time of the next member's run is the image of a time in some relation interval of corridor 1,
strictly before the interval's right end. -/
theorem time_cover (c1 : CorridorData) (gap : ∀ j, 1 ≤ j → j < c1.J → c1.m j + 104 < c1.m (j + 1))
    (t' : Nat) : ∃ q, q ≤ c1.J ∧ 104 * q ≤ t' ∧ c1.start q ≤ t' - 104 * q ∧
      (q < c1.J → t' - 104 * q < c1.m (q + 1) + 104) := by
  obtain ⟨q, hq, hmin⟩ := exists_first (fun q => c1.J ≤ q ∨ t' < c1.m (q + 1) + 104 * (q + 1))
    ⟨c1.J, Or.inl (Nat.le_refl _)⟩
  have hqJ : q ≤ c1.J := by
    rcases Nat.lt_or_ge c1.J q with h | h
    · exact absurd (Or.inl (Nat.le_refl _)) (hmin c1.J h)
    · exact h
  have hlow : 1 ≤ q → c1.m q + 104 * q ≤ t' := by
    intro h1
    have := hmin (q - 1) (by omega)
    simp only [not_or] at this
    rw [show q - 1 + 1 = q by omega] at this
    omega
  refine ⟨q, hqJ, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos q with h | h
    · subst h; omega
    · have := hlow h; omega
  · unfold CorridorData.start; split
    · omega
    · next h => have := hlow (by omega); omega
  · intro hlt
    rcases hq with h | h
    · omega
    · rw [Nat.mul_succ] at h; omega

theorem phi_perp_pos {δ1 δ2 : Diag} (hp : δ2.phi δ1.v = 0) (z : Pt) : δ2.phi (z + δ1.v) = δ2.phi z := by
  rw [Diag.phi_add, hp]; omega

/-- The relation of corridor 1 preserves the φ₂-value of the position. -/
theorem phi2_of_Rq {δ1 δ2 : Diag} {D C : Int} {q : Nat} {s s' : State} (hp : δ2.phi δ1.v = 0)
    (h : Rq δ1 D C q s s') : δ2.phi s'.pos = δ2.phi s.pos := by
  unfold Rq at h
  split at h
  · rw [h.1.1, Pt.add_zero]
  · rw [h.1.1, phi_perp_pos hp]

/-- Which half of corridor 1's relation to use at `z`: it depends only on φ₁(z). -/
def selId (δ1 : Diag) (D C : Int) (q : Nat) (z : Pt) : Bool :=
  if q % 2 = 0 then decide (δ1.phi z < C - 4) else !(decide (δ1.phi z > D + 12))

/-- Corridor 1's relation, read as a translation of the board by `0` or `v₁` chosen by `selId`. -/
theorem board_of_Rq {δ1 : Diag} {D C : Int} {q : Nat} {s s' : State} (hDC : D + 40 < C)
    (h : Rq δ1 D C q s s') (z : Pt) :
    (selId δ1 D C q z = true → s'.black z = s.black z) ∧
    (selId δ1 D C q z = false → s'.black z = s.black (z - δ1.v)) := by
  unfold Rq at h
  unfold selId
  split at h
  · next he =>
    obtain ⟨⟨_, _, hb⟩, hF⟩ := h
    simp only [he, if_true, decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hz => ?_, fun hz => hF z (by omega)⟩
    have := hb z hz; rw [Pt.add_zero] at this; exact this
  · next he =>
    obtain ⟨⟨_, _, hb⟩, hF⟩ := h
    simp only [he, if_false, Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_false',
      decide_eq_true_eq]
    refine ⟨fun hz => hF z (by omega), fun hz => ?_⟩
    have := hb (z - δ1.v) (by simp; omega); rw [Pt.sub_add_cancel] at this; exact this

theorem selId_phi {δ1 : Diag} {D C : Int} {q : Nat} {z w : Pt} (h : δ1.phi z = δ1.phi w) :
    selId δ1 D C q z = selId δ1 D C q w := by
  simp [selId, h]

/-- **Lemma 5.1(b).**  Perpendicular corridor 2 keeps its corridor hypotheses when corridor 1 is
lengthened by one period. -/
theorem perp_succ (c1 c2 : CorridorData) (qOf : Nat → Nat) (x x' y' : State)
    (h1 : CorridorHyp c1 x x') (h2 : CorridorHyp c2 x y')
    (hp21 : c2.δ.phi c1.δ.v = 0) (hp12 : c1.δ.phi c2.δ.v = 0)
    (hH : H1p c1 c2 qOf) (y'' : State) (hinit : Rid c2.δ c2.C x' y'') :
    CorridorHyp (c2.shiftBy qOf) x' y'' := by
  have R := corridor c1 x x' h1
  have hmono := m_mono c1 h1.gap
  -- the relation at the two ends of corridor 2's switch window j
  have atSw : ∀ j, 1 ≤ j → j ≤ c2.J →
      Rq c1.δ c1.D c1.C (qOf j) (run (c2.m j) x) (run (c2.m j + 104 * qOf j) x') ∧
      Rq c1.δ c1.D c1.C (qOf j) (run (c2.m j + 104) x) (run (c2.m j + 104 + 104 * qOf j) x') := by
    intro j hj1 hj2
    have hq := hH.qle j hj1 hj2
    have hs : c1.start (qOf j) ≤ c2.m j := by
      unfold CorridorData.start; split
      · omega
      · next h => have := hH.lo j hj1 hj2 (by omega); omega
    refine ⟨R (qOf j) hq _ hs (fun hlt => ?_), R (qOf j) hq _ (by omega) (fun hlt => ?_)⟩
    · have := hH.hi j hj1 hj2 hlt; omega
    · have := hH.hi j hj1 hj2 hlt; omega
  refine ⟨h2.hDC, ?_, ?_, ?_, ?_, ?_, hinit⟩
  · -- gap
    intro j hj1 hj2
    simp only [CorridorData.shiftBy] at hj2 ⊢
    have g := h2.gap j hj1 hj2
    -- the corridor-1 interval index is monotone along corridor 2's switches
    have hq : qOf j ≤ qOf (j + 1) := by
      rcases Nat.lt_or_ge (qOf (j + 1)) (qOf j) with hlt | hge
      · exfalso
        have a1 := hH.hi (j + 1) (by omega) (by omega) (by have := hH.qle j hj1 (by omega); omega)
        have a2 := hH.lo j hj1 (by omega) (by omega)
        have a3 := hmono (qOf (j + 1) + 1) (qOf j) (by omega) (by omega) (hH.qle j hj1 (by omega))
        omega
      · exact hge
    omega
  · -- C2, position
    intro j hj1 hj2
    simp only [CorridorData.shiftBy] at hj2 ⊢
    obtain ⟨A, B⟩ := atSw j hj1 hj2
    have hsv : CorridorData.sv { c2 with m := fun j => c2.m j + 104 * qOf j } j = c2.sv j := rfl
    rw [hsv, show c2.m j + 104 * qOf j + 104 = c2.m j + 104 + 104 * qOf j by omega]
    have hp := h2.c2pos j hj1 hj2
    unfold Rq at A B
    split at A
    · next he => rw [if_pos he] at B; rw [B.1.1, A.1.1, hp]; pt_ext
    · next he => rw [if_neg he] at B; rw [B.1.1, A.1.1, hp]; pt_ext
  · -- C2, heading
    intro j hj1 hj2
    simp only [CorridorData.shiftBy] at hj2 ⊢
    obtain ⟨A, B⟩ := atSw j hj1 hj2
    rw [show c2.m j + 104 * qOf j + 104 = c2.m j + 104 + 104 * qOf j by omega]
    unfold Rq at A B
    split at A
    · next he => rw [if_pos he] at B; rw [B.1.2.1, A.1.2.1, h2.c2dir j hj1 hj2]
    · next he => rw [if_neg he] at B; rw [B.1.2.1, A.1.2.1, h2.c2dir j hj1 hj2]
  · -- C3: the board relation is a φ₁-dependent translation, and v₂ does not change φ₁
    intro j hj1 hj2 w hw1 hw2
    simp only [CorridorData.shiftBy] at hj2 hw1 hw2 ⊢
    obtain ⟨A, B⟩ := atSw j hj1 hj2
    have hsv : CorridorData.sv { c2 with m := fun j => c2.m j + 104 * qOf j } j = c2.sv j := rfl
    rw [hsv, show c2.m j + 104 * qOf j + 104 = c2.m j + 104 + 104 * qOf j by omega]
    have c3 := h2.c3 j hj1 hj2
    have hsvphi1 : c1.δ.phi (c2.sv j) = 0 := by
      unfold CorridorData.sv; split
      · exact hp12
      · rw [Diag.phi_neg, hp12]; rfl
    have hsvphi2 : c2.δ.phi c1.δ.v = 0 := hp21
    have e1 : c1.δ.phi (w - c2.sv j) = c1.δ.phi w := by rw [Diag.phi_sub, hsvphi1]; omega
    have bB := board_of_Rq h1.hDC B w
    have bA := board_of_Rq h1.hDC A (w - c2.sv j)
    have hsel : selId c1.δ c1.D c1.C (qOf j) (w - c2.sv j) = selId c1.δ c1.D c1.C (qOf j) w :=
      selId_phi e1
    cases hw : selId c1.δ c1.D c1.C (qOf j) w with
    | true =>
      rw [bB.1 hw, bA.1 (by rw [hsel, hw]), c3 w hw1 hw2]
    | false =>
      rw [bB.2 hw, bA.2 (by rw [hsel, hw])]
      have hw1' : c2.δ.phi (w - c1.δ.v) = c2.δ.phi w := by rw [Diag.phi_sub, hp21]; omega
      rw [c3 (w - c1.δ.v) (by omega) (by omega)]
      congr 1; pt_ext
  · -- C4
    intro r hr t' hI
    simp only [CorridorData.shiftBy] at hr hI ⊢
    obtain ⟨q, hqJ, hle, hs, hlt⟩ := time_cover c1 h1.gap t'
    obtain ⟨t, rfl⟩ : ∃ t, t' = t + 104 * q := ⟨t' - 104 * q, by omega⟩
    rw [show t + 104 * q - 104 * q = t by omega] at hs hlt
    have Rt := R q hqJ t hs (fun h => by have := hlt h; omega)
    have hphi := phi2_of_Rq hp21 Rt
    -- interval r of corridor 2 contains the preimage time t
    have hInt : c2.InInt r t := by
      obtain ⟨hI1, hI2⟩ := hI
      refine ⟨?_, fun hrJ => ?_⟩
      · unfold CorridorData.start at hI1 ⊢
        split
        · omega
        · next hr0 =>
          simp only [hr0, if_false] at hI1
          have hqr := hH.qle r (by omega) hr
          rcases Nat.lt_or_ge (qOf r) q with hlt2 | hge2
          · -- t lies in a later corridor-1 interval, which starts after switch window r
            have a1 := hH.hi r (by omega) hr (by omega)
            have a2 := hmono (qOf r + 1) q (by omega) (by omega) hqJ
            have a3 : c1.m q ≤ t := by
              have := hs; unfold CorridorData.start at this; split at this
              · omega
              · exact this
            omega
          · omega
      · have h2' := hI2 hrJ
        dsimp only at h2'
        have hqr := hH.qle (r + 1) (by omega) (by omega)
        rcases Nat.lt_or_ge q (qOf (r + 1)) with hlt2 | hge2
        · have a1 := hH.lo (r + 1) (by omega) (by omega) (by omega)
          have a2 := hmono (q + 1) (qOf (r + 1)) (by omega) (by omega) hqr
          have a3 := hlt (by omega)
          omega
        · omega
    have c4 := h2.c4 r hr t hInt
    rw [hphi]
    exact c4

end TwoBlack

namespace TwoBlack

theorem CorridorData.iter_m (cd : CorridorData) (k j : Nat) : (cd.iter k).m j = cd.m j + 104 * j * k := by
  induction k with
  | zero => simp [CorridorData.iter]
  | succ k ih => simp only [CorridorData.iter, CorridorData.succ, ih]; rw [Nat.mul_succ]; omega

theorem CorridorData.iter_J (cd : CorridorData) (k : Nat) : (cd.iter k).J = cd.J := by
  induction k with
  | zero => rfl
  | succ k ih => simp [CorridorData.iter, CorridorData.succ, ih]

theorem CorridorData.iter_D (cd : CorridorData) (k : Nat) : (cd.iter k).D = cd.D := by
  induction k with
  | zero => rfl
  | succ k ih => simp [CorridorData.iter, CorridorData.succ, ih]

/-- corridor 2's data on member n + k e₁ -/
def CorridorData.shiftIter (c2 : CorridorData) (qOf : Nat → Nat) (k : Nat) : CorridorData :=
  { c2 with m := fun j => c2.m j + 104 * qOf j * k }

theorem shiftIter_succ (c2 : CorridorData) (qOf : Nat → Nat) (k : Nat) :
    (c2.shiftIter qOf k).shiftBy qOf = c2.shiftIter qOf (k + 1) := by
  simp only [CorridorData.shiftBy, CorridorData.shiftIter]
  congr 1
  funext j
  rw [Nat.mul_succ]; omega

/-- H1′ persists when corridor 1 is lengthened. -/
theorem H1p_succ (c1 c2 : CorridorData) (qOf : Nat → Nat) (h : H1p c1 c2 qOf) :
    H1p c1.succ (c2.shiftBy qOf) qOf := by
  refine ⟨fun j h1 h2 => h.qle j h1 h2, fun j h1 h2 h3 => ?_, fun j h1 h2 h3 => ?_⟩
  · have := h.lo j h1 h2 h3
    simp only [CorridorData.succ, CorridorData.shiftBy]; omega
  · have := h.hi j h1 h2 h3
    simp only [CorridorData.succ, CorridorData.shiftBy]; rw [Nat.mul_succ]; omega

/-- **Proposition 5.2 for two perpendicular corridors.**  `X a b` is the initial state of member
(n₁ + a, n₂ + b).  If both corridors' hypotheses hold at the base, the corridors are perpendicular, H1′
holds, consecutive members are related initially along both directions, and the base member reaches the
highway, then every member does. -/
theorem perp_family (c1 c2 : CorridorData) (qOf : Nat → Nat) (X : Nat → Nat → State)
    (h1 : CorridorHyp c1 (X 0 0) (X 1 0)) (h2 : CorridorHyp c2 (X 0 0) (X 0 1))
    (hp21 : c2.δ.phi c1.δ.v = 0) (hp12 : c1.δ.phi c2.δ.v = 0) (hH : H1p c1 c2 qOf)
    (init1 : ∀ k : Nat, Rid c1.δ (c1.C + 4 * ((k : Int) + 1)) (X (k + 1) 0) (X (k + 2) 0))
    (init2 : ∀ a k : Nat, Rid c2.δ (c2.C + 4 * (k : Int)) (X a k) (X a (k + 1)))
    (hx : ReachesP104 (X 0 0)) : ∀ a b, ReachesP104 (X a b) := by
  -- corridor 1 along the row b = 0
  have Hrow : ∀ a, CorridorHyp (c1.iter a) (X a 0) (X (a + 1) 0) := by
    intro a
    induction a with
    | zero => exact h1
    | succ a ih =>
      apply corridor_succ (c1.iter a) (X a 0) (X (a + 1) 0) (X (a + 2) 0) ih
      rw [CorridorData.iter_δ, CorridorData.iter_C]
      have := init1 a
      rw [show c1.C + 4 * (a : Int) + 4 = c1.C + 4 * ((a : Int) + 1) by omega]
      exact this
  have reachRow := corridor_family c1 (fun a => X a 0) h1 init1 hx
  -- corridor 2 on every row
  have Hcol : ∀ a, CorridorHyp (c2.shiftIter qOf a) (X a 0) (X a 1) ∧ H1p (c1.iter a) (c2.shiftIter qOf a) qOf := by
    intro a
    induction a with
    | zero =>
      have e : c2.shiftIter qOf 0 = c2 := by
        simp only [CorridorData.shiftIter, Nat.mul_zero, Nat.add_zero]
      rw [e]; exact ⟨h2, hH⟩
    | succ a ih =>
      obtain ⟨hc, hh⟩ := ih
      have hp21' : (c2.shiftIter qOf a).δ.phi (c1.iter a).δ.v = 0 := by
        rw [CorridorData.iter_δ]; exact hp21
      have hp12' : (c1.iter a).δ.phi (c2.shiftIter qOf a).δ.v = 0 := by
        rw [CorridorData.iter_δ]; exact hp12
      have hi : Rid (c2.shiftIter qOf a).δ (c2.shiftIter qOf a).C (X (a + 1) 0) (X (a + 1) 1) := by
        have := init2 (a + 1) 0
        simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero] at this
        exact this
      have step := perp_succ (c1.iter a) (c2.shiftIter qOf a) qOf (X a 0) (X (a + 1) 0) (X a 1)
        (Hrow a) hc hp21' hp12' hh (X (a + 1) 1) hi
      rw [shiftIter_succ] at step
      refine ⟨step, ?_⟩
      have := H1p_succ (c1.iter a) (c2.shiftIter qOf a) qOf hh
      rw [shiftIter_succ] at this
      exact this
  intro a b
  apply corridor_family (c2.shiftIter qOf a) (fun b => X a b) (Hcol a).1 _ (reachRow a) b
  intro k
  exact init2 a (k + 1)

end TwoBlack
