/-
  Lemma 5.1(c): structure preservation for a parallel corridor (drift ±v₁).

  Corridor 2 lies on one side σ of corridor 1 (`far = true`: beyond it; `far = false`: before it).
  Hypotheses (a checkable form of (H3)):
  * `side`: every switch of corridor 2 happens in a corridor-1 phase of side σ, away from corridor-1
    windows (H1′);
  * `band`: corridor 2's band lies in corridor 1's zone on side σ;
  * `zone`: every foreign read (a read in a corridor-1 phase of the other side, which includes every
    corridor-1 window) has φ₂ beyond corridor 2's zones, on the side given by the sign of
    ρ = (σ near ? Δ : −Δ), where Δ = φ₂(v₁) = ±4.
  Lengthening corridor 1 then keeps corridor 2's hypotheses; when σ = far, corridor 2's zones move by Δ.
-/
import TwoBlack.Perp

namespace TwoBlack

def Diag.flip : Diag → Diag
  | .pp => .mm | .mm => .pp | .pm => .mp | .mp => .pm

@[simp] theorem Diag.flip_phi (δ : Diag) (z : Pt) : δ.flip.phi z = - δ.phi z := by
  cases δ <;> simp [Diag.flip, Diag.phi] <;> omega

theorem Diag.flip_v (δ : Diag) : δ.flip.v = -δ.v := by
  cases δ <;> rfl

/-- φ₂(v₁) -/
def parDelta (c1 c2 : CorridorData) : Int := c2.δ.phi c1.δ.v

def sideBit (far : Bool) : Nat := if far then 1 else 0

def parRho (c1 c2 : CorridorData) (far : Bool) : Int := if far then - parDelta c1 c2 else parDelta c1 c2

structure ParHyp (c1 c2 : CorridorData) (qOf : Nat → Nat) (far : Bool) (x : State) : Prop where
  h1p : H1p c1 c2 qOf
  side : ∀ j, 1 ≤ j → j ≤ c2.J → qOf j % 2 = sideBit far
  band : ∀ z, c2.D + 8 < c2.δ.phi z → c2.δ.phi z < c2.C - 8 →
    (far = true → c1.δ.phi z ≥ c1.C) ∧ (far = false → c1.δ.phi z ≤ c1.D)
  zone : ∀ q t, q ≤ c1.J → c1.InInt q t → q % 2 ≠ sideBit far →
    (parRho c1 c2 far > 0 → c2.δ.phi (run t x).pos ≥ c2.C) ∧
    (parRho c1 c2 far < 0 → c2.δ.phi (run t x).pos ≤ c2.D)

/-- corridor 2's data on the next member -/
def parNext (c1 c2 : CorridorData) (qOf : Nat → Nat) (far : Bool) : CorridorData :=
  let s := if far then parDelta c1 c2 else 0
  { c2 with D := c2.D + s, C := c2.C + s, m := fun j => c2.m j + 104 * qOf j }

theorem pos_of_Rq {δ1 : Diag} {D C : Int} {q : Nat} {s s' : State} (h : Rq δ1 D C q s s') :
    s'.pos = s.pos + (if q % 2 = 0 then Pt.zero else δ1.v) := by
  unfold Rq at h
  split at h
  · next he => rw [h.1.1, if_pos he]
  · next he => rw [h.1.1, if_neg he]

theorem parDelta_cases (c1 c2 : CorridorData) (hpar : c2.δ = c1.δ ∨ c2.δ = c1.δ.flip) :
    (parDelta c1 c2 = 4 ∧ ∀ z, c2.δ.phi z = c1.δ.phi z) ∨
    (parDelta c1 c2 = -4 ∧ ∀ z, c2.δ.phi z = - c1.δ.phi z) := by
  rcases hpar with h | h
  · left; refine ⟨?_, fun z => by rw [h]⟩; simp [parDelta, h]
  · right; refine ⟨?_, fun z => by rw [h, Diag.flip_phi]⟩; simp [parDelta, h]

/-- **Lemma 5.1(c).** -/
theorem par_succ (c1 c2 : CorridorData) (qOf : Nat → Nat) (far : Bool) (x x' y' : State)
    (h1 : CorridorHyp c1 x x') (h2 : CorridorHyp c2 x y')
    (hpar : c2.δ = c1.δ ∨ c2.δ = c1.δ.flip) (hP : ParHyp c1 c2 qOf far x)
    (y'' : State) (hinit : Rid c2.δ (parNext c1 c2 qOf far).C x' y'') :
    CorridorHyp (parNext c1 c2 qOf far) x' y'' ∧ ParHyp c1.succ (parNext c1 c2 qOf far) qOf far x' := by
  have R := corridor c1 x x' h1
  have hmono := m_mono c1 h1.gap
  have hH := hP.h1p
  have hDC1 := h1.hDC
  have hDC2 := h2.hDC
  obtain ⟨hΔ, hlin⟩ | ⟨hΔ, hlin⟩ := parDelta_cases c1 c2 hpar <;>
  · have hv : c2.δ.phi c1.δ.v = parDelta c1 c2 := rfl
    have hv1 : c1.δ.phi c1.δ.v = 4 := Diag.phi_v _
    -- relation at both ends of corridor 2's switch window j
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
    -- interval bookkeeping (as for perpendicular corridors)
    have intMap : ∀ r, r ≤ c2.J → ∀ q t, q ≤ c1.J → c1.start q ≤ t → (q < c1.J → t < c1.m (q + 1) + 104) →
        (parNext c1 c2 qOf far).InInt r (t + 104 * q) → c2.InInt r t := by
      intro r hr q t hqJ hs hlt hI
      obtain ⟨hI1, hI2⟩ := hI
      refine ⟨?_, fun hrJ => ?_⟩
      · unfold CorridorData.start at hI1 ⊢
        split
        · omega
        · next hr0 =>
          simp only [parNext, hr0, if_false] at hI1
          have hqr := hH.qle r (by omega) hr
          rcases Nat.lt_or_ge (qOf r) q with hlt2 | hge2
          · have a1 := hH.hi r (by omega) hr (by omega)
            have a2 := hmono (qOf r + 1) q (by omega) (by omega) hqJ
            have a3 : c1.m q ≤ t := by
              have := hs; unfold CorridorData.start at this; split at this
              · omega
              · exact this
            omega
          · omega
      · have h2' := hI2 hrJ
        simp only [parNext] at h2'
        have hqr := hH.qle (r + 1) (by omega) (by omega)
        rcases Nat.lt_or_ge q (qOf (r + 1)) with hlt2 | hge2
        · have a1 := hH.lo (r + 1) (by omega) (by omega) (by omega)
          have a2 := hmono (q + 1) (qOf (r + 1)) (by omega) (by omega) hqr
          have a3 := hlt (by omega)
          omega
        · omega
    -- every time of x' with its preimage
    have cover : ∀ t', ∃ q t, q ≤ c1.J ∧ t' = t + 104 * q ∧ c1.start q ≤ t ∧
        (q < c1.J → t < c1.m (q + 1) + 104) ∧
        Rq c1.δ c1.D c1.C q (run t x) (run t' x') := by
      intro t'
      obtain ⟨q, hqJ, hle, hs, hlt⟩ := time_cover c1 h1.gap t'
      refine ⟨q, t' - 104 * q, hqJ, by omega, hs, hlt, ?_⟩
      have := R q hqJ (t' - 104 * q) hs (fun h => by have := hlt h; omega)
      rw [show t' - 104 * q + 104 * q = t' by omega] at this
      exact this
    -- the foreign relation interval: a preimage time in a window of corridor 1 is foreign
    have foreignOf : ∀ q t, q ≤ c1.J → c1.start q ≤ t → (q < c1.J → t < c1.m (q + 1) + 104) →
        ∀ q', q' ≤ c1.succ.J → c1.succ.InInt q' (t + 104 * q) → q' % 2 ≠ sideBit far →
        ∃ q'', q'' ≤ c1.J ∧ c1.InInt q'' t ∧ q'' % 2 ≠ sideBit far := by
      intro q t hqJ hs hlt q' hq' hI' hpar'
      have hJ : c1.succ.J = c1.J := rfl
      obtain ⟨hI1, hI2⟩ := hI'
      by_cases e : q' = q
      · subst e; exact ⟨q', hqJ, ⟨hs, hlt⟩, hpar'⟩
      · -- t + 104 q lies in interval q' ≠ q of x': only possible as q' = q − 1, in window q
        have hq'lt : q' < q := by
          rcases Nat.lt_or_ge q' q with h | h
          · exact h
          · exfalso
            have h' : q < q' := by omega
            have : c1.succ.start q' ≤ t + 104 * q := hI1
            unfold CorridorData.start at this; split at this
            · omega
            · simp only [CorridorData.succ] at this
              have a1 := hmono (q + 1) q' (by omega) (by omega) (by rw [hJ] at hq'; exact hq')
              have a2 := hlt (by omega)
              omega
        have hb := hI2 (by rw [hJ]; omega)
        simp only [CorridorData.succ] at hb
        have hq1 : q' + 1 = q ∨ q' + 1 < q := by omega
        rcases hq1 with e1 | e1
        · subst e1
          -- t is in window q' + 1 of x, hence also in interval q'
          refine ⟨q', by omega, ⟨?_, fun _ => by rw [Nat.mul_succ] at hb; omega⟩, hpar'⟩
          have := hs; unfold CorridorData.start at this ⊢
          split
          · omega
          · next h0 =>
            simp only [show q' + 1 ≠ 0 by omega, if_false] at this
            have := h1.gap q' (by omega) (by omega); omega
        · exfalso
          have a1 := hmono (q' + 1) q (by omega) (by omega) hqJ
          have a3 : c1.m q ≤ t := by
            have := hs; unfold CorridorData.start at this; split at this
            · omega
            · exact this
          rw [Nat.mul_succ] at hb
          have : 104 * q ≥ 104 * (q' + 2) := by omega
          omega
    refine ⟨⟨by simp only [parNext]; omega, ?_, ?_, ?_, ?_, ?_, hinit⟩, ?_⟩
    · -- gap
      intro j hj1 hj2
      simp only [parNext] at hj2 ⊢
      have g := h2.gap j hj1 hj2
      have hq : qOf j ≤ qOf (j + 1) := by
        rcases Nat.lt_or_ge (qOf (j + 1)) (qOf j) with hlt | hge
        · exfalso
          have a1 := hH.hi (j + 1) (by omega) (by omega) (by have := hH.qle j hj1 (by omega); omega)
          have a2 := hH.lo j hj1 (by omega) (by omega)
          have a3 := hmono (qOf (j + 1) + 1) (qOf j) (by omega) (by omega) (hH.qle j hj1 (by omega))
          omega
        · exact hge
      omega
    · -- C2 position
      intro j hj1 hj2
      simp only [parNext] at hj2 ⊢
      obtain ⟨A, B⟩ := atSw j hj1 hj2
      have hsv : CorridorData.sv (parNext c1 c2 qOf far) j = c2.sv j := rfl
      simp only [parNext] at hsv
      rw [hsv, show c2.m j + 104 * qOf j + 104 = c2.m j + 104 + 104 * qOf j by omega]
      have hp := h2.c2pos j hj1 hj2
      rw [pos_of_Rq A, pos_of_Rq B, hp]; pt_ext
    · -- C2 heading
      intro j hj1 hj2
      simp only [parNext] at hj2 ⊢
      obtain ⟨A, B⟩ := atSw j hj1 hj2
      rw [show c2.m j + 104 * qOf j + 104 = c2.m j + 104 + 104 * qOf j by omega]
      unfold Rq at A B
      split at A
      · next he => rw [if_pos he] at B; rw [B.1.2.1, A.1.2.1, h2.c2dir j hj1 hj2]
      · next he => rw [if_neg he] at B; rw [B.1.2.1, A.1.2.1, h2.c2dir j hj1 hj2]
    · -- C3: the band lies in one half of corridor 1's relation
      intro j hj1 hj2 w hw1 hw2
      simp only [parNext] at hj2 hw1 hw2 ⊢
      obtain ⟨A, B⟩ := atSw j hj1 hj2
      have hsv : CorridorData.sv (parNext c1 c2 qOf far) j = c2.sv j := rfl
      simp only [parNext] at hsv
      rw [hsv, show c2.m j + 104 * qOf j + 104 = c2.m j + 104 + 104 * qOf j by omega]
      have c3 := h2.c3 j hj1 hj2
      have hside := hP.side j hj1 hj2
      have hsvφ : c1.δ.phi (c2.sv j) = 4 ∨ c1.δ.phi (c2.sv j) = -4 := by
        unfold CorridorData.sv; rcases hpar with h | h <;> split <;> simp [h, Diag.flip_v]
      have bB := board_of_Rq h1.hDC B w
      have bA := board_of_Rq h1.hDC A (w - c2.sv j)
      cases hf : far
      · -- σ near: identity half at w and at w − sv
        simp only [hf, Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hw1 hw2
        have hb := (hP.band w hw1 hw2).2 hf
        have hq0 : qOf j % 2 = 0 := by rw [hside, hf]; rfl
        have s1 : selId c1.δ c1.D c1.C (qOf j) w = true := by simp [selId, hq0]; omega
        have s2 : selId c1.δ c1.D c1.C (qOf j) (w - c2.sv j) = true := by
          simp [selId, hq0]; rcases hsvφ with e | e <;> rw [e] <;> omega
        rw [bB.1 s1, bA.1 s2, c3 w hw1 hw2]
      · -- σ far: translated half at w and w − sv; corridor 2 has moved by v₁
        simp only [hf, ↓reduceIte] at hw1 hw2
        have hq1 : qOf j % 2 = 1 := by rw [hside, hf]; rfl
        have hw1' : c2.D + 8 < c2.δ.phi (w - c1.δ.v) := by rw [Diag.phi_sub, hv]; omega
        have hw2' : c2.δ.phi (w - c1.δ.v) < c2.C - 8 := by rw [Diag.phi_sub, hv]; omega
        have hb := (hP.band (w - c1.δ.v) hw1' hw2').1 hf
        rw [Diag.phi_sub, hv1] at hb
        have s1 : selId c1.δ c1.D c1.C (qOf j) w = false := by simp [selId, hq1]; omega
        have s2 : selId c1.δ c1.D c1.C (qOf j) (w - c2.sv j) = false := by
          simp [selId, hq1]; rcases hsvφ with e | e <;> rw [e] <;> omega
        rw [bB.2 s1, bA.2 s2, c3 (w - c1.δ.v) hw1' hw2']
        congr 1; pt_ext
    · -- C4
      intro r hr t' hI
      simp only [parNext] at hr
      obtain ⟨q, t, hqJ, rfl, hs, hlt, Rt⟩ := cover t'
      have hInt := intMap r hr q t hqJ hs hlt hI
      have c4 := h2.c4 r hr t hInt
      have hp := pos_of_Rq Rt
      simp only [parNext]
      rw [hp, Diag.phi_add]
      by_cases hqs : q % 2 = sideBit far
      · -- same side: the translation is exactly the shift of corridor 2's zones
        cases hf : far
        · have hq0 : q % 2 = 0 := by rw [hqs, hf]; rfl
          simp only [hq0, ↓reduceIte, Diag.phi_zero, Int.add_zero, Bool.false_eq_true]
          exact c4
        · have hq1 : q % 2 = 1 := by rw [hqs, hf]; rfl
          simp only [show ¬ (q % 2 = 0) by omega, ↓reduceIte, hv]
          constructor
          · intro he; have := c4.1 he; omega
          · intro he; have := c4.2 he; omega
      · -- foreign: corridor 2's zones are far away
        have hz := hP.zone q t hqJ ⟨hs, hlt⟩ hqs
        have hshift : (c2.δ.phi (if q % 2 = 0 then Pt.zero else c1.δ.v)) = 0 ∨
            (c2.δ.phi (if q % 2 = 0 then Pt.zero else c1.δ.v)) = parDelta c1 c2 := by
          split
          · left; simp
          · right; rfl
        have hzs : (if far = true then parDelta c1 c2 else 0) = 0 ∨
            (if far = true then parDelta c1 c2 else 0) = parDelta c1 c2 := by
          split
          · right; rfl
          · left; rfl
        have hrho : parRho c1 c2 far = 4 ∨ parRho c1 c2 far = -4 := by
          unfold parRho; split <;> omega
        constructor
        · intro he
          have b := c4.1 he
          rcases hrho with e | e
          · have := hz.1 (by omega); omega
          · have := hz.2 (by omega)
            rcases hshift with e1 | e1 <;> rcases hzs with e2 | e2 <;> rw [e1, e2] <;> omega
        · intro he
          have b := c4.2 he
          rcases hrho with e | e
          · have := hz.1 (by omega)
            rcases hshift with e1 | e1 <;> rcases hzs with e2 | e2 <;> rw [e1, e2] <;> omega
          · have := hz.2 (by omega); omega
    · -- ParHyp for the next member
      refine ⟨?_, fun j h1' h2' => hP.side j h1' h2', ?_, ?_⟩
      · have := H1p_succ c1 c2 qOf hH
        exact { qle := this.qle, lo := this.lo, hi := this.hi }
      · intro z hz1 hz2
        simp only [parNext] at hz1 hz2 ⊢
        constructor
        · intro hf
          simp only [hf, ↓reduceIte] at hz1 hz2
          have hz1' : c2.D + 8 < c2.δ.phi (z - c1.δ.v) := by rw [Diag.phi_sub, hv]; omega
          have hz2' : c2.δ.phi (z - c1.δ.v) < c2.C - 8 := by rw [Diag.phi_sub, hv]; omega
          have := (hP.band _ hz1' hz2').1 hf
          rw [Diag.phi_sub, hv1] at this
          simp only [CorridorData.succ]; omega
        · intro hf
          simp only [hf, Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hz1 hz2
          have := (hP.band z hz1 hz2).2 hf
          simp only [CorridorData.succ]; exact this
      · intro q' t' hq' hI' hpar'
        obtain ⟨q, t, hqJ, rfl, hs, hlt, Rt⟩ := cover t'
        obtain ⟨q'', hq'', hI'', hpar''⟩ := foreignOf q t hqJ hs hlt q' hq' hI' hpar'
        have hz := hP.zone q'' t hq'' hI'' hpar''
        have hp := pos_of_Rq Rt
        have hrho' : parRho c1.succ (parNext c1 c2 qOf far) far = parRho c1 c2 far := rfl
        rw [hrho', hp, Diag.phi_add]
        simp only [parNext]
        -- relative motion of foreign material: 0 (window copy on side σ) or ρ
        have hrho : parRho c1 c2 far = 4 ∨ parRho c1 c2 far = -4 := by
          unfold parRho; split <;> omega
        have hmove : (c2.δ.phi (if q % 2 = 0 then Pt.zero else c1.δ.v)) -
            (if far = true then parDelta c1 c2 else 0) = 0 ∨
            (c2.δ.phi (if q % 2 = 0 then Pt.zero else c1.δ.v)) -
            (if far = true then parDelta c1 c2 else 0) = parRho c1 c2 far := by
          unfold parRho
          by_cases hqs : q % 2 = sideBit far
          · left
            cases hf : far
            · have : q % 2 = 0 := by rw [hqs, hf]; rfl
              simp [this]
            · have : q % 2 = 1 := by rw [hqs, hf]; rfl
              simp [show ¬ (q % 2 = 0) by omega, parDelta]
          · right
            cases hf : far
            · have : q % 2 = 1 := by unfold sideBit at hqs; simp [hf] at hqs; omega
              simp [show ¬ (q % 2 = 0) by omega, parDelta]
            · have : q % 2 = 0 := by unfold sideBit at hqs; simp [hf] at hqs; omega
              simp [this, parDelta]
        constructor
        · intro he
          have := hz.1 he
          rcases hmove with e | e <;> omega
        · intro he
          have := hz.2 he
          rcases hmove with e | e <;> omega

end TwoBlack

namespace TwoBlack

/-- corridor 2's data on member n + a e₁ -/
def parIter (c1 c2 : CorridorData) (qOf : Nat → Nat) (far : Bool) (a : Nat) : CorridorData :=
  let s := if far then (a : Int) * parDelta c1 c2 else 0
  { c2 with D := c2.D + s, C := c2.C + s, m := fun j => c2.m j + 104 * qOf j * a }

theorem parIter_succ (c1 c2 : CorridorData) (qOf : Nat → Nat) (far : Bool) (a : Nat) :
    parNext (c1.iter a) (parIter c1 c2 qOf far a) qOf far = parIter c1 c2 qOf far (a + 1) := by
  have hd : parDelta (c1.iter a) (parIter c1 c2 qOf far a) = parDelta c1 c2 := by
    simp [parDelta, parIter, CorridorData.iter_δ]
  simp only [parNext, hd]
  simp only [parIter]
  congr 1
  · cases far <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
  · cases far <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
  · funext j; rw [Nat.mul_succ]; omega

/-- **Proposition 5.2 for two parallel corridors.** -/
theorem par_family (c1 c2 : CorridorData) (qOf : Nat → Nat) (far : Bool) (X : Nat → Nat → State)
    (h1 : CorridorHyp c1 (X 0 0) (X 1 0)) (h2 : CorridorHyp c2 (X 0 0) (X 0 1))
    (hpar : c2.δ = c1.δ ∨ c2.δ = c1.δ.flip) (hP : ParHyp c1 c2 qOf far (X 0 0))
    (init1 : ∀ k : Nat, Rid c1.δ (c1.C + 4 * ((k : Int) + 1)) (X (k + 1) 0) (X (k + 2) 0))
    (init2 : ∀ a k : Nat, Rid c2.δ ((parIter c1 c2 qOf far a).C + 4 * (k : Int)) (X a k) (X a (k + 1)))
    (hx : ReachesP104 (X 0 0)) : ∀ a b, ReachesP104 (X a b) := by
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
  have Hcol : ∀ a, CorridorHyp (parIter c1 c2 qOf far a) (X a 0) (X a 1) ∧
      ParHyp (c1.iter a) (parIter c1 c2 qOf far a) qOf far (X a 0) := by
    intro a
    induction a with
    | zero =>
      have e : parIter c1 c2 qOf far 0 = c2 := by
        cases c2; simp [parIter]
      rw [e]; exact ⟨h2, hP⟩
    | succ a ih =>
      obtain ⟨hc, hh⟩ := ih
      have hpar' : (parIter c1 c2 qOf far a).δ = (c1.iter a).δ ∨
          (parIter c1 c2 qOf far a).δ = (c1.iter a).δ.flip := by
        simp only [parIter, CorridorData.iter_δ]; exact hpar
      have hi : Rid (parIter c1 c2 qOf far a).δ (parNext (c1.iter a) (parIter c1 c2 qOf far a) qOf far).C
          (X (a + 1) 0) (X (a + 1) 1) := by
        rw [parIter_succ]
        have := init2 (a + 1) 0
        simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero] at this
        exact this
      have step := par_succ (c1.iter a) (parIter c1 c2 qOf far a) qOf far (X a 0) (X (a + 1) 0) (X a 1)
        (Hrow a) hc hpar' hh (X (a + 1) 1) hi
      rw [parIter_succ] at step
      exact step
  intro a b
  apply corridor_family (parIter c1 c2 qOf far a) (fun b => X a b) (Hcol a).1 _ (reachRow a) b
  intro k
  have := init2 a (k + 1)
  simp only [parIter] at this ⊢
  push_cast at this ⊢
  exact this

end TwoBlack
