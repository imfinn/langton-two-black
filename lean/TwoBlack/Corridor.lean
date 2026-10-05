/-
  Lemma 4.1 (the corridor lemma), in an abstract form that does not mention families.

  `x` is the initial state of member n and `x'` that of member n + eᵢ.  The corridor has a diagonal
  direction `δ` with functional φ = δ.phi and drift v = δ.v (φ v = 4), zones D < C, and switch times
  m 1 < m 2 < … < m J.  Switch j is outward (σ = +1) for odd j and inward (σ = −1) for even j.
  Relation interval q (0 ≤ q ≤ J) is [start q, m (q+1) + 104), and [m J, ∞) for q = J.
-/
import TwoBlack.Highway

namespace TwoBlack

inductive Diag where
  | pp | pm | mp | mm
deriving DecidableEq, Repr

namespace Diag
def phi : Diag → Pt → Int
  | pp, z => z.x + z.y
  | pm, z => z.x - z.y
  | mp, z => -z.x + z.y
  | mm, z => -z.x - z.y
def v : Diag → Pt
  | pp => ⟨2, 2⟩
  | pm => ⟨2, -2⟩
  | mp => ⟨-2, 2⟩
  | mm => ⟨-2, -2⟩

@[simp] theorem phi_add (δ : Diag) (a b : Pt) : δ.phi (a + b) = δ.phi a + δ.phi b := by
  cases δ <;> simp [phi] <;> omega
@[simp] theorem phi_sub (δ : Diag) (a b : Pt) : δ.phi (a - b) = δ.phi a - δ.phi b := by
  cases δ <;> simp [phi] <;> omega
@[simp] theorem phi_neg (δ : Diag) (a : Pt) : δ.phi (-a) = - δ.phi a := by
  cases δ <;> simp [phi] <;> omega
@[simp] theorem phi_v (δ : Diag) : δ.phi δ.v = 4 := by
  cases δ <;> rfl
@[simp] theorem phi_zero (δ : Diag) : δ.phi Pt.zero = 0 := by
  cases δ <;> rfl
theorem phi_smul (δ : Diag) (k : Int) (a : Pt) : δ.phi (Pt.smul k a) = k * δ.phi a := by
  cases δ <;> simp [phi, Int.mul_add, Int.mul_sub, Int.mul_neg] <;> omega
end Diag

section Relations
variable (δ : Diag) (D C : Int)

/-- Near-phase relation R_id (no lag in position): identical below `C − 4` (on the `s` side),
far content translated by `v` at and above `C − 12`. -/
def Rid (s s' : State) : Prop :=
  Agree (fun z => δ.phi z < C - 4) Pt.zero s s' ∧
  ∀ z, δ.phi z ≥ C - 12 → s'.black z = s.black (z - δ.v)

/-- Far-phase relation R_tr: translated by `v` above `D + 8` (on the `s` side), identical at and below
`D + 16`. -/
def Rtr (s s' : State) : Prop :=
  Agree (fun z => δ.phi z > D + 8) δ.v s s' ∧
  ∀ z, δ.phi z ≤ D + 16 → s'.black z = s.black z

/-- The relation for relation interval `q`. -/
def Rq (q : Nat) (s s' : State) : Prop :=
  if q % 2 = 0 then Rid δ C s s' else Rtr δ D s s'

end Relations

/-- Cells outside the φ-range of a stretch of reads keep their colour. -/
theorem untouched_phi (δ : Diag) (x : State) (t k : Nat) (lo hi : Int)
    (hr : ∀ j, j < k → lo < δ.phi (run (t + j) x).pos ∧ δ.phi (run (t + j) x).pos < hi)
    (z : Pt) (hz : δ.phi z ≤ lo ∨ δ.phi z ≥ hi) :
    (run (t + k) x).black z = (run t x).black z := by
  apply black_untouched_from
  intro j hj e
  have := hr j hj
  rw [e] at this
  omega

theorem untouched_lt (δ : Diag) (x : State) (t k : Nat) (hi : Int)
    (hr : ∀ j, j < k → δ.phi (run (t + j) x).pos < hi)
    (z : Pt) (hz : δ.phi z ≥ hi) : (run (t + k) x).black z = (run t x).black z := by
  apply black_untouched_from
  intro j hj e
  have := hr j hj
  rw [e] at this
  omega

theorem untouched_gt (δ : Diag) (x : State) (t k : Nat) (lo : Int)
    (hr : ∀ j, j < k → lo < δ.phi (run (t + j) x).pos)
    (z : Pt) (hz : δ.phi z ≤ lo) : (run (t + k) x).black z = (run t x).black z := by
  apply black_untouched_from
  intro j hj e
  have := hr j hj
  rw [e] at this
  omega

/-! ### Persistence of the two relations -/

theorem Rid_persist (δ : Diag) (C : Int) (x x' : State) (t t' k : Nat)
    (h : Rid δ C (run t x) (run t' x'))
    (hr : ∀ j, j < k → δ.phi (run (t + j) x).pos < C - 16) :
    Rid δ C (run (t + k) x) (run (t' + k) x') := by
  obtain ⟨hA, hF⟩ := h
  have hAg : ∀ j, j ≤ k → Agree (fun z => δ.phi z < C - 4) Pt.zero (run (t + j) x) (run (t' + j) x') :=
    fun j hj => agree_run_from t t' j hA (fun l hl => by have := hr l (by omega); omega)
  refine ⟨hAg k (Nat.le_refl k), ?_⟩
  intro z hz
  -- x' does not visit z, x does not visit z − v
  have h1 : (run (t' + k) x').black z = (run t' x').black z := by
    apply black_untouched_from
    intro j hj e
    have hp := (hAg j (by omega)).1
    have := hr j hj
    rw [e, Pt.add_zero] at hp
    rw [← hp] at this
    omega
  have h2 : (run (t + k) x).black (z - δ.v) = (run t x).black (z - δ.v) := by
    apply untouched_lt δ x t k (C - 16) hr
    simp; omega
  rw [h1, hF z hz, h2]

theorem Rtr_persist (δ : Diag) (D : Int) (x x' : State) (t t' k : Nat)
    (h : Rtr δ D (run t x) (run t' x'))
    (hr : ∀ j, j < k → δ.phi (run (t + j) x).pos > D + 16) :
    Rtr δ D (run (t + k) x) (run (t' + k) x') := by
  obtain ⟨hA, hF⟩ := h
  have hAg : ∀ j, j ≤ k → Agree (fun z => δ.phi z > D + 8) δ.v (run (t + j) x) (run (t' + j) x') :=
    fun j hj => agree_run_from t t' j hA (fun l hl => by have := hr l (by omega); omega)
  refine ⟨hAg k (Nat.le_refl k), ?_⟩
  intro z hz
  have h1 : (run (t' + k) x').black z = (run t' x').black z := by
    apply black_untouched_from
    intro j hj e
    have hp := (hAg j (by omega)).1
    have := hr j hj
    rw [e] at hp
    have : δ.phi z = δ.phi (run (t + j) x).pos + 4 := by rw [hp]; simp
    omega
  have h2 : (run (t + k) x).black z = (run t x).black z := by
    apply untouched_gt δ x t k (D + 16) (fun j hj => hr j hj)
    exact hz
  rw [h1, hF z hz, h2]

/-! ### The two switch lemmas -/

/-- Outward switch at `m`: R_id at `m + 104` (lag `L`) gives R_tr at `m` (lag `L + 104`). -/
theorem switch_out (δ : Diag) (D C : Int) (x x' : State) (m L : Nat)
    (hR : Rid δ C (run (m + 104) x) (run (m + 104 + L) x'))
    (hpos : (run (m + 104) x).pos = (run m x).pos + δ.v)
    (hdir : (run (m + 104) x).dir = (run m x).dir)
    (hC3 : ∀ w, D + 8 < δ.phi w → δ.phi w < C - 8 →
      (run (m + 104) x).black w = (run m x).black (w - δ.v))
    (hwin : ∀ j, j < 104 → D + 16 < δ.phi (run (m + j) x).pos ∧ δ.phi (run (m + j) x).pos < C - 16)
    (hDC : D + 40 < C) :
    Rtr δ D (run m x) (run (m + 104 + L) x') := by
  obtain ⟨⟨hp, hd, hb⟩, hF⟩ := hR
  have unt := untouched_phi δ x m 104 (D + 16) (C - 16) hwin
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hp, Pt.add_zero, hpos]
  · rw [hd, hdir]
  · intro w hw
    by_cases hc : δ.phi w + 4 < C - 8
    · have e1 := hb (w + δ.v) (by simp; omega)
      rw [Pt.add_zero] at e1
      rw [e1, hC3 (w + δ.v) (by simp; omega) (by simp; omega), Pt.add_sub_cancel]
    · have e1 := hF (w + δ.v) (by simp; omega)
      rw [e1, Pt.add_sub_cancel, unt w (Or.inr (by omega))]
  · intro z hz
    have e1 := hb z (by omega)
    rw [Pt.add_zero] at e1
    rw [e1, unt z (Or.inl hz)]

/-- Inward switch at `m`: R_tr at `m + 104` (lag `L`) gives R_id at `m` (lag `L + 104`). -/
theorem switch_in (δ : Diag) (D C : Int) (x x' : State) (m L : Nat)
    (hR : Rtr δ D (run (m + 104) x) (run (m + 104 + L) x'))
    (hpos : (run (m + 104) x).pos + δ.v = (run m x).pos)
    (hdir : (run (m + 104) x).dir = (run m x).dir)
    (hC3 : ∀ w, D + 8 < δ.phi w → δ.phi w < C - 8 →
      (run (m + 104) x).black w = (run m x).black (w + δ.v))
    (hwin : ∀ j, j < 104 → D + 16 < δ.phi (run (m + j) x).pos ∧ δ.phi (run (m + j) x).pos < C - 16)
    (hDC : D + 40 < C) :
    Rid δ C (run m x) (run (m + 104 + L) x') := by
  obtain ⟨⟨hp, hd, hb⟩, hF⟩ := hR
  have unt := untouched_phi δ x m 104 (D + 16) (C - 16) hwin
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hp, hpos, Pt.add_zero]
  · rw [hd, hdir]
  · intro z hz
    rw [Pt.add_zero]
    by_cases hc : δ.phi z > D + 12
    · have e1 := hb (z - δ.v) (by simp; omega)
      rw [Pt.sub_add_cancel] at e1
      rw [e1, hC3 (z - δ.v) (by simp; omega) (by simp; omega), Pt.sub_add_cancel]
    · have e1 := hF z (by omega)
      rw [e1, unt z (Or.inl (by omega))]
  · intro z hz
    have e1 := hb (z - δ.v) (by simp; omega)
    rw [Pt.sub_add_cancel] at e1
    rw [e1, unt (z - δ.v) (Or.inr (by simp; omega))]

/-! ### Corridor data and hypotheses -/

structure CorridorData where
  δ : Diag
  D : Int
  C : Int
  J : Nat
  m : Nat → Nat

namespace CorridorData
/-- start of relation interval `q` -/
def start (cd : CorridorData) (q : Nat) : Nat := if q = 0 then 0 else cd.m q
/-- the switch displacement σ_j v -/
def sv (cd : CorridorData) (j : Nat) : Pt := if j % 2 = 1 then cd.δ.v else -cd.δ.v
/-- `t` lies in relation interval `q` (closed at the right end if `closed`) -/
def InInt (cd : CorridorData) (q t : Nat) : Prop :=
  cd.start q ≤ t ∧ (q < cd.J → t < cd.m (q + 1) + 104)
end CorridorData

/-- The hypotheses (C1)–(C4) of the corridor lemma for corridor data `cd`, on the run from `x`, together
with the initial relation between `x` and `x'`. -/
structure CorridorHyp (cd : CorridorData) (x x' : State) : Prop where
  hDC : cd.D + 40 < cd.C
  gap : ∀ j, 1 ≤ j → j < cd.J → cd.m j + 104 < cd.m (j + 1)
  c2pos : ∀ j, 1 ≤ j → j ≤ cd.J → (run (cd.m j + 104) x).pos = (run (cd.m j) x).pos + cd.sv j
  c2dir : ∀ j, 1 ≤ j → j ≤ cd.J → (run (cd.m j + 104) x).dir = (run (cd.m j) x).dir
  c3 : ∀ j, 1 ≤ j → j ≤ cd.J → ∀ w, cd.D + 8 < cd.δ.phi w → cd.δ.phi w < cd.C - 8 →
    (run (cd.m j + 104) x).black w = (run (cd.m j) x).black (w - cd.sv j)
  c4 : ∀ q, q ≤ cd.J → ∀ t, cd.InInt q t →
    (q % 2 = 0 → cd.δ.phi (run t x).pos < cd.C - 16) ∧ (q % 2 = 1 → cd.δ.phi (run t x).pos > cd.D + 16)
  init : Rid cd.δ cd.C x x'

namespace CorridorHyp
variable {cd : CorridorData} {x x' : State}

theorem start_le_m (h : CorridorHyp cd x x') (q : Nat) (hq : q < cd.J) : cd.start q ≤ cd.m (q + 1) := by
  unfold CorridorData.start
  split
  · omega
  · have := h.gap q (by omega) hq; omega

/-- The window of switch `q + 1` lies in relation intervals `q` and `q + 1`, so its reads are in the band. -/
theorem window (h : CorridorHyp cd x x') (q : Nat) (hq : q < cd.J) :
    ∀ j, j < 104 → cd.D + 16 < cd.δ.phi (run (cd.m (q + 1) + j) x).pos ∧
      cd.δ.phi (run (cd.m (q + 1) + j) x).pos < cd.C - 16 := by
  intro j hj
  have hs := h.start_le_m q hq
  have i1 : cd.InInt q (cd.m (q + 1) + j) := ⟨by omega, fun _ => by omega⟩
  have i2 : cd.InInt (q + 1) (cd.m (q + 1) + j) := by
    refine ⟨by simp [CorridorData.start], fun hq2 => ?_⟩
    have := h.gap (q + 1) (by omega) hq2; omega
  have a1 := h.c4 q (by omega) _ i1
  have a2 := h.c4 (q + 1) hq _ i2
  rcases Nat.mod_two_eq_zero_or_one q with e | e
  · have e' : (q + 1) % 2 = 1 := by omega
    exact ⟨a2.2 e', a1.1 e⟩
  · have e' : (q + 1) % 2 = 0 := by omega
    exact ⟨a1.2 e, a2.1 e'⟩

end CorridorHyp

/-- **Lemma 4.1 (corridor lemma).**  On every relation interval `q`, including its right end, the run
from `x'` is the run from `x` delayed by `104 q`, related by R_id (q even) or R_tr (q odd). -/
theorem corridor (cd : CorridorData) (x x' : State) (h : CorridorHyp cd x x') :
    ∀ q, q ≤ cd.J → ∀ t, cd.start q ≤ t → (q < cd.J → t ≤ cd.m (q + 1) + 104) →
      Rq cd.δ cd.D cd.C q (run t x) (run (t + 104 * q) x') := by
  -- persistence from the start of interval q
  have persist : ∀ q, q ≤ cd.J → Rq cd.δ cd.D cd.C q (run (cd.start q) x) (run (cd.start q + 104 * q) x') →
      ∀ t, cd.start q ≤ t → (q < cd.J → t ≤ cd.m (q + 1) + 104) →
        Rq cd.δ cd.D cd.C q (run t x) (run (t + 104 * q) x') := by
    intro q hq h0 t ht1 ht2
    obtain ⟨k, rfl⟩ : ∃ k, t = cd.start q + k := ⟨t - cd.start q, by omega⟩
    have hr : ∀ j, j < k → cd.InInt q (cd.start q + j) :=
      fun j hj => ⟨by omega, fun hlt => by have := ht2 hlt; omega⟩
    rw [show cd.start q + k + 104 * q = (cd.start q + 104 * q) + k by omega]
    unfold Rq at h0 ⊢
    split
    · next he =>
      rw [if_pos he] at h0
      exact Rid_persist cd.δ cd.C x x' _ _ _ h0 (fun j hj => (h.c4 q hq _ (hr j hj)).1 he)
    · next he =>
      rw [if_neg he] at h0
      have he' : q % 2 = 1 := by omega
      exact Rtr_persist cd.δ cd.D x x' _ _ _ h0 (fun j hj => (h.c4 q hq _ (hr j hj)).2 he')
  intro q
  induction q with
  | zero =>
    intro hq
    apply persist 0 hq
    simp [CorridorData.start, Rq]
    exact h.init
  | succ q ih =>
    intro hq
    apply persist (q + 1) hq
    have hqJ : q < cd.J := by omega
    have prev := ih (by omega) (cd.m (q + 1) + 104) (by have := h.start_le_m q hqJ; omega) (fun _ => Nat.le_refl _)
    have hst : cd.start (q + 1) = cd.m (q + 1) := by simp [CorridorData.start]
    rw [hst]
    have e : cd.m (q + 1) + 104 * (q + 1) = cd.m (q + 1) + 104 + 104 * q := by rw [Nat.mul_succ]; omega
    rw [e]
    have hw := h.window q hqJ
    unfold Rq at prev ⊢
    rcases Nat.mod_two_eq_zero_or_one q with he | he
    · rw [if_pos he] at prev
      have he' : ¬ ((q + 1) % 2 = 0) := by omega
      rw [if_neg he']
      have hsv : cd.sv (q + 1) = cd.δ.v := by simp [CorridorData.sv]; omega
      apply switch_out cd.δ cd.D cd.C x x' (cd.m (q + 1)) (104 * q) prev
      · rw [h.c2pos (q + 1) (by omega) hq, hsv]
      · exact h.c2dir (q + 1) (by omega) hq
      · intro w h1 h2; rw [h.c3 (q + 1) (by omega) hq w h1 h2, hsv]
      · exact hw
      · exact h.hDC
    · rw [if_neg (by omega)] at prev
      have he' : (q + 1) % 2 = 0 := by omega
      rw [if_pos he']
      have hsv : cd.sv (q + 1) = -cd.δ.v := by simp [CorridorData.sv]; omega
      apply switch_in cd.δ cd.D cd.C x x' (cd.m (q + 1)) (104 * q) prev
      · rw [h.c2pos (q + 1) (by omega) hq, hsv]; pt_ext
      · exact h.c2dir (q + 1) (by omega) hq
      · intro w h1 h2
        rw [h.c3 (q + 1) (by omega) hq w h1 h2, hsv]
        congr 1; pt_ext
      · exact hw
      · exact h.hDC

end TwoBlack
