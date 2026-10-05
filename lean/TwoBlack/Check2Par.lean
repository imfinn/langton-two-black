/-
  An executable checker for two-corridor families with parallel drifts, sound by `par_family`
  (Proposition 5.2 for parallel corridors, via Lemma 5.1(c)), and the bridge to the channel children.
-/
import TwoBlack.PerpKids
import TwoBlack.Par

namespace TwoBlack
open Std

/-- foreign reads (corridor-1 phases of the other side) lie in corridor 2's zone `Z` -/
def zoneOkB (c1 c2 : CorridorData) (far : Bool) (t : Nat) (p : Pt) : Bool :=
  (List.range (c1.J + 1)).all (fun q => !(inIntB c1 q t) || q % 2 == sideBit far ||
    ((!(decide (parRho c1 c2 far > 0)) || decide (c2.δ.phi p ≥ c2.C)) &&
     (!(decide (parRho c1 c2 far < 0)) || decide (c2.δ.phi p ≤ c2.D))))

def zoneLoopB (c1 c2 : CorridorData) (far : Bool) : FState → Nat → Nat → Bool
  | _, _, 0 => true
  | f, t, k + 1 => zoneOkB c1 c2 far t f.pos && zoneLoopB c1 c2 far f.step (t + 1) k

theorem zoneLoopB_sound {c1 c2 : CorridorData} {far : Bool} {f : FState} {t k : Nat}
    (h : zoneLoopB c1 c2 far f t k = true) : ∀ j, j < k → zoneOkB c1 c2 far (t + j) (frun j f).pos = true := by
  induction k generalizing f t with
  | zero => intro j hj; omega
  | succ k ih =>
    simp only [zoneLoopB, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j => rw [frun, show t + (j + 1) = (t + 1) + j by omega]; exact ih h.2 j (by omega)

/-- the band of corridor 2 lies in corridor 1's zone on side `far` (arithmetic form) -/
def bandB (c1 c2 : CorridorData) (far : Bool) : Bool :=
  if c2.δ = c1.δ then (if far then decide (c2.D + 9 ≥ c1.C) else decide (c2.C - 9 ≤ c1.D))
  else (if far then decide (-c2.C + 9 ≥ c1.C) else decide (-c2.D - 9 ≤ c1.D))

/-- per-block conditions making the column initial relations hold on every row -/
def colOkB (F : Fam2) (H : Hint2) (far : Bool) : Bool :=
  let Δ := F.δ2.phi F.δ1.v
  F.blocks.all (fun blk =>
    let e1 : Int := if blk.2.1 then 1 else 0
    let sf : Int := if far then 1 else 0
    let p := F.cell H.a0 0 blk
    if blk.2.2 then decide (F.δ2.phi (p + Pt.smul (H.b0 : Int) F.δ2.v) ≥ H.C2 - 4) && decide ((e1 - sf) * Δ ≥ 0)
    else decide (F.δ2.phi p < H.C2 - 16) && decide ((e1 - sf) * Δ ≤ 0))

def check2par (F : Fam2) (H : Hint2) (far : Bool) : Bool :=
  let cells := F.cells H.a0 H.b0
  let f0 := FState.init cells
  let Sc := frun H.s f0
  let Sc' := frun 104 Sc
  let G : Pt → Bool := fun z => decide (dot H.u z > H.A)
  let c1 := H.cd1 F
  let c2 := H.cd2 F
  stdDriftB H.u && (Sc'.pos == Sc.pos + H.u) && (Sc'.dir == Sc.dir) &&
  agreeB G H.u Sc.black Sc'.black && readsB G Sc 104 &&
  decide (F.δ2 = F.δ1 ∨ F.δ2 = F.δ1.flip) &&
  corrB c1 f0 H.s H.u && corrB c2 f0 H.s H.u && h1pB c1 c2 &&
  (List.range c2.J).all (fun i => qOfFn c1 c2 (i + 1) % 2 == sideBit far) &&
  bandB c1 c2 far &&
  zoneLoopB c1 c2 far f0 0 (H.s + 104) &&
  (c1.J % 2 == sideBit far ||
    ((!(decide (parRho c1 c2 far > 0)) || decide (c2.δ.phi H.u ≥ 0)) &&
     (!(decide (parRho c1 c2 far < 0)) || decide (c2.δ.phi H.u ≤ 0)))) &&
  (F.row1 H.b0).far.all (fun b => decide (F.δ1.phi (b + Pt.smul (H.a0 : Int) F.δ1.v) ≥ H.C1 - 4)) &&
  (F.row1 H.b0).near.all (fun b => decide (F.δ1.phi b < H.C1 - 16)) &&
  colOkB F H far

theorem col2_member (F : Fam2) (a : Nat) :
    (∀ b ∈ (F.col2 a).near, ∃ blk ∈ F.blocks, blk.2.2 = false ∧ b = F.cell a 0 blk) ∧
    (∀ b ∈ (F.col2 a).far, ∃ blk ∈ F.blocks, blk.2.2 = true ∧ b = F.cell a 0 blk) := by
  constructor
  · intro b hb
    simp only [Fam2.col2, List.mem_map, List.mem_filter] at hb
    obtain ⟨blk, ⟨hblk, h2⟩, rfl⟩ := hb
    exact ⟨blk, hblk, by simpa using h2, rfl⟩
  · intro b hb
    simp only [Fam2.col2, List.mem_map, List.mem_filter] at hb
    obtain ⟨blk, ⟨hblk, h2⟩, rfl⟩ := hb
    exact ⟨blk, hblk, h2, rfl⟩

theorem check2par_sound (F : Fam2) (H : Hint2) (far : Bool) (hc : check2par F H far = true) :
    ∀ a b, ReachesP104 (initState (F.cells (H.a0 + a) (H.b0 + b))) := by
  simp only [check2par, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hstd, hpos⟩, hdir⟩, hag⟩, hreads⟩, hpar⟩, hc1⟩, hc2⟩, hH⟩, hside⟩, hband⟩,
    hzone⟩, htail⟩, hf1⟩, hn1⟩, hcol⟩ := hc
  simp only [colOkB, List.all_eq_true] at hcol
  let cells := F.cells H.a0 H.b0
  have runX : ∀ t, run t (initState cells) = (frun t (FState.init cells)).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  have hu := stdDriftB_sound hstd
  have hagS : Agree (fun z => dot H.u z > H.A) H.u (run H.s (initState cells)) (run (H.s + 104) (initState cells)) := by
    rw [runX, runX, frun_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [FState.toState_pos, FState.toState_pos]; exact hpos
    · rw [FState.toState_dir, FState.toState_dir]; exact hdir
    · intro z hz
      rw [FState.toState_black, FState.toState_black]
      exact agreeB_sound hag z (by simp; exact hz)
  have hin : ∀ j, j < 104 → dot H.u (run (H.s + j) (initState cells)).pos > H.A := by
    intro j hj
    rw [runX, frun_add, FState.toState_pos]
    have := readsB_sound hreads j hj
    simp at this
    exact this
  have reach0 := reaches_of_certificate (initState cells) H.s H.u H.A hu hagS hin
  have per := halfplane_obs (initState cells) (fun z => dot H.u z > H.A) H.u H.s 104 (by decide)
    (fun z hz => stdDrift_dot_pos hu z H.A hz) hagS hin
  let X : Nat → Nat → State := fun a b => initState (F.cells (H.a0 + a) (H.b0 + b))
  have eRow : ∀ a b, X a b = initState ((F.row1 (H.b0 + b)).cells (H.a0 + a)) := fun a b =>
    initState_sameCells (F.row1_same _ _)
  have eCol : ∀ a b, X a b = initState ((F.col2 (H.a0 + a)).cells (H.b0 + b)) := fun a b =>
    initState_sameCells (F.col2_same _ _)
  have init1 := fam_init (F.row1 H.b0) H.a0 H.C1 hf1 hn1
  have hparδ : (H.cd2 F).δ = (H.cd1 F).δ ∨ (H.cd2 F).δ = (H.cd1 F).δ.flip := hpar
  have hH' := h1pB_sound _ _ hH
  have gap1 : ∀ j, 1 ≤ j → j < (H.cd1 F).J → (H.cd1 F).m j + 104 < (H.cd1 F).m (j + 1) := by
    have := corrB_sound (H.cd1 F) cells (X 1 0) H.s H.u H.A hu hagS hin hc1
    -- the gap condition does not depend on the initial relation; extract it from corrB directly
    simp only [corrB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc1
    intro j hj1 hj2
    have h := hc1.1.1.1.1.2 j (List.mem_range.mpr hj2)
    simp at h
    rcases h with h | h
    · omega
    · exact h
  have hsJ1 : (H.cd1 F).start (H.cd1 F).J ≤ H.s := by
    simp only [corrB, Bool.and_eq_true, decide_eq_true_eq] at hc1; exact hc1.1.1.1.2
  -- Δ and the column initial relations on every row
  have hΔ : parDelta (H.cd1 F) (H.cd2 F) = F.δ2.phi F.δ1.v := rfl
  have init2 : ∀ a k : Nat, Rid F.δ2 ((parIter (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) far a).C + 4 * (k : Int)) (X a k) (X a (k + 1)) := by
    intro a k
    have hΔv : F.δ2.phi F.δ1.v = 4 ∨ F.δ2.phi F.δ1.v = -4 := by
      rcases hpar with h | h <;> rw [h] <;> simp [Diag.flip_phi]
    have shiftCell : ∀ blk : Pt × Bool × Bool, F.δ2.phi (F.cell (H.a0 + a) 0 blk) =
        F.δ2.phi (F.cell H.a0 0 blk) + (if blk.2.1 then (a : Int) * F.δ2.phi F.δ1.v else 0) := by
      intro blk
      rw [Fam2.cell_a F (H.a0 + a) 0, Fam2.cell_a F H.a0 0]
      cases blk.2.1 <;> simp [Diag.phi_smul] <;> push_cast <;> simp only [Int.add_mul] <;> omega
    have hCa : (parIter (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) far a).C = H.C2 + (if far then (a : Int) * F.δ2.phi F.δ1.v else 0) := by
      simp [parIter, hΔ]; rfl
    have hf2a : ∀ b ∈ (F.col2 (H.a0 + a)).far,
        F.δ2.phi (b + Pt.smul (H.b0 : Int) F.δ2.v) ≥ (parIter (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) far a).C - 4 := by
      intro b hb
      obtain ⟨blk, hblk, h2, rfl⟩ := (col2_member F (H.a0 + a)).2 b hb
      have hb' := hcol blk hblk
      simp only [h2, if_true, Bool.and_eq_true, decide_eq_true_eq] at hb'
      rw [Diag.phi_add, shiftCell, hCa]
      rw [Diag.phi_add] at hb'
      rcases hΔv with e | e <;> rw [e] at hb' ⊢ <;> cases hb1 : blk.2.1 <;> cases far <;>
        simp [hb1] at hb' ⊢ <;> omega
    have hn2a : ∀ b ∈ (F.col2 (H.a0 + a)).near, F.δ2.phi b < (parIter (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) far a).C - 16 := by
      intro b hb
      obtain ⟨blk, hblk, h2, rfl⟩ := (col2_member F (H.a0 + a)).1 b hb
      have hb' := hcol blk hblk
      simp only [h2, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at hb'
      rw [shiftCell, hCa]
      rcases hΔv with e | e <;> rw [e] at hb' ⊢ <;> cases hb1 : blk.2.1 <;> cases far <;>
        simp [hb1] at hb' ⊢ <;> omega
    have := fam_init (F.col2 (H.a0 + a)) H.b0 _ hf2a hn2a k
    rw [eCol, eCol, show H.b0 + (k + 1) = H.b0 + k + 1 by omega]
    exact this
  have h1 : CorridorHyp (H.cd1 F) (X 0 0) (X 1 0) := by
    have hi : Rid (H.cd1 F).δ (H.cd1 F).C (initState cells) (X 1 0) := by
      have := init1 0
      have e0 : initState cells = initState ((F.row1 H.b0).cells H.a0) :=
        initState_sameCells (F.row1_same _ _)
      have e1 : (F.row1 H.b0).δ = F.δ1 := rfl
      rw [eRow 1 0, e0]
      rw [e1] at this
      simpa [Hint2.cd1] using this
    exact corrB_sound (H.cd1 F) cells (X 1 0) H.s H.u H.A hu hagS hin hc1 hi
  have h2 : CorridorHyp (H.cd2 F) (X 0 0) (X 0 1) := by
    have hi : Rid (H.cd2 F).δ (H.cd2 F).C (initState cells) (X 0 1) := by
      have := init2 0 0
      simpa [parIter, Hint2.cd2, X, cells] using this
    exact corrB_sound (H.cd2 F) cells (X 0 1) H.s H.u H.A hu hagS hin hc2 hi
  -- ParHyp at the base
  have hP : ParHyp (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) far (X 0 0) := by
    refine ⟨hH', fun j hj1 hj2 => ?_, ?_, ?_⟩
    · have := hside (j - 1) (List.mem_range.mpr (by omega))
      rw [show j - 1 + 1 = j by omega] at this
      exact this
    · intro z hz1 hz2
      simp only [bandB] at hband
      rcases hpar with h | h
      · have hc : (H.cd2 F).δ = (H.cd1 F).δ := h
        rw [if_pos hc] at hband
        rw [hc] at hz1 hz2
        cases far <;> simp at hband ⊢ <;> omega
      · have hc : (H.cd2 F).δ = (H.cd1 F).δ.flip := h
        have hne : ¬ ((H.cd2 F).δ = (H.cd1 F).δ) := by rw [hc]; cases (H.cd1 F).δ <;> decide
        rw [if_neg hne] at hband
        rw [hc, Diag.flip_phi] at hz1 hz2
        cases far <;> simp at hband ⊢ <;> omega
    · intro q t hq hI hqs
      have zfin : ∀ t, t < H.s + 104 → (H.cd1 F).InInt q t →
          (parRho (H.cd1 F) (H.cd2 F) far > 0 → (H.cd2 F).δ.phi (run t (initState cells)).pos ≥ (H.cd2 F).C) ∧
          (parRho (H.cd1 F) (H.cd2 F) far < 0 → (H.cd2 F).δ.phi (run t (initState cells)).pos ≤ (H.cd2 F).D) := by
        intro t ht hI
        have h1 := zoneLoopB_sound hzone t ht
        simp only [Nat.zero_add, zoneOkB, List.all_eq_true, List.mem_range] at h1
        have h2 := h1 q (by omega)
        have hib : inIntB (H.cd1 F) q t = true := by
          simp only [inIntB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not]
          refine ⟨hI.1, ?_⟩
          by_cases hqJ : q < (H.cd1 F).J
          · exact Or.inr (hI.2 hqJ)
          · exact Or.inl hqJ
        have hne : (q % 2 == sideBit far) = false := by simp; exact hqs
        simp only [hib, hne, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h2
        rw [runX]
        constructor
        · intro hr; rcases h2.1 with h | h
          · exact absurd hr h
          · exact h
        · intro hr; rcases h2.2 with h | h
          · exact absurd hr h
          · exact h
      by_cases ht : t < H.s + 104
      · exact zfin t ht hI
      · -- the tail: only the last interval of corridor 1, and periodicity
        have hqJ : q = (H.cd1 F).J := by
          rcases Nat.lt_or_ge q (H.cd1 F).J with hlt | hge
          · exfalso
            have h2 := hI.2 hlt
            have hmono := m_mono (H.cd1 F) gap1 (q + 1) (H.cd1 F).J (by omega) (by omega) (Nat.le_refl _)
            have hsJ' : (H.cd1 F).m (H.cd1 F).J ≤ H.s := by
              have := hsJ1; unfold CorridorData.start at this; split at this
              · omega
              · exact this
            omega
          · omega
        subst hqJ
        obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = H.s + c * 104 + j :=
          ⟨(t - H.s) / 104, (t - H.s) % 104, Nat.mod_lt _ (by decide), by omega⟩
        have hp : (run (H.s + c * 104 + j) (initState cells)).pos =
            (run (H.s + j) (initState cells)).pos + Pt.smul (c : Int) H.u := by
          have := congrArg Obs.pos (per c j)
          simpa [observe, Obs.shift] using this
        have hI' : (H.cd1 F).InInt (H.cd1 F).J (H.s + j) := ⟨by omega, fun h => absurd h (Nat.lt_irrefl _)⟩
        have base := zfin (H.s + j) (by omega) hI'
        have hne : ((H.cd1 F).J % 2 == sideBit far) = false := by simp; exact hqs
        simp only [hne, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not, decide_eq_true_eq] at htail
        show (parRho (H.cd1 F) (H.cd2 F) far > 0 → (H.cd2 F).δ.phi (run (H.s + c * 104 + j) (initState cells)).pos ≥ (H.cd2 F).C) ∧
          (parRho (H.cd1 F) (H.cd2 F) far < 0 → (H.cd2 F).δ.phi (run (H.s + c * 104 + j) (initState cells)).pos ≤ (H.cd2 F).D)
        rw [hp, Diag.phi_add, Diag.phi_smul]
        have hu2 : (H.cd2 F).δ.phi H.u = 4 ∨ (H.cd2 F).δ.phi H.u = 0 ∨ (H.cd2 F).δ.phi H.u = -4 := phi_std (H.cd2 F).δ hu
        constructor
        · intro hr
          have b := base.1 hr
          rcases htail.1 with h | h
          · exact absurd hr h
          · rcases hu2 with e | e | e <;> rw [e] at h ⊢ <;> omega
        · intro hr
          have b := base.2 hr
          rcases htail.2 with h | h
          · exact absurd hr h
          · rcases hu2 with e | e | e <;> rw [e] at h ⊢ <;> omega
  apply par_family (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) far X h1 h2 hparδ hP _ init2 reach0
  intro k
  have := init1 (k + 1)
  rw [eRow (k + 1) 0, eRow (k + 2) 0]
  simp only [Nat.add_zero] at this ⊢
  rw [show H.a0 + (k + 1) + 1 = H.a0 + (k + 2) by omega] at this
  push_cast at this ⊢
  exact this

/-- A parallel child with its side, hints, and slab hints for both parameters below the base. -/
def parOK (c : FamD × List Nat) (far : Bool) (H : Hint2) (slabs1 slabs2 : List Hint1) : Bool :=
  match toFam2? c.1, c.2 with
  | some F, [n1, n2] =>
    check2par F H far && decide (n2 ≤ H.b0) && decide (n1 ≤ H.a0) &&
      slabs1.length == H.a0 - n1 && slabs2.length == H.b0 - n2 &&
      (List.range (H.a0 - n1)).all (fun i => Kid1.ok ⟨F.col2 (n1 + i), n2, slabs1.getD i ⟨0, 0, 0, [], 0, ⟨0, 0⟩, 0⟩⟩) &&
      (List.range (H.b0 - n2)).all (fun i => Kid1.ok ⟨F.row1 (n2 + i), n1, slabs2.getD i ⟨0, 0, 0, [], 0, ⟨0, 0⟩, 0⟩⟩)
  | _, _ => false

theorem parOK_sound (c : FamD × List Nat) (far : Bool) (H : Hint2) (s1 s2 : List Hint1)
    (h : parOK c far H s1 s2 = true) : FamReaches c := by
  unfold parOK at h
  split at h
  · next F n1 n2 hF hb =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨⟨hc, hb0⟩, ha0⟩, _⟩, _⟩, hsl1⟩, hsl2⟩ := h
    intro m ⟨hlen, hge⟩
    rw [hb] at hlen hge
    match m, hlen with
    | [m1, m2], _ =>
      have h1 : n1 ≤ m1 := by have := hge 0 (by simp); simpa using this
      have h2 : n2 ≤ m2 := by have := hge 1 (by simp); simpa using this
      rw [toFam2_cells hF]
      rcases Nat.lt_or_ge m1 H.a0 with hlt | hge'
      · have hk := hsl1 (m1 - n1) (by omega)
        rw [show n1 + (m1 - n1) = m1 by omega] at hk
        have := Kid1.reaches _ hk [m2] ⟨rfl, fun i hi => by
          have : i = 0 := by simp at hi; omega
          subst this; simpa using h2⟩
        simp only [toFamD_cells] at this
        rw [initState_sameCells (F.col2_same m1 m2)]
        exact this
      · rcases Nat.lt_or_ge m2 H.b0 with hlt2 | hge2
        · have hk := hsl2 (m2 - n2) (by omega)
          rw [show n2 + (m2 - n2) = m2 by omega] at hk
          have := Kid1.reaches _ hk [m1] ⟨rfl, fun i hi => by
            have : i = 0 := by simp at hi; omega
            subst this; simpa using h1⟩
          simp only [toFamD_cells] at this
          rw [initState_sameCells (F.row1_same m1 m2)]
          exact this
        · have := check2par_sound F H far hc (m1 - H.a0) (m2 - H.b0)
          rw [show H.a0 + (m1 - H.a0) = m1 by omega, show H.b0 + (m2 - H.b0) = m2 by omega] at this
          exact this
  · simp at h

def parCovered (tab : List ChanEntry)
    (ptab : List ((FamD × List Nat) × Bool × Hint2 × List Hint1 × List Hint1)) : Bool :=
  tab.all (fun e => e.kids2.all (fun c => isPerp c.1 ||
    ptab.any (fun p => p.1 == c && parOK p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)))

theorem parCovered_sound {tab : List ChanEntry}
    {ptab : List ((FamD × List Nat) × Bool × Hint2 × List Hint1 × List Hint1)}
    (h : parCovered tab ptab = true) :
    ∀ e ∈ tab, ∀ c ∈ e.kids2, isPerp c.1 = false → FamReaches c := by
  intro e he c hc hp
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h e he) c hc
  simp only [hp, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨p, _, hpc, hok⟩ := h1
  rw [← hpc]
  exact parOK_sound p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 hok

end TwoBlack
