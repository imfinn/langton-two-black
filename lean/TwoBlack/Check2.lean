/-
  An executable checker for two-corridor families with perpendicular drifts, sound by `perp_family`
  (Proposition 5.2 for perpendicular corridors), and the bridge to the two-parameter channel children.
-/
import TwoBlack.Perp

namespace TwoBlack
open Std

/-! ### Generic corridor checks on one run -/

/-- The finite corridor checks for data `cd` on the run from `f0`, given a certificate start `s` and drift `u`. -/
def corrB (cd : CorridorData) (f0 : FState) (s : Nat) (u : Pt) : Bool :=
  decide (cd.D + 40 < cd.C) &&
  (List.range cd.J).all (fun i => i == 0 || decide (cd.m i + 104 < cd.m (i + 1))) &&
  decide (cd.start cd.J ≤ s) &&
  (if cd.J % 2 = 0 then decide (cd.δ.phi u ≤ 0) else decide (cd.δ.phi u ≥ 0)) &&
  (List.range cd.J).all (fun i => switchB cd f0 (i + 1)) &&
  c4loopB cd f0 0 (s + 104)

/-- Soundness of the corridor checks, given a certificate for the run. -/
theorem corrB_sound (cd : CorridorData) (cells : List Pt) (x' : State) (s : Nat) (u : Pt) (A : Int)
    (hu : StdDrift u)
    (hag : Agree (fun z => dot u z > A) u (run s (initState cells)) (run (s + 104) (initState cells)))
    (hin : ∀ j, j < 104 → dot u (run (s + j) (initState cells)).pos > A)
    (hc : corrB cd (FState.init cells) s u = true) (hinit : Rid cd.δ cd.C (initState cells) x') :
    CorridorHyp cd (initState cells) x' := by
  simp only [corrB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hDC, hgap⟩, hsJ⟩, hsign⟩, hsw⟩, hc4⟩ := hc
  have runX : ∀ t, run t (initState cells) = (frun t (FState.init cells)).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  have gap : ∀ j, 1 ≤ j → j < cd.J → cd.m j + 104 < cd.m (j + 1) := by
    intro j hj1 hj2
    have := hgap j (List.mem_range.mpr hj2)
    simp at this
    rcases this with h | h
    · omega
    · exact h
  have per := halfplane_obs (initState cells) (fun z => dot u z > A) u s 104 (by decide)
    (fun z hz => stdDrift_dot_pos hu z A hz) hag hin
  have fin : ∀ q, q ≤ cd.J → ∀ t, t < s + 104 → cd.InInt q t →
      (q % 2 = 0 → cd.δ.phi (run t (initState cells)).pos < cd.C - 16) ∧
      (q % 2 = 1 → cd.δ.phi (run t (initState cells)).pos > cd.D + 16) := by
    intro q hq t ht hI
    have h1 := c4loopB_sound hc4 t ht
    simp only [Nat.zero_add, c4okB, List.all_eq_true, List.mem_range] at h1
    have h2 := h1 q (by omega)
    have hib : inIntB cd q t = true := by
      simp only [inIntB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      refine ⟨hI.1, ?_⟩
      by_cases hqJ : q < cd.J
      · exact Or.inr (hI.2 hqJ)
      · exact Or.inl hqJ
    simp only [hib, Bool.not_true, Bool.false_or, boundB] at h2
    rw [runX]
    constructor
    · intro he; simp [he] at h2; exact h2
    · intro he; have : ¬ (q % 2 = 0) := by omega
      simp [this] at h2; exact h2
  refine ⟨hDC, gap, ?_, ?_, ?_, ?_, hinit⟩
  · intro j hj1 hj2
    have h := hsw (j - 1) (List.mem_range.mpr (by omega))
    rw [show j - 1 + 1 = j by omega] at h
    simp only [switchB, Bool.and_eq_true, beq_iff_eq] at h
    rw [runX, runX, frun_add, FState.toState_pos, FState.toState_pos]; exact h.1.1
  · intro j hj1 hj2
    have h := hsw (j - 1) (List.mem_range.mpr (by omega))
    rw [show j - 1 + 1 = j by omega] at h
    simp only [switchB, Bool.and_eq_true, beq_iff_eq] at h
    rw [runX, runX, frun_add, FState.toState_dir, FState.toState_dir]; exact h.1.2
  · intro j hj1 hj2 w hw1 hw2
    have h := hsw (j - 1) (List.mem_range.mpr (by omega))
    rw [show j - 1 + 1 = j by omega] at h
    simp only [switchB, Bool.and_eq_true, beq_iff_eq] at h
    rw [runX, runX, frun_add, FState.toState_black, FState.toState_black]
    have := agreeB_sound h.2 (w - cd.sv j) (by simp [Pt.sub_add_cancel]; exact ⟨hw1, hw2⟩)
    rw [Pt.sub_add_cancel] at this
    exact this
  · intro q hq t hI
    by_cases ht : t < s + 104
    · exact fin q hq t ht hI
    · have hqJ : q = cd.J := by
        rcases Nat.lt_or_ge q cd.J with hlt | hge
        · exfalso
          have h2 := hI.2 hlt
          have hmono := m_mono cd gap (q + 1) cd.J (by omega) (by omega) (Nat.le_refl _)
          have hsJ' : cd.m cd.J ≤ s := by
            have := hsJ; unfold CorridorData.start at this; split at this
            · omega
            · exact this
          omega
        · omega
      subst hqJ
      obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = s + c * 104 + j :=
        ⟨(t - s) / 104, (t - s) % 104, Nat.mod_lt _ (by decide), by omega⟩
      have hp : (run (s + c * 104 + j) (initState cells)).pos =
          (run (s + j) (initState cells)).pos + Pt.smul (c : Int) u := by
        have := congrArg Obs.pos (per c j)
        simpa [observe, Obs.shift] using this
      have hI' : cd.InInt cd.J (s + j) := ⟨by omega, fun h => absurd h (Nat.lt_irrefl _)⟩
      have base := fin cd.J (Nat.le_refl _) (s + j) (by omega) hI'
      rw [hp, Diag.phi_add, Diag.phi_smul]
      constructor
      · intro hpar
        have hb := base.1 hpar
        have hs : cd.δ.phi u ≤ 0 := by simp [hpar] at hsign; exact hsign
        rcases phi_std cd.δ hu with e | e | e <;> rw [e] at hs ⊢ <;> omega
      · intro hpar
        have hb := base.2 hpar
        have hs : cd.δ.phi u ≥ 0 := by
          have : ¬ (cd.J % 2 = 0) := by omega
          simp [this] at hsign; exact hsign
        rcases phi_std cd.δ hu with e | e | e <;> rw [e] at hs ⊢ <;> omega

/-! ### H1′ from switch lists -/

/-- the corridor-1 relation interval holding corridor 2's switch `j` -/
def qOfFn (c1 c2 : CorridorData) (j : Nat) : Nat :=
  ((List.range c1.J).filter (fun i => decide (c1.m (i + 1) + 104 ≤ c2.m j))).length

def h1pB (c1 c2 : CorridorData) : Bool :=
  (List.range c2.J).all (fun i =>
    let j := i + 1
    let q := qOfFn c1 c2 j
    decide (q ≤ c1.J) && (q == 0 || decide (c1.m q + 104 ≤ c2.m j)) &&
      (!(decide (q < c1.J)) || decide (c2.m j + 104 ≤ c1.m (q + 1))))

theorem h1pB_sound (c1 c2 : CorridorData) (h : h1pB c1 c2 = true) : H1p c1 c2 (qOfFn c1 c2) := by
  simp only [h1pB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 h3 => ?_, fun j h1 h2 h3 => ?_⟩
  · have := h (j - 1) (by omega); rw [show j - 1 + 1 = j by omega] at this; exact this.1.1
  · have := h (j - 1) (by omega); rw [show j - 1 + 1 = j by omega] at this
    rcases this.1.2 with e | e
    · omega
    · exact e
  · have := h (j - 1) (by omega); rw [show j - 1 + 1 = j by omega] at this
    rcases this.2 with e | e
    · exact absurd h3 e
    · exact e

/-! ### Two-parameter families -/

/-- blocks move with parameter 1, parameter 2, both, or neither -/
structure Fam2 where
  δ1 : Diag
  δ2 : Diag
  blocks : List (Pt × Bool × Bool)
deriving Repr

def Fam2.cell (F : Fam2) (a b : Nat) (blk : Pt × Bool × Bool) : Pt :=
  blk.1 + (if blk.2.1 then Pt.smul (a : Int) F.δ1.v else Pt.zero) +
    (if blk.2.2 then Pt.smul (b : Int) F.δ2.v else Pt.zero)

def Fam2.cells (F : Fam2) (a b : Nat) : List Pt := F.blocks.map (F.cell a b)

/-- row `b` (parameter 2 fixed) as a one-corridor family in parameter 1 -/
def Fam2.row1 (F : Fam2) (b : Nat) : Fam1 :=
  ⟨F.δ1, (F.blocks.filter (fun blk => !blk.2.1)).map (F.cell 0 b),
    (F.blocks.filter (fun blk => blk.2.1)).map (F.cell 0 b)⟩

/-- column `a` (parameter 1 fixed) as a one-corridor family in parameter 2 -/
def Fam2.col2 (F : Fam2) (a : Nat) : Fam1 :=
  ⟨F.δ2, (F.blocks.filter (fun blk => !blk.2.2)).map (F.cell a 0),
    (F.blocks.filter (fun blk => blk.2.2)).map (F.cell a 0)⟩

theorem Fam2.cell_a (F : Fam2) (a b : Nat) (blk : Pt × Bool × Bool) :
    F.cell a b blk = F.cell 0 b blk + (if blk.2.1 then Pt.smul (a : Int) F.δ1.v else Pt.zero) := by
  simp only [Fam2.cell]
  cases blk.2.1 <;> cases blk.2.2 <;> apply Pt.ext' <;> simp <;> omega

theorem Fam2.cell_b (F : Fam2) (a b : Nat) (blk : Pt × Bool × Bool) :
    F.cell a b blk = F.cell a 0 blk + (if blk.2.2 then Pt.smul (b : Int) F.δ2.v else Pt.zero) := by
  simp only [Fam2.cell]
  cases blk.2.1 <;> cases blk.2.2 <;> apply Pt.ext' <;> simp <;> omega

theorem Fam2.row1_same (F : Fam2) (a b : Nat) : SameCells (F.cells a b) ((F.row1 b).cells a) := by
  intro z
  apply bool_eq_of_iff
  rw [contains_iff, contains_iff, Fam1.mem_cells]
  simp only [Fam2.cells, Fam2.row1, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨blk, hb, rfl⟩
    cases h1 : blk.2.1
    · left; exact ⟨blk, ⟨hb, by simp [h1]⟩, by rw [Fam2.cell_a F a b blk]; simp [h1, Pt.add_zero]⟩
    · right; exact ⟨F.cell 0 b blk, ⟨blk, ⟨hb, h1⟩, rfl⟩, by rw [Fam2.cell_a F a b blk]; simp [h1]⟩
  · rintro (⟨blk, ⟨hb, h1⟩, rfl⟩ | ⟨_, ⟨blk, ⟨hb, h1⟩, rfl⟩, rfl⟩)
    · refine ⟨blk, hb, ?_⟩; rw [Fam2.cell_a F a b blk]; simp at h1; simp [h1, Pt.add_zero]
    · refine ⟨blk, hb, ?_⟩; rw [Fam2.cell_a F a b blk]; simp [h1]

theorem Fam2.col2_same (F : Fam2) (a b : Nat) : SameCells (F.cells a b) ((F.col2 a).cells b) := by
  intro z
  apply bool_eq_of_iff
  rw [contains_iff, contains_iff, Fam1.mem_cells]
  simp only [Fam2.cells, Fam2.col2, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨blk, hb, rfl⟩
    cases h2 : blk.2.2
    · left; exact ⟨blk, ⟨hb, by simp [h2]⟩, by rw [Fam2.cell_b F a b blk]; simp [h2, Pt.add_zero]⟩
    · right; exact ⟨F.cell a 0 blk, ⟨blk, ⟨hb, h2⟩, rfl⟩, by rw [Fam2.cell_b F a b blk]; simp [h2]⟩
  · rintro (⟨blk, ⟨hb, h2⟩, rfl⟩ | ⟨_, ⟨blk, ⟨hb, h2⟩, rfl⟩, rfl⟩)
    · refine ⟨blk, hb, ?_⟩; rw [Fam2.cell_b F a b blk]; simp at h2; simp [h2, Pt.add_zero]
    · refine ⟨blk, hb, ?_⟩; rw [Fam2.cell_b F a b blk]; simp [h2]

/-- Hints for a perpendicular two-corridor family at base `(a0, b0)`. -/
structure Hint2 where
  a0 : Nat
  b0 : Nat
  D1 : Int
  C1 : Int
  ms1 : List Nat
  D2 : Int
  C2 : Int
  ms2 : List Nat
  s : Nat
  u : Pt
  A : Int
deriving Repr

def Hint2.cd1 (H : Hint2) (F : Fam2) : CorridorData :=
  { δ := F.δ1, D := H.D1, C := H.C1, J := H.ms1.length, m := fun j => H.ms1.getD (j - 1) 0 }
def Hint2.cd2 (H : Hint2) (F : Fam2) : CorridorData :=
  { δ := F.δ2, D := H.D2, C := H.C2, J := H.ms2.length, m := fun j => H.ms2.getD (j - 1) 0 }

def check2p (F : Fam2) (H : Hint2) : Bool :=
  let cells := F.cells H.a0 H.b0
  let f0 := FState.init cells
  let Sc := frun H.s f0
  let Sc' := frun 104 Sc
  let G : Pt → Bool := fun z => decide (dot H.u z > H.A)
  stdDriftB H.u && (Sc'.pos == Sc.pos + H.u) && (Sc'.dir == Sc.dir) &&
  agreeB G H.u Sc.black Sc'.black && readsB G Sc 104 &&
  decide (F.δ2.phi F.δ1.v = 0) && decide (F.δ1.phi F.δ2.v = 0) &&
  corrB (H.cd1 F) f0 H.s H.u && corrB (H.cd2 F) f0 H.s H.u && h1pB (H.cd1 F) (H.cd2 F) &&
  (F.row1 H.b0).far.all (fun b => decide (F.δ1.phi (b + Pt.smul (H.a0 : Int) F.δ1.v) ≥ H.C1 - 4)) &&
  (F.row1 H.b0).near.all (fun b => decide (F.δ1.phi b < H.C1 - 16)) &&
  (F.col2 H.a0).far.all (fun b => decide (F.δ2.phi (b + Pt.smul (H.b0 : Int) F.δ2.v) ≥ H.C2 - 4)) &&
  (F.col2 H.a0).near.all (fun b => decide (F.δ2.phi b < H.C2 - 16))

/-- Moving along parameter 1 does not change φ₂ of the column family's blocks (perpendicularity). -/
theorem col2_phi (F : Fam2) (hp : F.δ2.phi F.δ1.v = 0) (a a' : Nat) :
    (∀ b ∈ (F.col2 a).near, ∃ b' ∈ (F.col2 a').near, F.δ2.phi b = F.δ2.phi b') ∧
    (∀ b ∈ (F.col2 a).far, ∃ b' ∈ (F.col2 a').far, F.δ2.phi b = F.δ2.phi b') := by
  have key : ∀ blk : Pt × Bool × Bool, F.δ2.phi (F.cell a 0 blk) = F.δ2.phi (F.cell a' 0 blk) := by
    intro blk
    rw [Fam2.cell_a F a 0, Fam2.cell_a F a' 0]
    cases blk.2.1 <;> simp [Diag.phi_smul, hp]
  constructor
  · intro b hb
    simp only [Fam2.col2, List.mem_map] at hb ⊢
    obtain ⟨blk, hblk, rfl⟩ := hb
    exact ⟨_, ⟨blk, hblk, rfl⟩, key blk⟩
  · intro b hb
    simp only [Fam2.col2, List.mem_map] at hb ⊢
    obtain ⟨blk, hblk, rfl⟩ := hb
    exact ⟨_, ⟨blk, hblk, rfl⟩, key blk⟩

theorem check2p_sound (F : Fam2) (H : Hint2) (hc : check2p F H = true) :
    ∀ a b, ReachesP104 (initState (F.cells (H.a0 + a) (H.b0 + b))) := by
  simp only [check2p, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hstd, hpos⟩, hdir⟩, hag⟩, hreads⟩, hp21⟩, hp12⟩, hc1⟩, hc2⟩, hH⟩, hf1⟩, hn1⟩,
    hf2⟩, hn2⟩ := hc
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
  -- the states of the family, through its rows and columns
  let X : Nat → Nat → State := fun a b => initState (F.cells (H.a0 + a) (H.b0 + b))
  have eRow : ∀ a b, X a b = initState ((F.row1 (H.b0 + b)).cells (H.a0 + a)) := fun a b =>
    initState_sameCells (F.row1_same _ _)
  have eCol : ∀ a b, X a b = initState ((F.col2 (H.a0 + a)).cells (H.b0 + b)) := fun a b =>
    initState_sameCells (F.col2_same _ _)
  have init1 := fam_init (F.row1 H.b0) H.a0 H.C1 hf1 hn1
  -- φ₂ conditions hold on every column, by perpendicularity
  have init2 : ∀ a, ∀ k : Nat, Rid F.δ2 (H.C2 + 4 * (k : Int)) (X a k) (X a (k + 1)) := by
    intro a k
    have hf2a : ∀ b ∈ (F.col2 (H.a0 + a)).far, F.δ2.phi (b + Pt.smul (H.b0 : Int) F.δ2.v) ≥ H.C2 - 4 := by
      intro b hb
      obtain ⟨b', hb', e⟩ := (col2_phi F hp21 (H.a0 + a) H.a0).2 b hb
      have := hf2 b' hb'
      rw [Diag.phi_add] at this ⊢; rw [e]; exact this
    have hn2a : ∀ b ∈ (F.col2 (H.a0 + a)).near, F.δ2.phi b < H.C2 - 16 := by
      intro b hb
      obtain ⟨b', hb', e⟩ := (col2_phi F hp21 (H.a0 + a) H.a0).1 b hb
      rw [e]; exact hn2 b' hb'
    have := fam_init (F.col2 (H.a0 + a)) H.b0 H.C2 hf2a hn2a k
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
    have := corrB_sound (H.cd1 F) cells (X 1 0) H.s H.u H.A hu hagS hin hc1 hi
    exact this
  have h2 : CorridorHyp (H.cd2 F) (X 0 0) (X 0 1) := by
    have hi : Rid (H.cd2 F).δ (H.cd2 F).C (initState cells) (X 0 1) := by
      have := init2 0 0
      simpa [Hint2.cd2, X, cells] using this
    exact corrB_sound (H.cd2 F) cells (X 0 1) H.s H.u H.A hu hagS hin hc2 hi
  have hH' := h1pB_sound _ _ hH
  apply perp_family (H.cd1 F) (H.cd2 F) (qOfFn (H.cd1 F) (H.cd2 F)) X h1 h2 hp21 hp12 hH' _ init2 reach0
  intro k
  have := init1 (k + 1)
  rw [eRow (k + 1) 0, eRow (k + 2) 0]
  simp only [Nat.add_zero] at this ⊢
  rw [show H.a0 + (k + 1) + 1 = H.a0 + (k + 2) by omega] at this
  push_cast at this ⊢
  exact this

end TwoBlack
