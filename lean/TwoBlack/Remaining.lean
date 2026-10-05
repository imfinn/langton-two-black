/-
  `ChannelParentsOK`, reduced to the two statements the paper proves for it (both are now proved in Lean:
  `hpart_proved` in `PartData.lean`, and `two_black_final` in `Final.lean`):

  * `ChildPartition1 F kids` — Lemma 6.3 for a one-corridor parent: every second cell not read by the time
    the parent's block is read is never read at all, or completes the parent to a member of one of the
    child families `kids` (the reviewer's `child_partition`);
  * `FamReaches c` for every child — Proposition 5.2 for the child (one parameter: `check1`; two
    parameters: Lemma 5.1(b–d)).
-/
import TwoBlack.TheoremA

namespace TwoBlack

/-- A family with any number of parameters: drifts, and blocks with the list of parameters they move with. -/
structure FamD where
  vs : List Diag
  blocks : List (Pt × List Nat)
deriving Repr, DecidableEq

def FamD.cell (F : FamD) (m : List Nat) (b : Pt × List Nat) : Pt :=
  b.2.foldl (fun p i => p + Pt.smul ((m.getD i 0 : Nat) : Int) (F.vs.getD i .pp).v) b.1

def FamD.cells (F : FamD) (m : List Nat) : List Pt := F.blocks.map (F.cell m)

/-- `m` is a member at or above the base `base` -/
def AboveBase (base m : List Nat) : Prop :=
  m.length = base.length ∧ ∀ i, i < m.length → base.getD i 0 ≤ m.getD i 0

/-- Every member of the child family at or above its base reaches the highway. -/
def FamReaches (c : FamD × List Nat) : Prop :=
  ∀ m, AboveBase c.2 m → ReachesP104 (initState (c.1.cells m))

/-- Two block lists describe the same set of black cells. -/
def SameCells (L L' : List Pt) : Prop := ∀ z, L.contains z = L'.contains z

theorem initState_sameCells {L L' : List Pt} (h : SameCells L L') : initState L = initState L' := by
  simp only [initState]
  congr 1
  funext z
  exact h z

/-- **Lemma 6.3 for a one-corridor parent with a single far block (the 22 channels).**  For every member
`j ≥ base`, once the run has read the parent's block, every cell `S` not yet read is either never read, or
completes the member to a member of a child family. -/
def ChildPartition1 (F : Fam1) (base : Nat) (kids : List (FamD × List Nat)) : Prop :=
  ∀ z0, F.far = [z0] → F.near = [] →
  ∀ j, base ≤ j → ∀ τ, FirstRead (initState (F.cells j)) (z0 + Pt.smul (j : Int) F.δ.v) τ →
  ∀ S, (∀ t, t ≤ τ → (run t (initState (F.cells j))).pos ≠ S) →
    (∀ t, (run t (initState (F.cells j))).pos ≠ S) ∨
    ∃ c ∈ kids, ∃ m, AboveBase c.2 m ∧ SameCells (c.1.cells m) (F.cells j ++ [S])

/-- `famFor` succeeded, so the window cell has a family in the list. -/
theorem famFor_mem {P : List Pt} {δu : Diag} {z0 : Pt} {fs : List (Fam1 × Hint1)} {periods : Nat}
    (h : famFor P δu z0 fs periods = true) :
    ∃ p ∈ fs, p.1.δ = δu ∧ p.1.near = P ∧ p.1.far = [z0] := by
  simp only [famFor, List.any_eq_true] at h
  obtain ⟨⟨F, H⟩, hm, h2⟩ := h
  dsimp only at h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨(F, H), hm, h2.1.1.1.1, h2.1.1.1.2, h2.1.1.2⟩

/-- Cells first read by the blank run at or after its tail cutoff lie deep on one of the 22 channels. -/
theorem deep_is_channel (F : Pt) (τ : Nat) (hF : FirstRead blankState F τ) (hτ : blankT2 ≤ τ) :
    ∃ p ∈ level1Families, ∃ (z0 : Pt) (j : Nat), p.1.far = [z0] ∧ p.1.near = [] ∧ p.1.δ = .mm ∧ 40 ≤ j ∧
      F = z0 + Pt.smul (j : Int) Diag.mm.v := by
  -- replay the argument of `check0_sound` on the blank run
  have hc := blank_check
  simp only [check0, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpos, hdir⟩, hag⟩, hreads⟩, hst⟩, htd⟩, hpre⟩, hwin⟩, hloop⟩ := hc
  let x := blankState
  have runX : ∀ t, run t x = (frun t (FState.init [])).toState := by
    intro t; rw [frun_toState, FState.init_toState]; rfl
  let G : Pt → Prop := fun z => dot blankHint.δu.v z > blankHint.A
  have hagS : Agree G blankHint.δu.v (run blankHint.s x) (run (blankHint.s + 104) x) := by
    rw [runX, runX, frun_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [FState.toState_pos, FState.toState_pos]; exact hpos
    · rw [FState.toState_dir, FState.toState_dir]; exact hdir
    · intro z hz
      rw [FState.toState_black, FState.toState_black]
      exact agreeB_sound hag z (by simp; exact hz)
  have hin : ∀ j, j < 104 → G (run (blankHint.s + j) x).pos := by
    intro j hj
    rw [runX, frun_add, FState.toState_pos]
    have := readsB_sound hreads j hj
    simp at this
    exact this
  have hu := diag_std blankHint.δu
  have per := halfplane_obs x G blankHint.δu.v blankHint.s 104 (by decide)
    (fun z hz => stdDrift_dot_pos hu z blankHint.A hz) hagS hin
  have hperA : PeriodicAfter x blankHint.s blankHint.δu.v := by
    intro t ht
    obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = blankHint.s + c * 104 + j :=
      ⟨(t - blankHint.s) / 104, (t - blankHint.s) % 104, Nat.mod_lt _ (by decide), by omega⟩
    have e1 := congrArg Obs.pos (per (c + 1) j)
    have e2 := congrArg Obs.pos (per c j)
    simp [observe, Obs.shift] at e1 e2
    rw [show blankHint.s + c * 104 + j + 104 = blankHint.s + (c + 1) * 104 + j by rw [Nat.succ_mul]; omega,
      e1, e2]
    apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
  have hpre' : ∀ t, t < blankHint.s → blankHint.δu.phi (run t x).pos ≤ blankHint.ψ := by
    intro t ht
    have := readsB_sound hpre t ht
    rw [runX, FState.toState_pos]; simpa using this
  have hwin' : ∀ j, j < 104 → blankHint.δu.phi (run (blankHint.t1 + j) x).pos > blankHint.ψ + 4 := by
    intro j hj
    have := readsB_sound hwin j hj
    rw [runX, frun_add, FState.toState_pos]; simpa using this
  have L := loop0_sound [] blankHint.δu blankHint.tdiv blankHint.t1 blankHint.periods level1Families x _ _ _ 0
    hloop (by rw [runX]; rfl) (by intro q; simp)
  let j := (τ - blankHint.t1) / 104
  have hT2 : blankT2 = blankHint.t1 + 104 * 40 := rfl
  have hj40 : 40 ≤ j := by simp only [j]; omega
  have hD := descent x blankHint.δu blankHint.s blankHint.t1 blankHint.ψ hperA hst hpre' hwin' j F τ hF
    (by simp only [j]; omega)
  have hw := (L (τ - 104 * j) (by omega) (by simp only [j]; omega) _ hD (by simp [blankHint]))
    |>.2 (by simp only [j]; omega) (by simp only [j]; omega)
  obtain ⟨p, hp, hδ, hn, hf⟩ := famFor_mem hw
  have hδu : blankHint.δu = Diag.mm := rfl
  rw [hδu] at hf hδ
  refine ⟨p, hp, _, j, hf, hn, hδ, hj40, ?_⟩
  rw [Pt.sub_add_cancel]

/-- **Reduction.**  The child partition for the 22 channel families, together with the highway for every
child family, gives `ChannelParentsOK`. -/
theorem channelParentsOK_of (kids : Fam1 → List (FamD × List Nat))
    (hpart : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kids p.1))
    (hreach : ∀ p ∈ level1Families, ∀ c ∈ kids p.1, FamReaches c) : ChannelParentsOK := by
  intro F τ hF hτ S hS
  obtain ⟨p, hp, z0, j, hf, hn, hδ, hj, rfl⟩ := deep_is_channel F τ hF hτ
  have hcells : p.1.cells j = [z0 + Pt.smul (j : Int) Diag.mm.v] := by
    simp [Fam1.cells, hf, hn, hδ]
  -- the parent run is the run of member j, and the block is first read at τ there as well
  have hF' : FirstRead (initState (p.1.cells j)) (z0 + Pt.smul (j : Int) p.1.δ.v) τ := by
    rw [hcells, hδ]
    refine ⟨?_, fun t ht => ?_⟩
    · have := pos_add_unread_upto [] (z0 + Pt.smul (j : Int) Diag.mm.v) τ (fun t ht => hF.2 t ht) τ (Nat.le_refl _)
      simp only [List.nil_append] at this
      rw [this]; exact hF.1
    · have := pos_add_unread_upto [] (z0 + Pt.smul (j : Int) Diag.mm.v) τ (fun t ht => hF.2 t ht) t (by omega)
      simp only [List.nil_append] at this
      rw [this]; exact hF.2 t ht
  have hS' : ∀ t, t ≤ τ → (run t (initState (p.1.cells j))).pos ≠ S := by rw [hcells]; exact hS
  rcases hpart p hp z0 hf hn j hj τ hF' S hS' with hnever | ⟨c, hc, m, hm, hsame⟩
  · have reach : ReachesP104 (initState (p.1.cells j)) := by
      have := level1_families_reach p hp (j - p.2.n)
      have hn40 : p.2.n ≤ 40 := by
        have hall : level1Families.all (fun p => decide (p.2.n ≤ 40)) = true := by decide
        have := List.all_eq_true.mp hall p hp
        simpa using this
      rw [show p.2.n + (j - p.2.n) = j by omega] at this
      exact this
    have := reaches_add_unread (p.1.cells j) S hnever reach
    rw [hcells] at this
    exact this
  · have := hreach p hp c hc m hm
    rw [initState_sameCells hsame, hcells] at this
    exact this

end TwoBlack
