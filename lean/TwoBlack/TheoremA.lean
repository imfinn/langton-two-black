/-
  Theorem A (at most two black cells) — the assembly.

  For a pair {a, b}, let F be the cell the blank run reads first and S the other.  Until it reads F, the
  run of {F} is the blank run, so S has not been read by time τ_F.  Everything then reduces to
  `ParentOK F τ_F`: adding any cell not yet read to the parent {F} leads to the highway.

  * `ConcreteParentsOK` (F first read before the blank tail cutoff, 2,432 parents) is discharged by
    computation: `check0 [F]` for every parent (Parents/*.lean) and a coverage pass (`coverLoop`).
  * `ChannelParentsOK` (F deep on one of the 22 channels) is Lemma 6.3 for one-corridor parents together
    with the two-parameter children (Lemma 5.1(b–d)); it is proved in `PartData.lean` and `Final.lean`.
-/
import TwoBlack.General
import TwoBlack.ParentTable

namespace TwoBlack
open Std

def blankState : State := initState []

/-- Adding any cell `S` not read by time `τ` to the parent `{F}` leads to the highway. -/
def ParentOK (F : Pt) (τ : Nat) : Prop :=
  ∀ S, (∀ t, t ≤ τ → (run t (initState [F])).pos ≠ S) → ReachesP104 (initState [F, S])

def ParentsOK : Prop := ∀ F τ, FirstRead blankState F τ → ParentOK F τ

/-- The blank run's tail cutoff. -/
def blankT2 : Nat := blankHint.t1 + 104 * 40

def ConcreteParentsOK : Prop := ∀ F τ, FirstRead blankState F τ → τ < blankT2 → ParentOK F τ
def ChannelParentsOK : Prop := ∀ F τ, FirstRead blankState F τ → blankT2 ≤ τ → ParentOK F τ

theorem parentsOK_of (hc : ConcreteParentsOK) (hch : ChannelParentsOK) : ParentsOK := by
  intro F τ hF
  rcases Nat.lt_or_ge τ blankT2 with h | h
  · exact hc F τ hF h
  · exact hch F τ hF h

/-! ### Coupling before the first read -/

/-- Until the run from `P` visits `z`, adding `z` does not change positions. -/
theorem pos_add_unread_upto (P : List Pt) (z : Pt) (T : Nat)
    (hz : ∀ t, t < T → (run t (initState P)).pos ≠ z) :
    ∀ t, t ≤ T → (run t (initState (P ++ [z]))).pos = (run t (initState P)).pos := by
  have h0 : Agree (fun w => w ≠ z) Pt.zero (initState P) (initState (P ++ [z])) := by
    refine ⟨by simp [initState]; exact (Pt.add_zero _).symm, rfl, ?_⟩
    intro w hw
    simp only [initState, Pt.add_zero]
    apply bool_eq_of_iff
    rw [contains_iff, contains_iff]
    simp [hw]
  intro t ht
  have A := agree_run t h0 (fun j hj => hz j (by omega))
  rw [A.1, Pt.add_zero]

theorem initState_perm2 (a b : Pt) : initState [a, b] = initState [b, a] := by
  simp only [initState]
  congr 1
  funext z
  simp only [List.contains_cons, List.contains_nil, Bool.or_false]
  cases (z == a) <;> cases (z == b) <;> rfl

theorem initState_dup (a : Pt) : initState [a, a] = initState [a] := by
  simp only [initState]
  congr 1
  funext z
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_self]

/-- **Theorem A, canonical pose, from the parent hypothesis.** -/
theorem two_black_canonical (h : ParentsOK) : ∀ a b, ReachesP104 (initState [a, b]) := by
  intro a b
  by_cases hab : a = b
  · subst hab; rw [initState_dup]; exact one_black_canonical a
  -- reduce to a parent F read first and a second cell S not read by then
  have key : ∀ F S τ, FirstRead blankState F τ → (∀ t, t ≤ τ → (run t blankState).pos ≠ S) →
      ReachesP104 (initState [F, S]) := by
    intro F S τ hF hS
    apply h F τ hF S
    intro t ht
    have e := pos_add_unread_upto [] F τ (fun t' ht' => hF.2 t' ht') t ht
    simp only [List.nil_append] at e
    rw [e]
    exact hS t ht
  by_cases va : ∃ t, (run t blankState).pos = a
  · obtain ⟨τa, ha⟩ := firstRead_of_visit _ _ va
    by_cases vb : ∃ t, (run t blankState).pos = b
    · obtain ⟨τb, hb⟩ := firstRead_of_visit _ _ vb
      rcases Nat.lt_or_ge τa τb with hlt | hge
      · exact key a b τa ha (fun t ht e => hb.2 t (by omega) e)
      · have hne : τa ≠ τb := by
          intro e; subst e; exact hab (ha.1.symm.trans hb.1)
        rw [initState_perm2]
        exact key b a τb hb (fun t ht e => ha.2 t (by omega) e)
    · exact key a b τa ha (fun t _ e => vb ⟨t, e⟩)
  · by_cases vb : ∃ t, (run t blankState).pos = b
    · obtain ⟨τb, hb⟩ := firstRead_of_visit _ _ vb
      rw [initState_perm2]
      exact key b a τb hb (fun t _ e => va ⟨t, e⟩)
    · -- neither cell is ever read: the run is the blank run
      have r1 : ReachesP104 (initState [a]) := by
        have := reaches_add_unread [] a (fun t e => va ⟨t, e⟩) blank_reaches
        simpa using this
      have hb' : ∀ t, (run t (initState [a])).pos ≠ b := by
        intro t e
        have := pos_add_unread_upto [] a (t + 1) (fun t' _ e' => va ⟨t', e'⟩) t (by omega)
        simp only [List.nil_append] at this
        rw [this] at e
        exact vb ⟨t, e⟩
      have := reaches_add_unread [a] b hb' r1
      simpa using this

/-! ### Any pose -/

def AtMostTwoBlack (s : State) : Prop :=
  ∃ L : List Pt, L.length ≤ 2 ∧ ∀ z, s.black z = L.contains z

/-- **Theorem A from the parent hypothesis.**  Every Langton's-ant state with at most two black cells,
at any ant position and heading, reaches the period-104 highway. -/
theorem two_black_of (h : ParentsOK) : ∀ s, AtMostTwoBlack s → ReachesP104 s := by
  intro s ⟨L, hL, hs⟩
  apply reaches_of_canonical s (initState (L.map (canonCell s))) rfl rfl
  · intro z
    simp only [initState, hs]
    apply bool_eq_of_iff
    rw [contains_iff, contains_iff, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have e : Pt.unrotN s.dir.toN (canonCell s q) + s.pos = q := by
        simp only [canonCell, Pt.unrotN_rotN]; apply Pt.ext' <;> simp <;> omega
      rw [e]; exact hq
    · intro hm
      refine ⟨_, hm, ?_⟩
      simp only [canonCell]
      rw [show Pt.unrotN s.dir.toN z + s.pos + -s.pos = Pt.unrotN s.dir.toN z by
        apply Pt.ext' <;> simp <;> omega, Pt.rotN_unrotN]
  · match L, hL with
    | [], _ => exact blank_reaches
    | [a], _ => exact one_black_canonical _
    | [a, b], _ => exact two_black_canonical h _ _

/-! ### The concrete parents: coverage of the blank run's first reads -/

/-- Walk the blank run for `k` updates from time `t`; at each first read, the next table entry must be
that cell, with divergence hint at most one past the read time. -/
def coverLoop : List PEntry → FState → HashSet Pt → Nat → Nat → Bool
  | _, _, _, _, 0 => true
  | tab, f, V, t, k + 1 =>
    if V.contains f.pos then coverLoop tab f.step V (t + 1) k
    else match tab with
      | [] => false
      | e :: tab' => (e.F == f.pos && decide (e.H.tdiv ≤ t + 1)) &&
          coverLoop tab' f.step (V.insert f.pos) (t + 1) k

theorem coverLoop_sound (x : State) : ∀ (k : Nat) (tab : List PEntry) (f : FState) (V : HashSet Pt) (t : Nat),
    coverLoop tab f V t k = true → f.toState = run t x →
    (∀ q, V.contains q = true ↔ ∃ t', t' < t ∧ (run t' x).pos = q) →
    ∀ F τ, FirstRead x F τ → t ≤ τ → τ < t + k → ∃ e ∈ tab, e.F = F ∧ e.H.tdiv ≤ τ + 1 := by
  intro k
  induction k with
  | zero => intro tab f V t _ _ _ F τ _ h1 h2; omega
  | succ k ih =>
    intro tab f V t h hf hV F τ hF h1 h2
    have hp : f.pos = (run t x).pos := by rw [← hf]; rfl
    have hfs : f.step.toState = run (t + 1) x := by rw [FState.step_toState, hf, run_succ]
    simp only [coverLoop] at h
    split at h
    · next hvis =>
      -- already visited: τ ≠ t
      have hτ : τ ≠ t := by
        intro e; subst e
        obtain ⟨t', ht', e'⟩ := (hV _).mp hvis
        rw [hp, hF.1] at e'
        exact hF.2 t' ht' e'
      have hV' : ∀ q, V.contains q = true ↔ ∃ t', t' < t + 1 ∧ (run t' x).pos = q := by
        intro q; rw [hV]
        constructor
        · rintro ⟨t', ht', e⟩; exact ⟨t', by omega, e⟩
        · rintro ⟨t', ht', e⟩
          rcases Nat.lt_or_ge t' t with hl | hg
          · exact ⟨t', hl, e⟩
          · have htt : t' = t := by omega
            rw [htt] at e
            exact (hV q).mp (by rw [← e, ← hp]; exact hvis)
      exact ih tab f.step V (t + 1) h hfs hV' F τ hF (by omega) (by omega)
    · next hvis =>
      split at h
      · simp at h
      · next e tab' =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨he, htd⟩, hrest⟩ := h
        rcases Nat.lt_or_ge τ (t + 1) with hl | hg
        · have : τ = t := by omega
          subst this
          refine ⟨e, List.mem_cons_self .., ?_, by omega⟩
          rw [he, hp, hF.1]
        · have hV' : ∀ q, (V.insert f.pos).contains q = true ↔ ∃ t', t' < t + 1 ∧ (run t' x).pos = q := by
            intro q
            rw [HashSet.contains_insert, Bool.or_eq_true, hV]
            constructor
            · rintro (e1 | ⟨t', ht', e1⟩)
              · refine ⟨t, by omega, ?_⟩; simp at e1; rw [← hp]; exact e1
              · exact ⟨t', by omega, e1⟩
            · rintro ⟨t', ht', e1⟩
              rcases Nat.lt_or_ge t' t with hl' | hg'
              · exact Or.inr ⟨t', hl', e1⟩
              · have htt : t' = t := by omega
                rw [htt] at e1
                left; simp; rw [hp]; exact e1
          obtain ⟨e', he', h3⟩ := ih tab' f.step (V.insert f.pos) (t + 1) hrest hfs hV' F τ hF hg (by omega)
          exact ⟨e', List.mem_cons_of_mem _ he', h3⟩

/-- The concrete parents follow from the table checks and the coverage pass. -/
theorem concrete_of_table (tab : List PEntry) (hok : tab.all PEntry.ok = true)
    (hcov : coverLoop tab (FState.init []) {} 0 blankT2 = true) : ConcreteParentsOK := by
  intro F τ hF hτ S hS
  have runX : ∀ t, run t blankState = (frun t (FState.init [])).toState := by
    intro t; rw [frun_toState, FState.init_toState]; rfl
  obtain ⟨e, he, hF', htd⟩ := coverLoop_sound blankState blankT2 tab (FState.init []) {} 0 hcov
    (by rw [runX]; rfl) (by intro q; simp) F τ hF (Nat.zero_le _) (by omega)
  have hc := List.all_eq_true.mp hok e he
  have := check0_sound [e.F] e.H e.fs hc S (fun t ht => by rw [hF']; exact hS t (by omega))
  rw [hF'] at this
  simpa using this

end TwoBlack
