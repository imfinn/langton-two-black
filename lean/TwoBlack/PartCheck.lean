/-
  Lemma 6.3 for the channel parents, part 2: an executable check on the base member and its
  soundness theorem `checkPart_sound : checkPart F H P ks = true → ChildPartition1 F 40 ks`.

  The check runs member 40 once.  It verifies the parent's corridor hypotheses (`check1`), the facts the
  one-step lemma needs (block first read between the switches, periodicity of the returning transit),
  the tail margin for Lemma 6.1, and, for every cell first read after the block, that the child the
  partition prescribes is in the list `ks`:

  * φ S ≤ D + 12: the cell stays put — child `fixedKid` (one parameter);
  * D + 12 < φ S ≤ D + 16: a split representative — child `splitKid` (two parameters);
  * φ S > D + 16: the cell moves with the block — child `movingKid` (one parameter);
  * cells first read in the tail window also get a tail child (two parameters).
-/
import TwoBlack.Step

namespace TwoBlack
open Std

/-! ### The facts behind `check1` -/

/-- The hypotheses of `fam1_core`, as one structure. -/
structure Fam1Facts (F : Fam1) (cd : CorridorData) (n s : Nat) (u : Pt) (A : Int) : Prop where
  hδ : cd.δ = F.δ
  hDC : cd.D + 40 < cd.C
  gap : ∀ j, 1 ≤ j → j < cd.J → cd.m j + 104 < cd.m (j + 1)
  hfar : ∀ b ∈ F.far, F.δ.phi (b + Pt.smul (n : Int) F.δ.v) ≥ cd.C - 4
  hnear : ∀ b ∈ F.near, F.δ.phi b < cd.C - 16
  hsJ : cd.start cd.J ≤ s
  hsign : (cd.J % 2 = 0 → F.δ.phi u ≤ 0) ∧ (cd.J % 2 = 1 → F.δ.phi u ≥ 0)
  hsw : ∀ j, 1 ≤ j → j ≤ cd.J →
      (run (cd.m j + 104) (initState (F.cells n))).pos = (run (cd.m j) (initState (F.cells n))).pos + cd.sv j ∧
      (run (cd.m j + 104) (initState (F.cells n))).dir = (run (cd.m j) (initState (F.cells n))).dir ∧
      ∀ w, cd.D + 8 < cd.δ.phi w → cd.δ.phi w < cd.C - 8 →
        (run (cd.m j + 104) (initState (F.cells n))).black w =
          (run (cd.m j) (initState (F.cells n))).black (w - cd.sv j)
  hc4 : ∀ q, q ≤ cd.J → ∀ t, t < s + 104 → cd.InInt q t →
      (q % 2 = 0 → cd.δ.phi (run t (initState (F.cells n))).pos < cd.C - 16) ∧
      (q % 2 = 1 → cd.δ.phi (run t (initState (F.cells n))).pos > cd.D + 16)
  hu : StdDrift u
  hag : Agree (fun z => dot u z > A) u (run s (initState (F.cells n))) (run (s + 104) (initState (F.cells n)))
  hin : ∀ j, j < 104 → dot u (run (s + j) (initState (F.cells n))).pos > A

theorem check1_facts (F : Fam1) (H : Hint1) (hc : check1 F H = true) :
    Fam1Facts F (H.cd F) H.n H.s H.u H.A := by
  simp only [check1, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDC, hgap⟩, hfar⟩, hnear⟩, hsJ⟩, hsign⟩, hsw⟩, hc4⟩, hstd⟩, hcpos⟩, hcdir⟩, hcag⟩,
    hreads⟩ := hc
  have runX : ∀ t, run t (initState (F.cells H.n)) = (frun t (FState.init (F.cells H.n))).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  refine ⟨rfl, hDC, ?_, hfar, hnear, hsJ, ?_, ?_, ?_, stdDriftB_sound hstd, ?_, ?_⟩
  · intro j hj1 hj2
    have := hgap j (List.mem_range.mpr hj2)
    simp at this
    rcases this with h | h
    · omega
    · exact h
  · constructor
    · intro he; simp [he] at hsign; exact hsign
    · intro he; have : ¬ ((H.cd F).J % 2 = 0) := by omega
      simp [this] at hsign; exact hsign
  · intro j hj1 hj2
    have h := hsw (j - 1) (List.mem_range.mpr (by omega))
    rw [show j - 1 + 1 = j by omega] at h
    simp only [switchB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hp, hd⟩, ha⟩ := h
    rw [runX, runX, frun_add, FState.toState_pos, FState.toState_pos, FState.toState_dir, FState.toState_dir]
    refine ⟨hp, hd, ?_⟩
    intro w hw1 hw2
    rw [FState.toState_black, FState.toState_black]
    have := agreeB_sound ha (w - (H.cd F).sv j) (by simp [Pt.sub_add_cancel]; exact ⟨hw1, hw2⟩)
    rw [Pt.sub_add_cancel] at this
    exact this
  · intro q hq t ht hI
    have h1 := c4loopB_sound hc4 t ht
    simp only [Nat.zero_add, c4okB, List.all_eq_true, List.mem_range] at h1
    have h2 := h1 q (by omega)
    have hib : inIntB (H.cd F) q t = true := by
      simp only [inIntB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      refine ⟨hI.1, ?_⟩
      by_cases hqJ : q < (H.cd F).J
      · exact Or.inr (hI.2 hqJ)
      · exact Or.inl hqJ
    simp only [hib, Bool.not_true, Bool.false_or, boundB] at h2
    rw [runX]
    constructor
    · intro he; simp [he] at h2; exact h2
    · intro he; have : ¬ (q % 2 = 0) := by omega
      simp [this] at h2; exact h2
  · rw [runX, runX, frun_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [FState.toState_pos, FState.toState_pos]; exact hcpos
    · rw [FState.toState_dir, FState.toState_dir]; exact hcdir
    · intro z hz
      rw [FState.toState_black, FState.toState_black]
      exact agreeB_sound hcag z (by simp at hz ⊢; exact hz)
  · intro j hj
    rw [runX, frun_add]
    have := readsB_sound hreads j hj
    simp at this
    exact this

namespace Fam1Facts
variable {F : Fam1} {cd : CorridorData} {n s : Nat} {u : Pt} {A : Int}

/-- The certified highway: positions are periodic after `s` with drift `u`. -/
theorem periodic (h : Fam1Facts F cd n s u A) : PeriodicAfter (initState (F.cells n)) s u := by
  have per := halfplane_obs (initState (F.cells n)) (fun z => dot u z > A) u s 104 (by decide)
    (fun z hz => stdDrift_dot_pos h.hu z A hz) h.hag h.hin
  intro t ht
  obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = s + c * 104 + j :=
    ⟨(t - s) / 104, (t - s) % 104, Nat.mod_lt _ (by decide), by omega⟩
  have e1 := congrArg Obs.pos (per (c + 1) j)
  have e2 := congrArg Obs.pos (per c j)
  simp [observe, Obs.shift] at e1 e2
  rw [show s + c * 104 + j + 104 = s + (c + 1) * 104 + j by rw [Nat.succ_mul]; omega, e1, e2]
  apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega

/-- (C4) on the whole run, not only up to the certificate. -/
theorem c4_all (h : Fam1Facts F cd n s u A) : ∀ q, q ≤ cd.J → ∀ t, cd.InInt q t →
    (q % 2 = 0 → cd.δ.phi (run t (initState (F.cells n))).pos < cd.C - 16) ∧
    (q % 2 = 1 → cd.δ.phi (run t (initState (F.cells n))).pos > cd.D + 16) := by
  have per := h.periodic
  intro q hq t hI
  by_cases ht : t < s + 104
  · exact h.hc4 q hq t ht hI
  · have hqJ : q = cd.J := by
      rcases Nat.lt_or_ge q cd.J with hlt | hge
      · exfalso
        have h2 := hI.2 hlt
        have hmono := m_mono cd h.gap (q + 1) cd.J (by omega) (by omega) (Nat.le_refl _)
        have hsJ' : cd.m cd.J ≤ s := by
          have := h.hsJ; unfold CorridorData.start at this; split at this
          · omega
          · exact this
        omega
      · omega
    subst hqJ
    obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = s + j + c * 104 :=
      ⟨(t - s) / 104, (t - s) % 104, Nat.mod_lt _ (by decide), by omega⟩
    have hp := periodicAfter_iter per c (s + j) (by omega)
    have hI' : cd.InInt cd.J (s + j) := ⟨by have := h.hsJ; omega, fun h => absurd h (Nat.lt_irrefl _)⟩
    have base := h.hc4 cd.J (Nat.le_refl _) (s + j) (by omega) hI'
    rw [hp, Diag.phi_add, Diag.phi_smul]
    rw [h.hδ] at base ⊢
    constructor
    · intro hpar
      have hb := base.1 hpar
      have hs := h.hsign.1 hpar
      rcases phi_std F.δ h.hu with e | e | e <;> rw [e] at hs ⊢ <;> omega
    · intro hpar
      have hb := base.2 hpar
      have hs := h.hsign.2 hpar
      rcases phi_std F.δ h.hu with e | e | e <;> rw [e] at hs ⊢ <;> omega

/-- The corridor hypotheses for every pair of consecutive members. -/
theorem hyps (h : Fam1Facts F cd n s u A) :
    ∀ k, CorridorHyp (cd.iter k) (initState (F.cells (n + k))) (initState (F.cells (n + (k + 1)))) := by
  have hinit := fam_init F n cd.C h.hfar h.hnear
  have H0 : CorridorHyp cd (initState (F.cells n)) (initState (F.cells (n + 1))) := by
    refine ⟨h.hDC, h.gap, fun j h1 h2 => (h.hsw j h1 h2).1, fun j h1 h2 => (h.hsw j h1 h2).2.1,
      fun j h1 h2 => (h.hsw j h1 h2).2.2, h.c4_all, ?_⟩
    have := hinit 0
    simp only [Nat.add_zero, Int.natCast_zero, Int.mul_zero, Int.add_zero] at this
    rw [h.hδ]
    exact this
  intro k
  induction k with
  | zero => exact H0
  | succ k ih =>
    apply corridor_succ (cd.iter k) _ _ _ ih
    rw [CorridorData.iter_δ, CorridorData.iter_C, h.hδ]
    have := hinit (k + 1)
    rw [show n + (k + 1) + 1 = n + (k + 1 + 1) by omega] at this
    rw [show cd.C + 4 * (k : Int) + 4 = cd.C + 4 * ((k + 1 : Nat) : Int) by push_cast; omega]
    exact this

end Fam1Facts

/-! ### The children the partition prescribes -/

/-- The new cell stays put (one parameter). -/
def fixedKid (F : Fam1) (z0 S : Pt) : FamD × List Nat := (toFamD ⟨F.δ, [S], [z0]⟩, [40])
/-- The new cell moves with the block (one parameter). -/
def movingKid (F : Fam1) (z0 S : Pt) : FamD × List Nat :=
  (toFamD ⟨F.δ, [], [z0, S - Pt.smul 40 F.δ.v]⟩, [40])
/-- The corridor is split at the new cell, a representative at index 10 (two parameters). -/
def splitKid (F : Fam1) (z0 S : Pt) : FamD × List Nat :=
  (⟨[F.δ, F.δ], [(z0, [0, 1]), (S - Pt.smul 10 F.δ.v, [0])]⟩, [10, 30])
/-- A new corridor along the tail, beyond the moving frame (two parameters). -/
def movingTail (F : Fam1) (du : Diag) (z0 S : Pt) : FamD × List Nat :=
  (⟨[F.δ, du], [(z0, [0]), (S - Pt.smul 40 F.δ.v, [0, 1])]⟩, [40, 40])
/-- A new corridor along the tail, in the fixed frame (two parameters). -/
def fixedTail (F : Fam1) (du : Diag) (z0 S : Pt) : FamD × List Nat :=
  (⟨[F.δ, du], [(z0, [0]), (S, [1])]⟩, [40, 40])

def kidOK (F : Fam1) (D : Int) (z0 : Pt) (ks : List (FamD × List Nat)) (S : Pt) : Bool :=
  if F.δ.phi S ≤ D + 12 then decide (fixedKid F z0 S ∈ ks)
  else if F.δ.phi S ≤ D + 16 then decide (splitKid F z0 S ∈ ks)
  else decide (movingKid F z0 S ∈ ks)

def tailOK (F : Fam1) (D : Int) (du : Diag) (z0 : Pt) (ks : List (FamD × List Nat)) (S : Pt) : Bool :=
  (decide (F.δ.phi S > D + 16) && decide (F.δ.phi du.v ≥ 0) && decide (movingTail F du z0 S ∈ ks)) ||
  (decide (F.δ.phi S ≤ D + 12) && decide (F.δ.phi du.v ≤ 0) && decide (fixedTail F du z0 S ∈ ks))

theorem cells_fixedKid (F : Fam1) (z0 S : Pt) (m : Nat) :
    (fixedKid F z0 S).1.cells [m] = [S, z0 + Pt.smul (m : Int) F.δ.v] := by
  simp [fixedKid, toFamD_cells, Fam1.cells]

theorem cells_movingKid (F : Fam1) (z0 S : Pt) (m : Nat) :
    (movingKid F z0 S).1.cells [m] =
      [z0 + Pt.smul (m : Int) F.δ.v, S - Pt.smul 40 F.δ.v + Pt.smul (m : Int) F.δ.v] := by
  simp [movingKid, toFamD_cells, Fam1.cells]

theorem cells_splitKid (F : Fam1) (z0 S : Pt) (a c : Nat) :
    (splitKid F z0 S).1.cells [a, c] =
      [z0 + Pt.smul (a : Int) F.δ.v + Pt.smul (c : Int) F.δ.v, S - Pt.smul 10 F.δ.v + Pt.smul (a : Int) F.δ.v] := by
  simp [splitKid, FamD.cells, FamD.cell, List.foldl]

theorem cells_movingTail (F : Fam1) (du : Diag) (z0 S : Pt) (a c : Nat) :
    (movingTail F du z0 S).1.cells [a, c] =
      [z0 + Pt.smul (a : Int) F.δ.v, S - Pt.smul 40 F.δ.v + Pt.smul (a : Int) F.δ.v + Pt.smul (c : Int) du.v] := by
  simp [movingTail, FamD.cells, FamD.cell, List.foldl]

theorem cells_fixedTail (F : Fam1) (du : Diag) (z0 S : Pt) (a c : Nat) :
    (fixedTail F du z0 S).1.cells [a, c] = [z0 + Pt.smul (a : Int) F.δ.v, S + Pt.smul (c : Int) du.v] := by
  simp [fixedTail, FamD.cells, FamD.cell, List.foldl]

theorem sameCells_pair {a b a' b' : Pt} (h1 : a = a') (h2 : b = b') : SameCells [a, b] [a', b'] := by
  subst h1; subst h2; intro z; rfl

theorem sameCells_swap (a b : Pt) : SameCells [a, b] [b, a] := by
  intro z
  simp only [List.contains_cons, List.contains_nil, Bool.or_false]
  cases (z == a) <;> cases (z == b) <;> rfl

/-! ### Loops -/

/-- `P (pos f_i) → pos g_i + w = pos f_i` for the next `k` steps of two runs. -/
def perLoop (P : Pt → Bool) (w : Pt) : FState → FState → Nat → Bool
  | _, _, 0 => true
  | f, g, k + 1 => (!P f.pos || g.pos + w == f.pos) && perLoop P w f.step g.step k

theorem perLoop_sound {P : Pt → Bool} {w : Pt} : ∀ (k : Nat) (f g : FState), perLoop P w f g k = true →
    ∀ i, i < k → P (frun i f).pos = true → (frun i g).pos + w = (frun i f).pos := by
  intro k
  induction k with
  | zero => intro f g _ i hi; omega
  | succ k ih =>
    intro f g h i hi hp
    simp only [perLoop, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    cases i with
    | zero =>
      rcases h.1 with h1 | h1
      · simp [frun] at hp; rw [h1] at hp; exact absurd hp (by simp)
      · exact h1
    | succ i => simp only [frun]; exact ih f.step g.step h.2 i (by omega) hp

/-- One pass over the base member: the block is first read at `τ0`, and every cell first read after `τ0`
passes `kOK` (and `tOK` in the tail window). -/
def partLoop (b : Pt) (τ0 t1 : Nat) (kOK tOK : Pt → Bool) : FState → HashSet Pt → Nat → Nat → Bool
  | _, _, _, 0 => true
  | f, V, t, k + 1 =>
    let p := f.pos
    (if t < τ0 then p != b else if t = τ0 then p == b else
      (V.contains p || (kOK p && (!(decide (t1 ≤ t) && decide (t < t1 + 104)) || tOK p)))) &&
    partLoop b τ0 t1 kOK tOK f.step (V.insert p) (t + 1) k

theorem partLoop_sound (b : Pt) (τ0 t1 : Nat) (kOK tOK : Pt → Bool) (x : State) :
    ∀ (k : Nat) (f : FState) (V : HashSet Pt) (t : Nat),
    partLoop b τ0 t1 kOK tOK f V t k = true →
    f.toState = run t x →
    (∀ q, V.contains q = true ↔ ∃ t', t' < t ∧ (run t' x).pos = q) →
    ∀ τ, t ≤ τ → τ < t + k →
      ((τ < τ0 → (run τ x).pos ≠ b) ∧ (τ = τ0 → (run τ x).pos = b)) ∧
      (∀ z, FirstRead x z τ → τ0 < τ → kOK z = true ∧ (t1 ≤ τ → τ < t1 + 104 → tOK z = true)) := by
  intro k
  induction k with
  | zero => intro f V t _ _ _ τ h1 h2; omega
  | succ k ih =>
    intro f V t h hf hV τ h1 h2
    simp only [partLoop, Bool.and_eq_true] at h
    obtain ⟨hnow, hrest⟩ := h
    have hfs : f.step.toState = run (t + 1) x := by rw [FState.step_toState, hf, run_succ]
    have hp : f.pos = (run t x).pos := by rw [← hf]; rfl
    have hV' : ∀ q, (V.insert f.pos).contains q = true ↔ ∃ t', t' < t + 1 ∧ (run t' x).pos = q := by
      intro q
      rw [HashSet.contains_insert, Bool.or_eq_true, hV]
      constructor
      · rintro (e | ⟨t', ht', e⟩)
        · refine ⟨t, by omega, ?_⟩; simp at e; rw [← hp]; exact e
        · exact ⟨t', by omega, e⟩
      · rintro ⟨t', ht', e⟩
        rcases Nat.lt_or_ge t' t with hlt | hge
        · exact Or.inr ⟨t', hlt, e⟩
        · have : t' = t := by omega
          subst this; left; simp; rw [hp]; exact e
    rcases Nat.lt_or_ge τ (t + 1) with hτ | hτ
    · have hτt : τ = t := by omega
      subst hτt
      refine ⟨⟨fun hlt => ?_, fun heq => ?_⟩, fun z hz hgt => ?_⟩
      · simp only [hlt, if_true, bne_iff_ne, ne_eq] at hnow
        rw [← hp]; exact hnow
      · subst heq
        simp at hnow
        rw [← hp]; exact hnow
      · have h1' : ¬ τ < τ0 := by omega
        have h2' : ¬ τ = τ0 := by omega
        simp only [h1', h2', if_false, Bool.or_eq_true, Bool.and_eq_true] at hnow
        have hpz : f.pos = z := by rw [hp]; exact hz.1
        have hnew : V.contains f.pos = false := by
          rcases Bool.eq_false_or_eq_true (V.contains f.pos) with hc | hc
          · exfalso
            obtain ⟨t', ht', e⟩ := (hV _).mp hc
            rw [hpz] at e
            exact hz.2 t' ht' e
          · exact hc
        rcases hnow with hc | ⟨hk, htl⟩
        · rw [hnew] at hc; exact absurd hc (by simp)
        · rw [hpz] at hk htl
          refine ⟨hk, fun hw1 hw2 => ?_⟩
          simpa [hw1, hw2] using htl
    · exact ih f.step (V.insert f.pos) (t + 1) hrest hfs hV' τ hτ (by omega)

/-! ### The check -/

/-- Hints for the partition check: the block's first read in member 40, the tail window start and
margin, and the tail drift as a diagonal. -/
structure PartHint where
  tau : Nat
  t1 : Nat
  psi : Int
  du : Diag
deriving Repr

def checkPart (F : Fam1) (H : Hint1) (P : PartHint) (ks : List (FamD × List Nat)) : Bool :=
  match F.far, F.near with
  | [z0], [] =>
    let cd := H.cd F
    let f0 := FState.init (F.cells 40)
    (F.δ == .mm) && (H.n == 40) && check1 F H &&
    (cd.J == 1 || cd.J == 2) &&
    decide (cd.m 1 + 104 ≤ P.tau) && (cd.J != 2 || decide (P.tau < cd.m 2)) &&
    decide (cd.D ≥ 19) && decide (P.tau < P.t1) && decide (H.s ≤ P.t1) && (P.du.v == H.u) &&
    (cd.J != 2 || (decide (cd.m 2 ≤ H.s) &&
      perLoop (fun z => decide (F.δ.phi z > cd.D + 16)) F.δ.v (frun (cd.m 2) f0) (frun (cd.m 2 + 104) f0)
        (H.s - cd.m 2) &&
      readsB (fun z => decide (F.δ.phi z ≤ cd.D + 16)) (frun H.s f0) 104)) &&
    readsB (fun z => decide (P.du.phi z ≤ P.psi)) f0 H.s &&
    readsB (fun z => decide (P.du.phi z > P.psi + 4)) (frun P.t1 f0) 104 &&
    partLoop (z0 + Pt.smul 40 F.δ.v) P.tau P.t1 (kidOK F cd.D z0 ks) (tailOK F cd.D P.du z0 ks) f0 {} 0
      (P.t1 + 104 * 40)
  | _, _ => false


/-! ### Soundness -/

theorem aboveBase1 {a m : Nat} (h : a ≤ m) : AboveBase [a] [m] := by
  refine ⟨rfl, fun i hi => ?_⟩
  cases i with
  | zero => simpa using h
  | succ i => simp at hi

theorem aboveBase2 {a b m n : Nat} (h1 : a ≤ m) (h2 : b ≤ n) : AboveBase [a, b] [m, n] := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => simpa using h1
  | 1, _ => simpa using h2

theorem phi_smul_nat (δ : Diag) (a : Pt) (S : Pt) (r : Nat) :
    δ.phi (S - Pt.smul (r : Int) a) = δ.phi S - (r : Int) * δ.phi a := by
  rw [Diag.phi_sub, Diag.phi_smul]

/-- **Lemma 6.3 for a one-corridor channel parent**, from the check on member 40. -/
theorem checkPart_sound (F : Fam1) (H : Hint1) (P : PartHint) (ks : List (FamD × List Nat))
    (hc : checkPart F H P ks = true) : ChildPartition1 F 40 ks := by
  intro z0 hf hn j hj τ hτ S hS
  unfold checkPart at hc
  rw [hf, hn] at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := hc
  have hδ : F.δ = Diag.mm := h1
  have hcdδ : (H.cd F).δ = F.δ := rfl
  have facts := check1_facts F H h3
  rw [h2] at facts
  have hcells : ∀ m : Nat, F.cells m = [z0 + Pt.smul (m : Int) F.δ.v] := by
    intro m; simp [Fam1.cells, hf, hn]
  let X : Nat → State := fun k => initState (F.cells (40 + k))
  let b : Nat → Pt := fun k => z0 + Pt.smul ((40 + k : Nat) : Int) F.δ.v
  have runX0 : ∀ t, (run t (initState (F.cells 40))).pos = (frun t (FState.init (F.cells 40))).pos := by
    intro t; rw [← FState.toState_pos, frun_toState, FState.init_toState]
  -- the pass over member 40
  have L := partLoop_sound (z0 + Pt.smul 40 F.δ.v) P.tau P.t1 (kidOK F (H.cd F).D z0 ks)
    (tailOK F (H.cd F).D P.du z0 ks) (initState (F.cells 40)) _ _ _ 0 h14
    (by rw [FState.init_toState]; rfl) (by intro q; simp)
  have first0 : FirstRead (X 0) (b 0) P.tau := by
    have e1 : X 0 = initState (F.cells 40) := rfl
    have e2 : b 0 = z0 + Pt.smul 40 F.δ.v := rfl
    rw [e1, e2]
    exact ⟨(L P.tau (by omega) (by omega)).1.2 rfl, fun t ht => (L t (by omega) (by omega)).1.1 ht⟩
  have hb : ∀ k, b (k + 1) = b k + (H.cd F).δ.v := by
    intro k
    show z0 + Pt.smul ((40 + (k + 1) : Nat) : Int) F.δ.v = z0 + Pt.smul ((40 + k : Nat) : Int) F.δ.v + F.δ.v
    apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
  have hb0 : (H.cd F).δ.phi (b 0) ≥ (H.cd F).C - 4 := facts.hfar z0 (by simp [hf])
  have hτ2 : (H.cd F).J = 2 → P.tau < (H.cd F).m 2 := by
    intro hJ2; rcases h6 with h | h
    · exact absurd hJ2 h
    · exact h
  -- the outgoing transit is the blank highway
  have hblank := blank_facts
  have perOut : ∀ k, FirstRead (X k) (b k) (P.tau + 104 * k) → ∀ t, t < ((H.cd F).iter k).m 1 →
      (H.cd F).δ.phi (run t (X k)).pos > (H.cd F).D + 12 →
      (run (t + 104) (X k)).pos = (run t (X k)).pos + (H.cd F).δ.v := by
    intro k hfk t ht hφ
    have hXk : X k = initState [b k] := by show initState (F.cells (40 + k)) = _; rw [hcells]
    rw [hXk] at hfk hφ ⊢
    have hm : ((H.cd F).iter k).m 1 = (H.cd F).m 1 + 104 * k := by rw [CorridorData.iter_m] <;> omega
    have e1 := pos_eq_blank_upto (b k) _ hfk t (by omega)
    have e2 := pos_eq_blank_upto (b k) _ hfk (t + 104) (by omega)
    rw [e1, e2]
    rw [e1] at hφ
    have hd : (H.cd F).δ = blankHint.δu := by rw [hcdδ, hδ]; rfl
    rw [hd] at hφ ⊢
    have hs : blankHint.s ≤ t := by
      rcases Nat.lt_or_ge t blankHint.s with hlt | hge
      · exfalso
        have := hblank.2 t hlt
        have : blankHint.ψ = 31 := rfl
        omega
      · exact hge
    exact hblank.1 t hs
  -- the returning transit is periodic
  have perRet0 : (H.cd F).J = 2 → ∀ t, (H.cd F).m 2 ≤ t →
      (H.cd F).δ.phi (run t (X 0)).pos > (H.cd F).D + 16 →
      (run (t + 104) (X 0)).pos + (H.cd F).δ.v = (run t (X 0)).pos := by
    intro hJ2 t ht hφ
    have hX0 : X 0 = initState (F.cells 40) := rfl
    rw [hX0] at hφ ⊢
    rcases h11 with h | ⟨⟨hm2s, hper⟩, hrd⟩
    · exact absurd hJ2 h
    rcases Nat.lt_or_ge t H.s with hlt | hge
    · have := perLoop_sound _ _ _ hper (t - (H.cd F).m 2) (by omega)
      rw [← frun_add, ← frun_add, show (H.cd F).m 2 + (t - (H.cd F).m 2) = t by omega,
        show (H.cd F).m 2 + 104 + (t - (H.cd F).m 2) = t + 104 by omega] at this
      rw [runX0, runX0]
      apply this
      rw [runX0] at hφ
      simpa using hφ
    · exfalso
      obtain ⟨c, w, hw, rfl⟩ : ∃ c w, w < 104 ∧ t = H.s + w + c * 104 :=
        ⟨(t - H.s) / 104, (t - H.s) % 104, Nat.mod_lt _ (by decide), by omega⟩
      have hp := periodicAfter_iter facts.periodic c (H.s + w) (by omega)
      rw [hp, Diag.phi_add, Diag.phi_smul] at hφ
      have hr := readsB_sound hrd w hw
      rw [← frun_add, ← runX0] at hr
      simp only [decide_eq_true_eq] at hr
      have hsg := facts.hsign.1 (by omega)
      rw [hcdδ] at hφ
      rcases phi_std F.δ facts.hu with e | e | e <;> rw [e] at hsg hφ <;> omega
  have hJ : (H.cd F).J = 1 ∨ (H.cd F).J = 2 := h4
  have HK := step_chain (H.cd F) X b P.tau facts.hyps hJ first0 h5 hτ2 hb hb0 perOut perRet0
  -- the member in question
  obtain ⟨k, rfl⟩ : ∃ k, j = 40 + k := ⟨j - 40, by omega⟩
  have hτeq : τ = P.tau + 104 * k := firstRead_unique hτ (HK k).first
  subst hτeq
  by_cases hv : ∃ t, (run t (initState (F.cells (40 + k)))).pos = S
  · right
    have hnew : NewAfter (X k) (P.tau + 104 * k) S := ⟨fun t ht => hS t ht, hv⟩
    obtain ⟨r, hr, hnew0, c1, c2⟩ := unroll (H.cd F) X b P.tau HK k S hnew
    rw [hcdδ] at hnew0 c1 c2
    have hX0 : X 0 = initState (F.cells 40) := rfl
    rw [hX0] at hnew0
    obtain ⟨tS, htS⟩ := firstRead_of_visit _ _ hnew0.2
    have htS_gt : P.tau < tS := by
      rcases Nat.lt_or_ge P.tau tS with h | h
      · exact h
      · exact absurd htS.1 (hnew0.1 tS h)
    have hcellsj : F.cells (40 + k) ++ [S] = [z0 + Pt.smul ((40 + k : Nat) : Int) F.δ.v, S] := by
      rw [hcells]; rfl
    rw [hcellsj]
    have hSr : S = (S - Pt.smul (r : Int) F.δ.v) + Pt.smul (r : Int) F.δ.v := (Pt.sub_add_cancel _ _).symm
    rcases Nat.lt_or_ge tS (P.t1 + 104 * 40) with hlt | hge
    · -- a cell first read before the tail cutoff
      have K := ((L tS (Nat.zero_le _) (by rw [Nat.zero_add]; exact hlt)).2 _ htS htS_gt).1
      unfold kidOK at K
      split at K
      · next hle =>
        have hr0 : r = 0 := by
          rcases Nat.eq_zero_or_pos r with h | h
          · exact h
          · have := c2 h; omega
        subst hr0
        refine ⟨_, of_decide_eq_true K, [40 + k], aboveBase1 (by omega), ?_⟩
        rw [cells_fixedKid]
        have e : S - Pt.smul ((0 : Nat) : Int) F.δ.v = S := by apply Pt.ext' <;> simp
        rw [e]
        exact sameCells_swap _ _
      · next hle =>
        split at K
        · next hle2 =>
          refine ⟨_, of_decide_eq_true K, [10 + r, 30 + k - r], aboveBase2 (by omega) (by omega), ?_⟩
          rw [cells_splitKid]
          apply sameCells_pair
          · rw [hδ]; apply Pt.ext' <;> simp [Diag.v] <;> omega
          · conv => rhs; rw [hSr]
            rw [hδ]; apply Pt.ext' <;> simp [Diag.v] <;> omega
        · next hle2 =>
          have hrk : r = k := by
            rcases Nat.lt_or_ge r k with h | h
            · have := c1 h; omega
            · omega
          subst hrk
          refine ⟨_, of_decide_eq_true K, [40 + r], aboveBase1 (by omega), ?_⟩
          rw [cells_movingKid]
          apply sameCells_pair rfl
          conv => rhs; rw [hSr]
          rw [hδ]; apply Pt.ext' <;> simp [Diag.v] <;> omega
    · -- deep in the tail: descend to the window (Lemma 6.1)
      have hper : PeriodicAfter (initState (F.cells 40)) H.s P.du.v := by rw [h10]; exact facts.periodic
      have hpre : ∀ t, t < H.s → P.du.phi (run t (initState (F.cells 40))).pos ≤ P.psi := by
        intro t ht
        have := readsB_sound h12 t ht
        rw [runX0]; simpa using this
      have hwin : ∀ i, i < 104 → P.du.phi (run (P.t1 + i) (initState (F.cells 40))).pos > P.psi + 4 := by
        intro i hi
        have := readsB_sound h13 i hi
        rw [runX0, frun_add]; simpa using this
      have hjt : 40 ≤ (tS - P.t1) / 104 := by omega
      have hD := descent (initState (F.cells 40)) P.du H.s P.t1 P.psi hper h9 hpre hwin ((tS - P.t1) / 104)
        _ tS htS (by omega)
      have hlo : P.t1 ≤ tS - 104 * ((tS - P.t1) / 104) := by omega
      have hhi : tS - 104 * ((tS - P.t1) / 104) < P.t1 + 104 := by omega
      have K := ((L (tS - 104 * ((tS - P.t1) / 104)) (Nat.zero_le _) (by rw [Nat.zero_add]; omega)).2 _ hD
        (by omega)).2 hlo hhi
      simp only [tailOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at K
      have hS0 : S - Pt.smul (r : Int) F.δ.v =
          (S - Pt.smul (r : Int) F.δ.v - Pt.smul (((tS - P.t1) / 104 : Nat) : Int) P.du.v) +
            Pt.smul (((tS - P.t1) / 104 : Nat) : Int) P.du.v := (Pt.sub_add_cancel _ _).symm
      have hφS0 : F.δ.phi (S - Pt.smul (r : Int) F.δ.v) =
          F.δ.phi (S - Pt.smul (r : Int) F.δ.v - Pt.smul (((tS - P.t1) / 104 : Nat) : Int) P.du.v) +
            (((tS - P.t1) / 104 : Nat) : Int) * F.δ.phi P.du.v := by
        conv => lhs; rw [hS0]
        rw [Diag.phi_add, Diag.phi_smul]
      rcases K with ⟨⟨hφ, hu⟩, hmem⟩ | ⟨⟨hφ, hu⟩, hmem⟩
      · -- the tail moves with the block
        have hrk : r = k := by
          rcases Nat.lt_or_ge r k with h | h
          · have := c1 h
            rcases phi_std F.δ (diag_std P.du) with e | e | e <;> rw [e] at hu hφS0 <;> omega
          · omega
        subst hrk
        refine ⟨_, hmem, [40 + r, (tS - P.t1) / 104], aboveBase2 (by omega) hjt, ?_⟩
        rw [cells_movingTail]
        apply sameCells_pair rfl
        conv => rhs; rw [hSr]
        rw [hδ]; apply Pt.ext' <;> simp [Diag.v] <;> omega
      · -- the tail stays put
        have hr0 : r = 0 := by
          rcases Nat.eq_zero_or_pos r with h | h
          · exact h
          · have := c2 h
            rcases phi_std F.δ (diag_std P.du) with e | e | e <;> rw [e] at hu hφS0 <;> omega
        subst hr0
        refine ⟨_, hmem, [40 + k, (tS - P.t1) / 104], aboveBase2 (by omega) hjt, ?_⟩
        rw [cells_fixedTail]
        apply sameCells_pair rfl
        rw [Pt.sub_add_cancel]
        apply Pt.ext' <;> simp
  · left
    intro t e
    exact hv ⟨t, e⟩


end TwoBlack
