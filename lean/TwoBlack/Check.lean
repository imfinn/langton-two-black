/-
  An executable checker for one-corridor families, and its soundness theorem.

  `check1 F H = true` is a finite computation on the run of member `H.n`, with hints `H` (zones, switch
  times, certificate data) that the checker verifies rather than trusts.  `check1_sound` turns it into
  the statement that every member `H.n + k` reaches the period-104 highway.
-/
import TwoBlack.Family
import Std.Data.HashSet.Lemmas

namespace TwoBlack
open Std

/-! ### A finite-support simulator -/

structure FState where
  black : HashSet Pt
  pos : Pt
  dir : Dir

def FState.toState (f : FState) : State := ⟨fun z => f.black.contains z, f.pos, f.dir⟩

@[simp] theorem FState.toState_pos (f : FState) : f.toState.pos = f.pos := rfl
@[simp] theorem FState.toState_dir (f : FState) : f.toState.dir = f.dir := rfl
@[simp] theorem FState.toState_black (f : FState) (z : Pt) : f.toState.black z = f.black.contains z := rfl

def FState.step (f : FState) : FState :=
  let c := f.black.contains f.pos
  let d := turn c f.dir
  ⟨if c then f.black.erase f.pos else f.black.insert f.pos, f.pos + d.vec, d⟩

theorem FState.step_toState (f : FState) : f.step.toState = TwoBlack.step f.toState := by
  simp only [FState.step, FState.toState, TwoBlack.step]
  congr 1
  funext z
  by_cases c : f.black.contains f.pos = true
  · simp only [c, if_true]
    rw [HashSet.contains_erase]
    by_cases e : z = f.pos
    · subst e; simp [c]
    · have e' : (f.pos == z) = false := by simp; exact fun h => e h.symm
      simp [e, e']
  · have c' : f.black.contains f.pos = false := by simpa using c
    simp only [c', Bool.false_eq_true, if_false]
    rw [HashSet.contains_insert]
    by_cases e : z = f.pos
    · subst e; simp [c']
    · have e' : (f.pos == z) = false := by simp; exact fun h => e h.symm
      simp [e, e']

def frun : Nat → FState → FState
  | 0, f => f
  | n + 1, f => frun n f.step

theorem frun_toState (n : Nat) (f : FState) : (frun n f).toState = run n f.toState := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [frun, ih, FState.step_toState, run_succ']

theorem frun_add (a b : Nat) (f : FState) : frun (a + b) f = frun b (frun a f) := by
  induction a generalizing f with
  | zero => simp [frun]
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega, frun, frun, ih]

def FState.init (cells : List Pt) : FState := ⟨HashSet.ofList cells, Pt.zero, Dir.N⟩

theorem FState.init_toState (cells : List Pt) : (FState.init cells).toState = initState cells := by
  simp only [FState.init, FState.toState, initState]
  congr 1
  funext z
  exact HashSet.contains_ofList

/-! ### Boolean building blocks and their soundness -/

def stdDriftB (u : Pt) : Bool :=
  u == ⟨-2, -2⟩ || u == ⟨2, -2⟩ || u == ⟨2, 2⟩ || u == ⟨-2, 2⟩

theorem stdDriftB_sound {u : Pt} (h : stdDriftB u = true) : StdDrift u := by
  simp [stdDriftB] at h
  unfold StdDrift
  rcases h with ((h | h) | h) | h <;> simp [h]

/-- Check `∀ z, P z → B'(z + τ) = B(z)` using only the finitely many black cells. -/
def agreeB (P : Pt → Bool) (τ : Pt) (B B' : HashSet Pt) : Bool :=
  B.toList.all (fun z => !P z || B'.contains (z + τ)) &&
  B'.toList.all (fun w => !P (w - τ) || B.contains (w - τ))

theorem agreeB_sound {P : Pt → Bool} {τ : Pt} {B B' : HashSet Pt} (h : agreeB P τ B B' = true) :
    ∀ z, P z = true → B'.contains (z + τ) = B.contains z := by
  simp only [agreeB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  intro z hz
  apply bool_eq_of_iff
  constructor
  · intro hw
    have hm : z + τ ∈ B'.toList := HashSet.mem_toList.mpr (HashSet.contains_iff_mem.mp hw)
    have := h2 _ hm
    rw [Pt.add_sub_cancel] at this
    simp [hz] at this
    exact this
  · intro hb
    have hm : z ∈ B.toList := HashSet.mem_toList.mpr (HashSet.contains_iff_mem.mp hb)
    have := h1 _ hm
    simp [hz] at this
    exact this

/-- `P` holds at the positions of the next `k` updates from `f`. -/
def readsB (P : Pt → Bool) : FState → Nat → Bool
  | _, 0 => true
  | f, k + 1 => P f.pos && readsB P f.step k

theorem readsB_sound {P : Pt → Bool} {f : FState} {k : Nat} (h : readsB P f k = true) :
    ∀ j, j < k → P (frun j f).pos = true := by
  induction k generalizing f with
  | zero => intro j hj; omega
  | succ k ih =>
    simp only [readsB, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j => rw [frun]; exact ih h.2 j (by omega)

/-! ### The checker -/

/-- Hints for a one-corridor family: base member, zones, switch times, certificate. -/
structure Hint1 where
  n : Nat
  D : Int
  C : Int
  ms : List Nat
  s : Nat
  u : Pt
  A : Int
deriving Repr

def Hint1.cd (H : Hint1) (F : Fam1) : CorridorData :=
  { δ := F.δ, D := H.D, C := H.C, J := H.ms.length, m := fun j => H.ms.getD (j - 1) 0 }

def inIntB (cd : CorridorData) (q t : Nat) : Bool :=
  decide (cd.start q ≤ t) && (!(decide (q < cd.J)) || decide (t < cd.m (q + 1) + 104))

def boundB (cd : CorridorData) (q : Nat) (p : Pt) : Bool :=
  if q % 2 = 0 then decide (cd.δ.phi p < cd.C - 16) else decide (cd.δ.phi p > cd.D + 16)

def c4okB (cd : CorridorData) (t : Nat) (p : Pt) : Bool :=
  (List.range (cd.J + 1)).all (fun q => !(inIntB cd q t) || boundB cd q p)

def c4loopB (cd : CorridorData) : FState → Nat → Nat → Bool
  | _, _, 0 => true
  | f, t, k + 1 => c4okB cd t f.pos && c4loopB cd f.step (t + 1) k

theorem c4loopB_sound {cd : CorridorData} {f : FState} {t k : Nat} (h : c4loopB cd f t k = true) :
    ∀ j, j < k → c4okB cd (t + j) (frun j f).pos = true := by
  induction k generalizing f t with
  | zero => intro j hj; omega
  | succ k ih =>
    simp only [c4loopB, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j => rw [frun, show t + (j + 1) = (t + 1) + j by omega]; exact ih h.2 j (by omega)

def switchB (cd : CorridorData) (f0 : FState) (j : Nat) : Bool :=
  let S := frun (cd.m j) f0
  let S' := frun 104 S
  let sv := cd.sv j
  S'.pos == S.pos + sv && S'.dir == S.dir &&
  agreeB (fun z => decide (cd.D + 8 < cd.δ.phi (z + sv)) && decide (cd.δ.phi (z + sv) < cd.C - 8))
    sv S.black S'.black

def check1 (F : Fam1) (H : Hint1) : Bool :=
  let cd := H.cd F
  let f0 := FState.init (F.cells H.n)
  let Sc := frun H.s f0
  let Sc' := frun 104 Sc
  let G : Pt → Bool := fun z => decide (dot H.u z > H.A)
  decide (cd.D + 40 < cd.C) &&
  (List.range cd.J).all (fun i => i == 0 || decide (cd.m i + 104 < cd.m (i + 1))) &&
  F.far.all (fun b => decide (F.δ.phi (b + Pt.smul (H.n : Int) F.δ.v) ≥ cd.C - 4)) &&
  F.near.all (fun b => decide (F.δ.phi b < cd.C - 16)) &&
  decide (cd.start cd.J ≤ H.s) &&
  (if cd.J % 2 = 0 then decide (F.δ.phi H.u ≤ 0) else decide (F.δ.phi H.u ≥ 0)) &&
  (List.range cd.J).all (fun i => switchB cd f0 (i + 1)) &&
  c4loopB cd f0 0 (H.s + 104) &&
  stdDriftB H.u &&
  (Sc'.pos == Sc.pos + H.u) && (Sc'.dir == Sc.dir) &&
  agreeB G H.u Sc.black Sc'.black &&
  readsB G Sc 104

/-! ### Soundness -/

theorem phi_std (δ : Diag) {u : Pt} (hu : StdDrift u) :
    δ.phi u = 4 ∨ δ.phi u = 0 ∨ δ.phi u = -4 := by
  rcases hu with h | h | h | h <;> subst h <;> cases δ <;> simp [Diag.phi]

theorem m_mono (cd : CorridorData) (gap : ∀ j, 1 ≤ j → j < cd.J → cd.m j + 104 < cd.m (j + 1)) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ cd.J → cd.m i ≤ cd.m j := by
  intro i j hi hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases e : i = j + 1
    · subst e; omega
    · have := ih (by omega) (by omega)
      have := gap j (by omega) (by omega)
      omega

/-- The mathematical core of the soundness proof: the checked facts, stated as propositions about the
run of member `n`, imply that every member `n + k` reaches the highway. -/
theorem fam1_core (F : Fam1) (cd : CorridorData) (hδ : cd.δ = F.δ) (n s : Nat) (u : Pt) (A : Int)
    (hDC : cd.D + 40 < cd.C)
    (gap : ∀ j, 1 ≤ j → j < cd.J → cd.m j + 104 < cd.m (j + 1))
    (hfar : ∀ b ∈ F.far, F.δ.phi (b + Pt.smul (n : Int) F.δ.v) ≥ cd.C - 4)
    (hnear : ∀ b ∈ F.near, F.δ.phi b < cd.C - 16)
    (hsJ : cd.start cd.J ≤ s)
    (hsign : (cd.J % 2 = 0 → F.δ.phi u ≤ 0) ∧ (cd.J % 2 = 1 → F.δ.phi u ≥ 0))
    (hsw : ∀ j, 1 ≤ j → j ≤ cd.J →
      (run (cd.m j + 104) (initState (F.cells n))).pos = (run (cd.m j) (initState (F.cells n))).pos + cd.sv j ∧
      (run (cd.m j + 104) (initState (F.cells n))).dir = (run (cd.m j) (initState (F.cells n))).dir ∧
      ∀ w, cd.D + 8 < cd.δ.phi w → cd.δ.phi w < cd.C - 8 →
        (run (cd.m j + 104) (initState (F.cells n))).black w =
          (run (cd.m j) (initState (F.cells n))).black (w - cd.sv j))
    (hc4 : ∀ q, q ≤ cd.J → ∀ t, t < s + 104 → cd.InInt q t →
      (q % 2 = 0 → cd.δ.phi (run t (initState (F.cells n))).pos < cd.C - 16) ∧
      (q % 2 = 1 → cd.δ.phi (run t (initState (F.cells n))).pos > cd.D + 16))
    (hu : StdDrift u)
    (hag : Agree (fun z => dot u z > A) u (run s (initState (F.cells n))) (run (s + 104) (initState (F.cells n))))
    (hin : ∀ j, j < 104 → dot u (run (s + j) (initState (F.cells n))).pos > A) :
    ∀ k, ReachesP104 (initState (F.cells (n + k))) := by
  let X : Nat → State := fun k => initState (F.cells (n + k))
  have reach0 : ReachesP104 (initState (F.cells n)) :=
    reaches_of_certificate (initState (F.cells n)) s u A hu hag hin
  have per := halfplane_obs (initState (F.cells n)) (fun z => dot u z > A) u s 104 (by decide)
    (fun z hz => stdDrift_dot_pos hu z A hz) hag hin
  have c4 : ∀ q, q ≤ cd.J → ∀ t, cd.InInt q t →
      (q % 2 = 0 → cd.δ.phi (run t (initState (F.cells n))).pos < cd.C - 16) ∧
      (q % 2 = 1 → cd.δ.phi (run t (initState (F.cells n))).pos > cd.D + 16) := by
    intro q hq t hI
    by_cases ht : t < s + 104
    · exact hc4 q hq t ht hI
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
      have hp : (run (s + c * 104 + j) (initState (F.cells n))).pos =
          (run (s + j) (initState (F.cells n))).pos + Pt.smul (c : Int) u := by
        have := congrArg Obs.pos (per c j)
        simpa [observe, Obs.shift] using this
      have hI' : cd.InInt cd.J (s + j) := ⟨by omega, fun h => absurd h (Nat.lt_irrefl _)⟩
      have base := hc4 cd.J (Nat.le_refl _) (s + j) (by omega) hI'
      rw [hp, Diag.phi_add, Diag.phi_smul]
      rw [hδ] at base ⊢
      constructor
      · intro hpar
        have hb := base.1 hpar
        have hs := hsign.1 hpar
        rcases phi_std F.δ hu with e | e | e <;> rw [e] at hs ⊢ <;> omega
      · intro hpar
        have hb := base.2 hpar
        have hs := hsign.2 hpar
        rcases phi_std F.δ hu with e | e | e <;> rw [e] at hs ⊢ <;> omega
  have hinit := fam_init F n cd.C hfar hnear
  have H0 : CorridorHyp cd (X 0) (X 1) := by
    refine ⟨hDC, gap, fun j h1 h2 => (hsw j h1 h2).1, fun j h1 h2 => (hsw j h1 h2).2.1,
      fun j h1 h2 => (hsw j h1 h2).2.2, c4, ?_⟩
    have := hinit 0
    simp only [Nat.add_zero, Int.natCast_zero, Int.mul_zero, Int.add_zero] at this
    rw [hδ]
    exact this
  intro k
  apply corridor_family cd X H0 _ reach0 k
  intro k
  have := hinit (k + 1)
  rw [hδ]
  rw [show n + (k + 1) + 1 = n + (k + 2) by omega] at this
  push_cast at this ⊢
  exact this

theorem check1_sound (F : Fam1) (H : Hint1) (hc : check1 F H = true) :
    ∀ k, ReachesP104 (initState (F.cells (H.n + k))) := by
  simp only [check1, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDC, hgap⟩, hfar⟩, hnear⟩, hsJ⟩, hsign⟩, hsw⟩, hc4⟩, hstd⟩, hcpos⟩, hcdir⟩, hcag⟩,
    hreads⟩ := hc
  have runX : ∀ t, run t (initState (F.cells H.n)) = (frun t (FState.init (F.cells H.n))).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  apply fam1_core F (H.cd F) rfl H.n H.s H.u H.A hDC
  · intro j hj1 hj2
    have := hgap j (List.mem_range.mpr hj2)
    simp at this
    rcases this with h | h
    · omega
    · exact h
  · exact hfar
  · exact hnear
  · exact hsJ
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
  · exact stdDriftB_sound hstd
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

end TwoBlack
