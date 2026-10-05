/-
  Lemma 6.3 for the channel parents, part 1: the one-step image lemma.

  For a one-corridor family with one or two switches whose block is first read between the two
  switches, compare the new cells of member n (run from `x`) and member n + 1 (run from `x'`).  A new
  cell is a cell not read up to the block's first read, but read later.  With φ = δ.phi:

  * the block of member n + 1 is first read exactly 104 updates later (`step_first`);
  * a new cell S of member n + 1 with φ S ≤ D + 16 is a new cell of member n (`step_new`, near case);
  * a new cell S of member n + 1 with φ S > D + 16 gives the new cell S − v of member n (far case).

  Iterating (`unroll`): a new cell of member n + k is S₀ + r·v for a new cell S₀ of member n and
  some 0 ≤ r ≤ k, where r = k unless φ S₀ ≤ D + 16, and r = 0 unless φ S₀ > D + 12.
-/
import TwoBlack.Channels

namespace TwoBlack

/-! ### Iterated corridor data -/

@[simp] theorem CorridorData.iter_J (cd : CorridorData) (k : Nat) : (cd.iter k).J = cd.J := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [CorridorData.iter, CorridorData.succ, ih]

@[simp] theorem CorridorData.iter_D (cd : CorridorData) (k : Nat) : (cd.iter k).D = cd.D := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [CorridorData.iter, CorridorData.succ, ih]

theorem CorridorData.iter_m (cd : CorridorData) (k j : Nat) :
    (cd.iter k).m j = cd.m j + 104 * j * k := by
  induction k with
  | zero => simp [CorridorData.iter]
  | succ k ih =>
    simp only [CorridorData.iter, CorridorData.succ, ih]
    rw [Nat.mul_succ, Nat.add_assoc]

/-! ### Positions along the corridor -/

/-- The corridor lemma, positions only: on relation interval `q`, member n + 1 is member n delayed by
`104 q`, translated by `v` when `q` is odd. -/
theorem corridor_pos (cd : CorridorData) (x x' : State) (h : CorridorHyp cd x x') (q : Nat)
    (hq : q ≤ cd.J) (t : Nat) (h1 : cd.start q ≤ t) (h2 : q < cd.J → t ≤ cd.m (q + 1) + 104) :
    (run (t + 104 * q) x').pos = (run t x).pos + (if q % 2 = 0 then Pt.zero else cd.δ.v) := by
  have R := corridor cd x x' h q hq t h1 h2
  unfold Rq at R
  split at R
  · next he => rw [if_pos he]; exact R.1.1
  · next he => rw [if_neg he]; exact R.1.1

/-- A cell is new after `τ`: not read up to time `τ`, read at some time. -/
def NewAfter (x : State) (τ : Nat) (z : Pt) : Prop :=
  (∀ t, t ≤ τ → (run t x).pos ≠ z) ∧ ∃ t, (run t x).pos = z

/-- Hypotheses of the one-step lemma. -/
structure StepHyp (cd : CorridorData) (x x' : State) (b : Pt) (τ : Nat) : Prop where
  hyp : CorridorHyp cd x x'
  hJ : cd.J = 1 ∨ cd.J = 2
  first : FirstRead x b τ
  hτ1 : cd.m 1 + 104 ≤ τ
  hτ2 : cd.J = 2 → τ < cd.m 2
  hb : cd.δ.phi b ≥ cd.C - 4
  /-- the outgoing transit is periodic before the first switch, away from the near zone -/
  perOut : ∀ t, t < cd.m 1 → cd.δ.phi (run t x).pos > cd.D + 12 →
    (run (t + 104) x).pos = (run t x).pos + cd.δ.v
  /-- the returning transit is periodic after the second switch, away from the near zone -/
  perRet : cd.J = 2 → ∀ t, cd.m 2 ≤ t → cd.δ.phi (run t x).pos > cd.D + 16 →
    (run (t + 104) x).pos + cd.δ.v = (run t x).pos

namespace StepHyp
variable {cd : CorridorData} {x x' : State} {b : Pt} {τ : Nat}

theorem one_le_J (H : StepHyp cd x x' b τ) : 1 ≤ cd.J := by rcases H.hJ with h | h <;> omega

theorem pos0 (H : StepHyp cd x x' b τ) (t : Nat) (ht : t ≤ cd.m 1 + 104) :
    (run t x').pos = (run t x).pos := by
  have := corridor_pos cd x x' H.hyp 0 (Nat.zero_le _) t (by simp [CorridorData.start])
    (fun _ => by simpa using ht)
  simpa [Pt.add_zero] using this

theorem pos1 (H : StepHyp cd x x' b τ) (t : Nat) (h1 : cd.m 1 ≤ t) (h2 : cd.J = 2 → t ≤ cd.m 2 + 104) :
    (run (t + 104) x').pos = (run t x).pos + cd.δ.v := by
  have := corridor_pos cd x x' H.hyp 1 H.one_le_J t (by simpa [CorridorData.start] using h1)
    (fun hlt => h2 (by rcases H.hJ with h | h <;> omega))
  simpa using this

theorem pos2 (H : StepHyp cd x x' b τ) (hJ2 : cd.J = 2) (t : Nat) (h1 : cd.m 2 ≤ t) :
    (run (t + 208) x').pos = (run t x).pos := by
  have := corridor_pos cd x x' H.hyp 2 (by omega) t (by simpa [CorridorData.start] using h1)
    (fun hlt => by omega)
  simpa [Pt.add_zero] using this

theorem zone0 (H : StepHyp cd x x' b τ) (t : Nat) (ht : t < cd.m 1 + 104) :
    cd.δ.phi (run t x).pos < cd.C - 16 :=
  (H.hyp.c4 0 (Nat.zero_le _) t ⟨by simp [CorridorData.start], fun _ => by simpa using ht⟩).1 rfl

theorem zone1 (H : StepHyp cd x x' b τ) (t : Nat) (h1 : cd.m 1 ≤ t) (h2 : cd.J = 2 → t < cd.m 2 + 104) :
    cd.δ.phi (run t x).pos > cd.D + 16 :=
  (H.hyp.c4 1 H.one_le_J t ⟨by simpa [CorridorData.start] using h1,
    fun hlt => h2 (by rcases H.hJ with h | h <;> omega)⟩).2 rfl

/-- Every update of member n + 1 after the first window is an image of interval 1 or of interval 2. -/
theorem cover (H : StepHyp cd x x' b τ) (t' : Nat) (ht : cd.m 1 + 104 < t') :
    (∃ t, cd.m 1 ≤ t ∧ (cd.J = 2 → t < cd.m 2 + 104) ∧ t' = t + 104) ∨
    (cd.J = 2 ∧ ∃ t, cd.m 2 ≤ t ∧ t' = t + 208) := by
  rcases H.hJ with hJ | hJ
  · exact Or.inl ⟨t' - 104, by omega, fun h => by omega, by omega⟩
  · by_cases hlt : t' < cd.m 2 + 208
    · exact Or.inl ⟨t' - 104, by omega, fun _ => by omega, by omega⟩
    · exact Or.inr ⟨hJ, t' - 208, by omega, by omega⟩

/-- The block of member n + 1 is first read 104 updates later. -/
theorem step_first (H : StepHyp cd x x' b τ) : FirstRead x' (b + cd.δ.v) (τ + 104) := by
  have hτm := H.hτ1
  refine ⟨?_, fun t' ht' e => ?_⟩
  · rw [H.pos1 τ (by omega) (fun h => by have := H.hτ2 h; omega), H.first.1]
  · rcases Nat.lt_or_ge t' (cd.m 1 + 104) with hlt | hge
    · have z := H.zone0 t' hlt
      rw [← H.pos0 t' (by omega), e] at z
      have := H.hb
      simp at z
      omega
    · have hp := H.pos1 (t' - 104) (by omega) (fun h => by have := H.hτ2 h; omega)
      rw [show t' - 104 + 104 = t' by omega, e] at hp
      exact H.first.2 (t' - 104) (by omega) (Pt.add_right_cancel hp).symm

/-- **The one-step lemma.**  A new cell `S` of member n + 1 is a new cell of member n (near case), or
`S − v` is (far case). -/
theorem step_new (H : StepHyp cd x x' b τ) (S : Pt) (hS : NewAfter x' (τ + 104) S) :
    (cd.δ.phi S ≤ cd.D + 16 → NewAfter x τ S) ∧ (cd.δ.phi S > cd.D + 16 → NewAfter x τ (S - cd.δ.v)) := by
  obtain ⟨hnot, t', ht'⟩ := hS
  have hτm := H.hτ1
  have hlate : τ + 104 < t' := by
    rcases Nat.lt_or_ge (τ + 104) t' with h | h
    · exact h
    · exact absurd ht' (hnot t' h)
  have hτ2' : cd.J = 2 → τ < cd.m 2 := H.hτ2
  constructor
  · intro hnear
    refine ⟨fun t ht e => ?_, ?_⟩
    · rcases Nat.lt_or_ge t (cd.m 1) with hlt | hge
      · exact hnot t (by omega) (by rw [H.pos0 t (by omega)]; exact e)
      · have := H.zone1 t hge (fun h => by have := hτ2' h; omega)
        rw [e] at this; omega
    · rcases H.cover t' (by omega) with ⟨t, h1, h2, rfl⟩ | ⟨hJ2, t, h1, rfl⟩
      · have z := H.zone1 t h1 h2
        rw [H.pos1 t h1 (fun h => by have := h2 h; omega)] at ht'
        rw [← ht'] at hnear
        simp at hnear; omega
      · exact ⟨t, by rw [← H.pos2 hJ2 t h1]; exact ht'⟩
  · intro hfar
    refine ⟨fun t ht e => ?_, ?_⟩
    · rcases Nat.lt_or_ge t (cd.m 1) with hlt | hge
      · have hφ : cd.δ.phi (run t x).pos > cd.D + 12 := by rw [e]; simp; omega
        have hp := H.perOut t hlt hφ
        rw [e, Pt.sub_add_cancel] at hp
        exact hnot (t + 104) (by omega) (by rw [H.pos0 (t + 104) (by omega)]; exact hp)
      · have hp := H.pos1 t hge (fun h => by have := hτ2' h; omega)
        rw [e, Pt.sub_add_cancel] at hp
        exact hnot (t + 104) (by omega) hp
    · rcases H.cover t' (by omega) with ⟨t, h1, h2, rfl⟩ | ⟨hJ2, t, h1, rfl⟩
      · refine ⟨t, ?_⟩
        rw [H.pos1 t h1 (fun h => by have := h2 h; omega)] at ht'
        rw [← ht', Pt.add_sub_cancel]
      · rw [H.pos2 hJ2 t h1] at ht'
        have hp := H.perRet hJ2 t h1 (by rw [ht']; exact hfar)
        refine ⟨t + 104, ?_⟩
        rw [← ht', ← hp, Pt.add_sub_cancel]

end StepHyp

theorem firstRead_unique {x : State} {z : Pt} {a b : Nat} (ha : FirstRead x z a) (hb : FirstRead x z b) :
    a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd ha.1 (hb.2 a h)
  · exact h
  · exact absurd hb.1 (ha.2 b h)

/-! ### The whole family -/

theorem pts_smul_step (b0 v : Pt) (k : Nat) :
    b0 + Pt.smul ((k + 1 : Nat) : Int) v = b0 + Pt.smul (k : Int) v + v := by
  apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega

/-- The block positions of the members. -/
theorem block_pos (b : Nat → Pt) (v : Pt) (hb : ∀ k, b (k + 1) = b k + v) :
    ∀ k, b k = b 0 + Pt.smul (k : Int) v := by
  intro k
  induction k with
  | zero => apply Pt.ext' <;> simp
  | succ k ih => rw [hb, ih, pts_smul_step]

/-- Positions in the last relation interval of a two-switch corridor are the same for every member,
up to the delay `208 k`. -/
theorem posmap2 (cd : CorridorData) (X : Nat → State)
    (hyps : ∀ k, CorridorHyp (cd.iter k) (X k) (X (k + 1))) (hJ2 : cd.J = 2) :
    ∀ k t, cd.m 2 ≤ t → (run (t + 208 * k) (X k)).pos = (run t (X 0)).pos := by
  intro k
  induction k with
  | zero => intro t _; rfl
  | succ k ih =>
    intro t ht
    have hm : (cd.iter k).m 2 = cd.m 2 + 208 * k := by rw [CorridorData.iter_m] <;> omega
    have hs : (cd.iter k).start 2 = cd.m 2 + 208 * k := by simp [CorridorData.start, hm]
    have := corridor_pos (cd.iter k) (X k) (X (k + 1)) (hyps k) 2 (by simp [hJ2]) (t + 208 * k)
      (by rw [hs]; omega) (fun h => by simp [hJ2] at h)
    rw [show t + 208 * k + 104 * 2 = t + 208 * (k + 1) by omega] at this
    rw [this, ih t ht]
    simp [Pt.add_zero]

/-- The one-step hypotheses for every member, from facts about the base member. -/
theorem step_chain (cd : CorridorData) (X : Nat → State) (b : Nat → Pt) (τ0 : Nat)
    (hyps : ∀ k, CorridorHyp (cd.iter k) (X k) (X (k + 1)))
    (hJ : cd.J = 1 ∨ cd.J = 2)
    (first0 : FirstRead (X 0) (b 0) τ0)
    (hτ1 : cd.m 1 + 104 ≤ τ0) (hτ2 : cd.J = 2 → τ0 < cd.m 2)
    (hb : ∀ k, b (k + 1) = b k + cd.δ.v)
    (hb0 : cd.δ.phi (b 0) ≥ cd.C - 4)
    (perOut : ∀ k, FirstRead (X k) (b k) (τ0 + 104 * k) → ∀ t, t < (cd.iter k).m 1 →
      cd.δ.phi (run t (X k)).pos > cd.D + 12 → (run (t + 104) (X k)).pos = (run t (X k)).pos + cd.δ.v)
    (perRet0 : cd.J = 2 → ∀ t, cd.m 2 ≤ t → cd.δ.phi (run t (X 0)).pos > cd.D + 16 →
      (run (t + 104) (X 0)).pos + cd.δ.v = (run t (X 0)).pos) :
    ∀ k, StepHyp (cd.iter k) (X k) (X (k + 1)) (b k) (τ0 + 104 * k) := by
  have mk : ∀ k, FirstRead (X k) (b k) (τ0 + 104 * k) → StepHyp (cd.iter k) (X k) (X (k + 1)) (b k) (τ0 + 104 * k) := by
    intro k hf
    refine ⟨hyps k, by simp [hJ], hf, ?_, ?_, ?_, ?_, ?_⟩
    · rw [CorridorData.iter_m]; omega
    · intro h; simp at h; rw [CorridorData.iter_m]; have := hτ2 h; omega
    · rw [CorridorData.iter_δ, CorridorData.iter_C, block_pos b cd.δ.v hb k, Diag.phi_add, Diag.phi_smul,
        Diag.phi_v]
      omega
    · intro t ht hφ
      rw [CorridorData.iter_δ] at hφ ⊢
      rw [CorridorData.iter_D] at hφ
      exact perOut k hf t ht hφ
    · intro hJ2 t ht hφ
      simp at hJ2
      rw [CorridorData.iter_δ] at hφ ⊢
      rw [CorridorData.iter_D] at hφ
      rw [CorridorData.iter_m] at ht
      have P := posmap2 cd X hyps hJ2 k
      obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 208 * k := ⟨t - 208 * k, by omega⟩
      rw [P t0 (by omega)] at hφ ⊢
      rw [show t0 + 208 * k + 104 = (t0 + 104) + 208 * k by omega, P (t0 + 104) (by omega)]
      exact perRet0 hJ2 t0 (by omega) hφ
  intro k
  induction k with
  | zero => exact mk 0 (by simpa using first0)
  | succ k ih =>
    apply mk (k + 1)
    have := ih.step_first
    rw [CorridorData.iter_δ, ← hb, show τ0 + 104 * k + 104 = τ0 + 104 * (k + 1) by omega] at this
    exact this

/-- **Iterated one-step lemma.** -/
theorem unroll (cd : CorridorData) (X : Nat → State) (b : Nat → Pt) (τ0 : Nat)
    (H : ∀ k, StepHyp (cd.iter k) (X k) (X (k + 1)) (b k) (τ0 + 104 * k)) :
    ∀ k S, NewAfter (X k) (τ0 + 104 * k) S → ∃ r, r ≤ k ∧
      NewAfter (X 0) τ0 (S - Pt.smul (r : Int) cd.δ.v) ∧
      (r < k → cd.δ.phi (S - Pt.smul (r : Int) cd.δ.v) ≤ cd.D + 16) ∧
      (0 < r → cd.δ.phi (S - Pt.smul (r : Int) cd.δ.v) > cd.D + 12) := by
  have phis : ∀ (S : Pt) (r : Nat), cd.δ.phi (S - Pt.smul (r : Int) cd.δ.v) = cd.δ.phi S - 4 * (r : Int) := by
    intro S r; rw [Diag.phi_sub, Diag.phi_smul, Diag.phi_v]; omega
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨0, Nat.le_refl _, ?_, fun h => absurd h (Nat.lt_irrefl _), fun h => absurd h (Nat.lt_irrefl _)⟩
    have e : S - Pt.smul ((0 : Nat) : Int) cd.δ.v = S := by apply Pt.ext' <;> simp
    rw [e]; simpa using hS
  | succ k ih =>
    intro S hS
    rw [show τ0 + 104 * (k + 1) = (τ0 + 104 * k) + 104 by omega] at hS
    have st := (H k).step_new S hS
    simp only [CorridorData.iter_δ, CorridorData.iter_D] at st
    by_cases hn : cd.δ.phi S ≤ cd.D + 16
    · obtain ⟨r, hr, hnew, c1, c2⟩ := ih S (st.1 hn)
      refine ⟨r, by omega, hnew, fun hlt => ?_, c2⟩
      rcases Nat.lt_or_ge r k with h | h
      · exact c1 h
      · rw [phis]; omega
    · obtain ⟨r, hr, hnew, c1, c2⟩ := ih (S - cd.δ.v) (st.2 (by omega))
      have e : S - cd.δ.v - Pt.smul (r : Int) cd.δ.v = S - Pt.smul ((r + 1 : Nat) : Int) cd.δ.v := by
        apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
      rw [e] at hnew c1 c2
      refine ⟨r + 1, by omega, hnew, fun hlt => c1 (by omega), fun _ => ?_⟩
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0; rw [phis]; omega
      · exact c2 hpos

/-! ### The blank run before a channel block -/

theorem blank_facts : PeriodicAfter blankState blankHint.s blankHint.δu.v ∧
    ∀ t, t < blankHint.s → blankHint.δu.phi (run t blankState).pos ≤ blankHint.ψ := by
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
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = blankHint.s + c * 104 + j :=
      ⟨(t - blankHint.s) / 104, (t - blankHint.s) % 104, Nat.mod_lt _ (by decide), by omega⟩
    have e1 := congrArg Obs.pos (per (c + 1) j)
    have e2 := congrArg Obs.pos (per c j)
    simp [observe, Obs.shift] at e1 e2
    rw [show blankHint.s + c * 104 + j + 104 = blankHint.s + (c + 1) * 104 + j by rw [Nat.succ_mul]; omega,
      e1, e2]
    apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
  · intro t ht
    have := readsB_sound hpre t ht
    rw [runX, FState.toState_pos]; simpa using this

/-- Until it reads its only black cell, the run is the blank run. -/
theorem pos_eq_blank_upto (z : Pt) (τ : Nat) (h : FirstRead (initState [z]) z τ) :
    ∀ t, t ≤ τ → (run t (initState [z])).pos = (run t blankState).pos := by
  have h0 : Agree (fun w => w ≠ z) Pt.zero (initState [z]) blankState := by
    refine ⟨by simp [initState, blankState]; exact (Pt.add_zero _).symm, rfl, ?_⟩
    intro w hw
    simp [initState, blankState, Pt.add_zero, hw]
  intro t ht
  have A := agree_run t h0 (fun j hj => h.2 j (by omega))
  rw [A.1, Pt.add_zero]


end TwoBlack
