/-
  Lemma 6.3 for parents with no corridor (d = 0): adding one cell to a certified configuration `P`.

  * `certB cells periods` searches for a half-plane certificate inside Lean (no hints) and is sound for
    `ReachesP104 (initState cells)`.
  * `check0 P H fs` checks: a certificate for `P` with drift `δu.v`, the tail margin (window `[t1, t1+104)`),
    a certificate for `P ++ [z]` for every cell `z` first read in `[tdiv, t1 + 104·40)`, and, for every
    cell `z₀` first read in the window, a verified one-corridor family `P ++ [z₀ + j·δu.v]`.
  * `check0_sound`: then `P ++ [z]` reaches the highway for every cell `z` not read before `tdiv`.
-/
import TwoBlack.Tail

namespace TwoBlack
open Std

/-! ### Certificate search -/

/-- smallest `dot u` over the positions of the next `k` updates from `f` (and `acc`) -/
def minDot (u : Pt) : FState → Nat → Int → Int
  | _, 0, acc => acc
  | f, k + 1, acc => minDot u f.step k (min acc (dot u f.pos))

/-- Is there a half-plane certificate with start state `f` and end state `f' = frun 104 f`? -/
def certAt2 (f f' : FState) : Bool :=
  let u := f'.pos - f.pos
  stdDriftB u && f'.dir == f.dir &&
    (let A := minDot u f 104 (dot u f.pos) - 1
     let G : Pt → Bool := fun z => decide (dot u z > A)
     agreeB G u f.black f'.black && readsB G f 104)

def certAt (f : FState) : Bool := certAt2 f (frun 104 f)

theorem certAt_sound (f : FState) (h : certAt f = true) :
    ∃ u A, StdDrift u ∧
      Agree (fun z => dot u z > A) u f.toState (frun 104 f).toState ∧
      ∀ j, j < 104 → dot u (frun j f).pos > A := by
  unfold certAt certAt2 at h
  generalize hf' : frun 104 f = f' at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hd⟩, hag, hr⟩ := h
  refine ⟨f'.pos - f.pos, minDot (f'.pos - f.pos) f 104 (dot (f'.pos - f.pos) f.pos) - 1,
    stdDriftB_sound hs, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [FState.toState_pos, FState.toState_pos, Pt.add_comm, Pt.sub_add_cancel]
  · rw [FState.toState_dir, FState.toState_dir]; exact hd
  · intro z hz
    rw [FState.toState_black, FState.toState_black]
    exact agreeB_sound hag z (by simp; exact hz)
  · intro j hj
    have := readsB_sound hr j hj
    simp at this
    exact this

/-- try certificate starts `f, frun 104 f, frun 208 f, …` (`k` candidates) -/
def certLoop : FState → Nat → Bool
  | _, 0 => false
  | f, k + 1 => let f' := frun 104 f; certAt2 f f' || certLoop f' k

theorem certLoop_sound : ∀ (k : Nat) (f : FState), certLoop f k = true →
    ∃ i, certAt (frun (104 * i) f) = true := by
  intro k
  induction k with
  | zero => intro f h; simp [certLoop] at h
  | succ k ih =>
    intro f h
    simp only [certLoop, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨0, by simpa [frun, certAt] using h⟩
    · obtain ⟨i, hi⟩ := ih _ h
      refine ⟨i + 1, ?_⟩
      rw [show 104 * (i + 1) = 104 + 104 * i by omega, frun_add]
      exact hi

def certB (cells : List Pt) (periods : Nat) : Bool := certLoop (FState.init cells) periods

theorem certB_sound (cells : List Pt) (periods : Nat) (h : certB cells periods = true) :
    ReachesP104 (initState cells) := by
  obtain ⟨i, hi⟩ := certLoop_sound periods _ h
  obtain ⟨u, A, hu, hag, hr⟩ := certAt_sound _ hi
  have runX : ∀ t, run t (initState cells) = (frun t (FState.init cells)).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  apply reaches_of_certificate (initState cells) (104 * i) u A hu
  · rw [runX, runX, frun_add]; exact hag
  · intro j hj; rw [runX, frun_add, FState.toState_pos]; exact hr j hj

/-! ### The d = 0 checker -/

/-- a verified family for the window cell `z0`: near blocks `P`, far block `z0`, drift `δu.v`; members below
the family's base (if the base exceeds 40) are certified directly -/
def famFor (P : List Pt) (δu : Diag) (z0 : Pt) (fs : List (Fam1 × Hint1)) (periods : Nat) : Bool :=
  fs.any (fun p => p.1.δ == δu && p.1.near == P && p.1.far == [z0] && check1 p.1 p.2 &&
    (List.range (p.2.n - 40)).all (fun i =>
      certB (P ++ [z0 + Pt.smul ((40 + i : Nat) : Int) δu.v]) periods))

theorem famFor_sound {P : List Pt} {δu : Diag} {z0 : Pt} {fs : List (Fam1 × Hint1)} {periods : Nat}
    (h : famFor P δu z0 fs periods = true) :
    ∀ j : Nat, 40 ≤ j → ReachesP104 (initState (P ++ [z0 + Pt.smul (j : Int) δu.v])) := by
  simp only [famFor, List.any_eq_true] at h
  obtain ⟨⟨F, H⟩, _, h2⟩ := h
  dsimp only at h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h2
  obtain ⟨⟨⟨⟨hδ, hn⟩, hf⟩, hc⟩, hslab⟩ := h2
  intro j hj
  rcases Nat.lt_or_ge j H.n with hlt | hge
  · have := certB_sound _ _ (hslab (j - 40) (by omega))
    rw [show 40 + (j - 40) = j by omega] at this
    exact this
  · have := check1_sound F H hc (j - H.n)
    rw [show H.n + (j - H.n) = j by omega] at this
    have e : F.cells j = P ++ [z0 + Pt.smul (j : Int) δu.v] := by
      simp only [Fam1.cells, hn, hf, hδ, List.map]
    rw [e] at this
    exact this

/-- One pass over the first `k` updates from time `t`: every first read `p` at a time `≥ tdiv` gets a
certificate for `P ++ [p]`, and a verified family when it falls in the window `[t1, t1 + 104)`. -/
def loop0 (P : List Pt) (δu : Diag) (tdiv t1 periods : Nat) (fs : List (Fam1 × Hint1)) :
    FState → HashSet Pt → Nat → Nat → Bool
  | _, _, _, 0 => true
  | f, V, t, k + 1 =>
    let p := f.pos
    let isNew := !(V.contains p) && decide (tdiv ≤ t)
    let inW := decide (t1 ≤ t) && decide (t < t1 + 104)
    (!isNew || (certB (P ++ [p]) periods && (!inW || famFor P δu p fs periods))) &&
    loop0 P δu tdiv t1 periods fs f.step (V.insert p) (t + 1) k

theorem loop0_sound (P : List Pt) (δu : Diag) (tdiv t1 periods : Nat) (fs : List (Fam1 × Hint1))
    (x : State) : ∀ (k : Nat) (f : FState) (V : HashSet Pt) (t : Nat),
    loop0 P δu tdiv t1 periods fs f V t k = true →
    f.toState = run t x →
    (∀ q, V.contains q = true ↔ ∃ t', t' < t ∧ (run t' x).pos = q) →
    ∀ τ, t ≤ τ → τ < t + k → ∀ z, FirstRead x z τ → tdiv ≤ τ →
      certB (P ++ [z]) periods = true ∧ (t1 ≤ τ → τ < t1 + 104 → famFor P δu z fs periods = true) := by
  intro k
  induction k with
  | zero => intro f V t _ _ _ τ h1 h2; omega
  | succ k ih =>
    intro f V t h hf hV τ h1 h2 z hz htd
    simp only [loop0, Bool.and_eq_true] at h
    obtain ⟨hnow, hrest⟩ := h
    have hfs : f.step.toState = run (t + 1) x := by rw [FState.step_toState, hf, run_succ]
    have hV' : ∀ q, (V.insert f.pos).contains q = true ↔ ∃ t', t' < t + 1 ∧ (run t' x).pos = q := by
      intro q
      rw [HashSet.contains_insert, Bool.or_eq_true, hV]
      have hp : f.pos = (run t x).pos := by rw [← hf]; rfl
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
    · -- τ = t: this update is the first read of z
      have hτt : τ = t := by omega
      subst hτt
      have hp : f.pos = z := by rw [← hz.1, ← hf]; rfl
      have hnew : V.contains f.pos = false := by
        rcases Bool.eq_false_or_eq_true (V.contains f.pos) with hc | hc
        · exfalso
          obtain ⟨t', ht', e⟩ := (hV _).mp hc
          rw [hp] at e
          exact hz.2 t' ht' e
        · exact hc
      simp only [hnew, Bool.not_false, Bool.true_and, decide_eq_true htd, Bool.not_true,
        Bool.false_or, Bool.and_eq_true] at hnow
      obtain ⟨hcert, hfam⟩ := hnow
      rw [hp] at hcert hfam
      refine ⟨hcert, fun hw1 hw2 => ?_⟩
      simp only [decide_eq_true hw1, decide_eq_true hw2, Bool.and_true, Bool.not_true, Bool.false_or] at hfam
      exact hfam
    · exact ih f.step (V.insert f.pos) (t + 1) hrest hfs hV' τ hτ (by omega) z hz htd

/-- Hints for a d = 0 parent: certificate start `s` with drift `δu.v` and offset `A`, tail window start
`t1` with margin `ψ`, the divergence time `tdiv`, and the certificate-search budget. -/
structure Hint0 where
  s : Nat
  δu : Diag
  A : Int
  t1 : Nat
  ψ : Int
  tdiv : Nat
  periods : Nat
deriving Repr

def check0 (P : List Pt) (H : Hint0) (fs : List (Fam1 × Hint1)) : Bool :=
  let f0 := FState.init P
  let Sc := frun H.s f0
  let Sc' := frun 104 Sc
  let u := H.δu.v
  let G : Pt → Bool := fun z => decide (dot u z > H.A)
  (Sc'.pos == Sc.pos + u) && (Sc'.dir == Sc.dir) &&
  agreeB G u Sc.black Sc'.black && readsB G Sc 104 &&
  decide (H.s ≤ H.t1) && decide (H.tdiv ≤ H.t1) &&
  readsB (fun z => decide (H.δu.phi z ≤ H.ψ)) f0 H.s &&
  readsB (fun z => decide (H.δu.phi z > H.ψ + 4)) (frun H.t1 f0) 104 &&
  loop0 P H.δu H.tdiv H.t1 H.periods fs f0 {} 0 (H.t1 + 104 * 40)

theorem diag_std (δ : Diag) : StdDrift δ.v := by
  cases δ <;> simp [StdDrift, Diag.v]

/-- **Lemma 6.3, d = 0.**  If `check0 P H fs` passes, then `P ++ [z]` reaches the highway for every cell
`z` that the run from `P` does not visit before `H.tdiv`. -/
theorem check0_sound (P : List Pt) (H : Hint0) (fs : List (Fam1 × Hint1)) (hc : check0 P H fs = true) :
    ∀ z, (∀ t, t < H.tdiv → (run t (initState P)).pos ≠ z) → ReachesP104 (initState (P ++ [z])) := by
  simp only [check0, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpos, hdir⟩, hag⟩, hreads⟩, hst⟩, htd⟩, hpre⟩, hwin⟩, hloop⟩ := hc
  let x := initState P
  have runX : ∀ t, run t x = (frun t (FState.init P)).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  let G : Pt → Prop := fun z => dot H.δu.v z > H.A
  have hagS : Agree G H.δu.v (run H.s x) (run (H.s + 104) x) := by
    rw [runX, runX, frun_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [FState.toState_pos, FState.toState_pos]; exact hpos
    · rw [FState.toState_dir, FState.toState_dir]; exact hdir
    · intro z hz
      rw [FState.toState_black, FState.toState_black]
      exact agreeB_sound hag z (by simp; exact hz)
  have hin : ∀ j, j < 104 → G (run (H.s + j) x).pos := by
    intro j hj
    rw [runX, frun_add, FState.toState_pos]
    have := readsB_sound hreads j hj
    simp at this
    exact this
  have hu := diag_std H.δu
  have reachP : ReachesP104 x := reaches_of_certificate x H.s H.δu.v H.A hu hagS hin
  have per := halfplane_obs x G H.δu.v H.s 104 (by decide) (fun z hz => stdDrift_dot_pos hu z H.A hz) hagS hin
  have hperA : PeriodicAfter x H.s H.δu.v := by
    intro t ht
    obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = H.s + c * 104 + j :=
      ⟨(t - H.s) / 104, (t - H.s) % 104, Nat.mod_lt _ (by decide), by omega⟩
    have e1 := congrArg Obs.pos (per (c + 1) j)
    have e2 := congrArg Obs.pos (per c j)
    simp [observe, Obs.shift] at e1 e2
    rw [show H.s + c * 104 + j + 104 = H.s + (c + 1) * 104 + j by rw [Nat.succ_mul]; omega, e1, e2]
    apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
  have hpre' : ∀ t, t < H.s → H.δu.phi (run t x).pos ≤ H.ψ := by
    intro t ht
    have := readsB_sound hpre t ht
    rw [runX, FState.toState_pos]; simpa using this
  have hwin' : ∀ j, j < 104 → H.δu.phi (run (H.t1 + j) x).pos > H.ψ + 4 := by
    intro j hj
    have := readsB_sound hwin j hj
    rw [runX, frun_add, FState.toState_pos]; simpa using this
  have L := loop0_sound P H.δu H.tdiv H.t1 H.periods fs x _ _ _ 0 hloop
    (by rw [runX]; rfl) (by intro q; simp)
  intro z hz
  by_cases hvis : ∃ t, (run t x).pos = z
  · obtain ⟨τ, hτ⟩ := firstRead_of_visit x z hvis
    have htd' : H.tdiv ≤ τ := by
      rcases Nat.lt_or_ge τ H.tdiv with h | h
      · exact absurd hτ.1 (hz τ h)
      · exact h
    rcases Nat.lt_or_ge τ (H.t1 + 104 * 40) with hlt | hge
    · have h0 : 0 ≤ τ := Nat.zero_le τ
      have h1 : τ < 0 + (H.t1 + 104 * 40) := by rw [Nat.zero_add]; exact hlt
      exact certB_sound _ _ (L τ h0 h1 z hτ htd').1
    · -- deep in the tail: descend to the window
      let j := (τ - H.t1) / 104
      have hj40 : 40 ≤ j := by omega
      have hD := descent x H.δu H.s H.t1 H.ψ hperA hst hpre' hwin' j z τ hτ (by omega)
      have hw := (L (τ - 104 * j) (by omega) (by omega) _ hD (by omega)).2 (by omega) (by omega)
      have := famFor_sound hw j hj40
      rw [Pt.sub_add_cancel] at this
      exact this
  · exact reaches_add_unread P z (fun t e => hvis ⟨t, e⟩) reachP

end TwoBlack
