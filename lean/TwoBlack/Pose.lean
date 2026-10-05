/-
  Translations and quarter-turn rotations commute with the dynamics and preserve the highway predicate;
  hence any ant position and heading reduce to the canonical pose (origin, heading north).
-/
import TwoBlack.Succ

namespace TwoBlack

def Pt.rot (p : Pt) : Pt := ⟨-p.y, p.x⟩
def Pt.unrot (p : Pt) : Pt := ⟨p.y, -p.x⟩

@[simp] theorem Pt.rot_unrot (p : Pt) : p.unrot.rot = p := by cases p; simp [Pt.rot, Pt.unrot]
@[simp] theorem Pt.unrot_rot (p : Pt) : p.rot.unrot = p := by cases p; simp [Pt.rot, Pt.unrot]
theorem Pt.rot_add (a b : Pt) : (a + b).rot = a.rot + b.rot := by
  apply Pt.ext' <;> simp [Pt.rot] <;> omega
theorem Pt.rot_smul (k : Int) (a : Pt) : (Pt.smul k a).rot = Pt.smul k a.rot := by
  apply Pt.ext' <;> simp [Pt.rot, Pt.smul, Int.mul_neg]

def Dir.rot : Dir → Dir
  | .N => .W | .W => .S | .S => .E | .E => .N

theorem Dir.rot_vec (d : Dir) : d.rot.vec = d.vec.rot := by
  cases d <;> rfl
theorem Dir.rot_left (d : Dir) : d.left.rot = d.rot.left := by cases d <;> rfl
theorem Dir.rot_right (d : Dir) : d.right.rot = d.rot.right := by cases d <;> rfl
theorem turn_rot (c : Bool) (d : Dir) : (turn c d).rot = turn c d.rot := by
  cases c <;> simp [turn, Dir.rot_left, Dir.rot_right]

def shiftS (τ : Pt) (s : State) : State := ⟨fun z => s.black (z - τ), s.pos + τ, s.dir⟩
def rotS (s : State) : State := ⟨fun z => s.black z.unrot, s.pos.rot, s.dir.rot⟩

theorem step_shiftS (τ : Pt) (s : State) : step (shiftS τ s) = shiftS τ (step s) := by
  simp only [step, shiftS, Pt.add_sub_cancel]
  congr 1
  · funext z
    by_cases e : z = s.pos + τ
    · subst e; simp [Pt.add_sub_cancel]
    · have e' : ¬ (z - τ = s.pos) := by
        intro h; apply e; rw [← h, Pt.sub_add_cancel]
      simp [e, e']
  · apply Pt.ext' <;> simp <;> omega

theorem step_rotS (s : State) : step (rotS s) = rotS (step s) := by
  simp only [step, rotS, Pt.unrot_rot]
  congr 1
  · funext z
    by_cases e : z = s.pos.rot
    · subst e; simp
    · have e' : ¬ (z.unrot = s.pos) := by
        intro h; apply e; rw [← h, Pt.rot_unrot]
      simp [e, e']
  · rw [Pt.rot_add, ← turn_rot, Dir.rot_vec]
  · rw [turn_rot]

theorem run_shiftS (τ : Pt) (n : Nat) (s : State) : run n (shiftS τ s) = shiftS τ (run n s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, run_succ, ih, step_shiftS]

theorem run_rotS (n : Nat) (s : State) : run n (rotS s) = rotS (run n s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, run_succ, ih, step_rotS]

theorem stdDrift_rot {v : Pt} (h : StdDrift v) : StdDrift v.rot := by
  rcases h with h | h | h | h <;> subst h <;> simp [StdDrift, Pt.rot]

theorem observe_shiftS (τ : Pt) (t : State) : observe (shiftS τ t) = (observe t).shift τ := by
  simp [observe, shiftS, Obs.shift, Pt.add_sub_cancel]

theorem observe_rotS (t : State) : observe (rotS t) = ⟨t.pos.rot, t.dir.rot, t.black t.pos⟩ := by
  simp [observe, rotS]

theorem reaches_shiftS (τ : Pt) (s : State) (h : ReachesP104 s) : ReachesP104 (shiftS τ s) := by
  obtain ⟨n, v, hv, hp⟩ := h
  refine ⟨n, v, hv, fun c ph hph => ?_⟩
  have e1 : run (c * 104 + ph) (run n (shiftS τ s)) = shiftS τ (run (c * 104 + ph) (run n s)) := by
    rw [← run_add n (c * 104 + ph) (shiftS τ s), run_shiftS, run_add n (c * 104 + ph) s]
  have e2 : run ph (run n (shiftS τ s)) = shiftS τ (run ph (run n s)) := by
    rw [← run_add n ph (shiftS τ s), run_shiftS, run_add n ph s]
  rw [e1, e2, observe_shiftS, observe_shiftS, hp c ph hph, Obs.shift_comm]

theorem reaches_rotS (s : State) (h : ReachesP104 s) : ReachesP104 (rotS s) := by
  obtain ⟨n, v, hv, hp⟩ := h
  refine ⟨n, v.rot, stdDrift_rot hv, fun c ph hph => ?_⟩
  have e1 : run (c * 104 + ph) (run n (rotS s)) = rotS (run (c * 104 + ph) (run n s)) := by
    rw [← run_add n (c * 104 + ph) (rotS s), run_rotS, run_add n (c * 104 + ph) s]
  have e2 : run ph (run n (rotS s)) = rotS (run ph (run n s)) := by
    rw [← run_add n ph (rotS s), run_rotS, run_add n ph s]
  rw [e1, e2, observe_rotS, observe_rotS]
  have := hp c ph hph
  simp only [observe, Obs.shift] at this
  injection this with h1 h2 h3
  simp only [Obs.shift]
  rw [h3, h1, h2, Pt.rot_add, Pt.rot_smul]

theorem shiftS_shiftS (a b : Pt) (s : State) : shiftS b (shiftS a s) = shiftS (a + b) s := by
  simp only [shiftS]
  congr 1
  · funext z; congr 1; apply Pt.ext' <;> simp <;> omega
  · rw [Pt.add_assoc]

theorem shiftS_zero (s : State) : shiftS Pt.zero s = s := by
  cases s; simp only [shiftS]
  congr 1
  · funext z; congr 1; apply Pt.ext' <;> simp
  · exact Pt.add_zero _

theorem rotS4 (s : State) : rotS (rotS (rotS (rotS s))) = s := by
  cases s with
  | mk b p d =>
    simp only [rotS]
    congr 1
    · funext z; congr 1; apply Pt.ext' <;> simp [Pt.unrot]
    · apply Pt.ext' <;> simp [Pt.rot]
    · cases d <;> rfl

theorem reaches_of_shiftS (τ : Pt) (s : State) (h : ReachesP104 (shiftS τ s)) : ReachesP104 s := by
  have := reaches_shiftS (-τ) _ h
  rw [shiftS_shiftS, show τ + -τ = Pt.zero by apply Pt.ext' <;> simp <;> omega, shiftS_zero] at this
  exact this

theorem reaches_of_rotS (s : State) (h : ReachesP104 (rotS s)) : ReachesP104 s := by
  have := reaches_rotS _ (reaches_rotS _ (reaches_rotS _ h))
  rw [rotS4] at this
  exact this

/-- Reduce any pose to the canonical one: translate the ant to the origin, then rotate until it heads
north.  The result is the state with black cells transformed by `canonCell s`. -/
def rotN : Nat → State → State
  | 0, s => s
  | k + 1, s => rotS (rotN k s)

def Pt.rotN : Nat → Pt → Pt
  | 0, p => p
  | k + 1, p => (Pt.rotN k p).rot

def Dir.rotN : Nat → Dir → Dir
  | 0, d => d
  | k + 1, d => (Dir.rotN k d).rot

/-- number of quarter turns that bring heading `d` to north -/
def Dir.toN : Dir → Nat
  | .N => 0 | .E => 1 | .S => 2 | .W => 3

theorem Dir.rotN_toN (d : Dir) : Dir.rotN d.toN d = .N := by
  cases d <;> rfl

theorem reaches_of_rotN (k : Nat) (s : State) (h : ReachesP104 (rotN k s)) : ReachesP104 s := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    -- rotN (k+1) s = rotS (rotN k s)
    exact ih s (reaches_of_rotS _ h)

theorem rotN_pos (k : Nat) (s : State) : (rotN k s).pos = Pt.rotN k s.pos := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rotN, rotS, Pt.rotN, ih]

theorem rotN_dir (k : Nat) (s : State) : (rotN k s).dir = Dir.rotN k s.dir := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rotN, rotS, Dir.rotN, ih]

theorem Pt.rotN_zero (k : Nat) : Pt.rotN k Pt.zero = Pt.zero := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Pt.rotN, ih]; rfl

def Pt.unrotN : Nat → Pt → Pt
  | 0, p => p
  | k + 1, p => Pt.unrotN k p.unrot

theorem Pt.rotN_unrotN (k : Nat) (z : Pt) : Pt.rotN k (Pt.unrotN k z) = z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp only [Pt.rotN, Pt.unrotN, ih, Pt.rot_unrot]

theorem Pt.unrotN_rotN (k : Nat) (z : Pt) : Pt.unrotN k (Pt.rotN k z) = z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp only [Pt.rotN, Pt.unrotN, Pt.unrot_rot, ih]

theorem rotN_black (k : Nat) (s : State) (z : Pt) : (rotN k s).black z = s.black (Pt.unrotN k z) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp only [rotN, rotS, ih, Pt.unrotN]

/-- Any pose reduces to the canonical one.  If the state obtained by moving the ant to the origin and
turning it north (black cells transformed by `canonCell`) reaches the highway, so does `s`. -/
def canonCell (s : State) (q : Pt) : Pt := Pt.rotN s.dir.toN (q + -s.pos)

theorem reaches_of_canonical (s : State) (S : State)
    (hpos : S.pos = Pt.zero) (hdir : S.dir = .N)
    (hblack : ∀ z, S.black z = s.black (Pt.unrotN s.dir.toN z + s.pos))
    (h : ReachesP104 S) : ReachesP104 s := by
  apply reaches_of_shiftS (-s.pos) s
  apply reaches_of_rotN s.dir.toN
  have e : rotN s.dir.toN (shiftS (-s.pos) s) = S := by
    cases S with
    | mk b p d =>
      simp only at hpos hdir hblack
      have : (rotN s.dir.toN (shiftS (-s.pos) s)) = ⟨(rotN s.dir.toN (shiftS (-s.pos) s)).black,
        (rotN s.dir.toN (shiftS (-s.pos) s)).pos, (rotN s.dir.toN (shiftS (-s.pos) s)).dir⟩ := rfl
      rw [this]
      congr 1
      · funext z; rw [rotN_black, hblack]; simp only [shiftS]; congr 1; apply Pt.ext' <;> simp
      · rw [rotN_pos, hpos]; simp only [shiftS]
        rw [show s.pos + -s.pos = Pt.zero by apply Pt.ext' <;> simp <;> omega, Pt.rotN_zero]
      · rw [rotN_dir, hdir]; simp only [shiftS]; exact Dir.rotN_toN _
  rw [e]; exact h

end TwoBlack
