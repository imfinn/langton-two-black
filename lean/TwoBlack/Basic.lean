/-
  Langton's ant: lattice points, headings, states, one update, runs.

  Conventions (shared with the C++ checker, the Python checkers and Ke's one-black development):
  north = +y; at each update the ant reads its cell, turns right on white and left on black,
  flips the cell, and steps one cell in the new heading.  `State.dir` is the heading on arrival.
-/
namespace TwoBlack

structure Pt where
  x : Int
  y : Int
deriving DecidableEq, Repr, Hashable

namespace Pt

instance : Add Pt := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Sub Pt := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩
instance : Neg Pt := ⟨fun a => ⟨-a.x, -a.y⟩⟩

def zero : Pt := ⟨0, 0⟩

/-- integer multiple of a point -/
def smul (k : Int) (a : Pt) : Pt := ⟨k * a.x, k * a.y⟩

@[simp] theorem add_x (a b : Pt) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : Pt) : (a + b).y = a.y + b.y := rfl
@[simp] theorem sub_x (a b : Pt) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : Pt) : (a - b).y = a.y - b.y := rfl
@[simp] theorem neg_x (a : Pt) : (-a).x = -a.x := rfl
@[simp] theorem neg_y (a : Pt) : (-a).y = -a.y := rfl
@[simp] theorem zero_x : zero.x = 0 := rfl
@[simp] theorem zero_y : zero.y = 0 := rfl
@[simp] theorem smul_x (k : Int) (a : Pt) : (smul k a).x = k * a.x := rfl
@[simp] theorem smul_y (k : Int) (a : Pt) : (smul k a).y = k * a.y := rfl

theorem ext' {a b : Pt} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

theorem ext_iff' {a b : Pt} : a = b ↔ a.x = b.x ∧ a.y = b.y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => ext' h1 h2⟩

/-- A tactic-friendly way to prove point identities: reduce to the two coordinates. -/
macro "pt_ext" : tactic => `(tactic| (apply Pt.ext' <;> simp <;> omega))

theorem add_sub_cancel (a b : Pt) : a + b - b = a := by pt_ext
theorem sub_add_cancel (a b : Pt) : a - b + b = a := by pt_ext
theorem add_comm (a b : Pt) : a + b = b + a := by pt_ext
theorem add_assoc (a b c : Pt) : a + b + c = a + (b + c) := by pt_ext
theorem add_zero (a : Pt) : a + zero = a := by pt_ext
theorem add_right_cancel {a b c : Pt} (h : a + c = b + c) : a = b := by
  have := congrArg (· - c) h; simpa [add_sub_cancel] using this

end Pt

inductive Dir where
  | N | E | S | W
deriving DecidableEq, Repr

namespace Dir
def right : Dir → Dir
  | N => E | E => S | S => W | W => N
def left : Dir → Dir
  | N => W | W => S | S => E | E => N
def vec : Dir → Pt
  | N => ⟨0, 1⟩ | E => ⟨1, 0⟩ | S => ⟨0, -1⟩ | W => ⟨-1, 0⟩
end Dir

structure State where
  black : Pt → Bool
  pos : Pt
  dir : Dir

/-- the heading after reading colour `c` with incoming heading `d` -/
def turn (c : Bool) (d : Dir) : Dir := if c then d.left else d.right

def step (s : State) : State :=
  let d := turn (s.black s.pos) s.dir
  { black := fun z => if z = s.pos then !(s.black z) else s.black z
    pos := s.pos + d.vec
    dir := d }

/-- `run t s` is the state after `t` updates. -/
def run : Nat → State → State
  | 0, s => s
  | n + 1, s => step (run n s)

@[simp] theorem run_zero (s : State) : run 0 s = s := rfl
theorem run_succ (n : Nat) (s : State) : run (n + 1) s = step (run n s) := rfl

theorem run_add (m n : Nat) (s : State) : run (m + n) s = run n (run m s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, run_succ, ih]; rfl

theorem run_succ' (n : Nat) (s : State) : run (n + 1) s = run n (step s) := by
  rw [Nat.add_comm, run_add]; rfl

@[simp] theorem step_black (s : State) (z : Pt) :
    (step s).black z = if z = s.pos then !(s.black z) else s.black z := rfl
@[simp] theorem step_pos (s : State) : (step s).pos = s.pos + (turn (s.black s.pos) s.dir).vec := rfl
@[simp] theorem step_dir (s : State) : (step s).dir = turn (s.black s.pos) s.dir := rfl

/-- What the ant sees at an update: where it is, its heading, and the colour it reads. -/
structure Obs where
  pos : Pt
  dir : Dir
  c : Bool
deriving DecidableEq, Repr

def observe (s : State) : Obs := ⟨s.pos, s.dir, s.black s.pos⟩

def Obs.shift (v : Pt) (o : Obs) : Obs := ⟨o.pos + v, o.dir, o.c⟩

end TwoBlack
