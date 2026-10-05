/-
  One-corridor families (d = 1) and the initial relation between consecutive members.
-/
import TwoBlack.Succ

namespace TwoBlack

/-- The start state with black cells `cells`: the ant at the origin, heading north. -/
def initState (cells : List Pt) : State := ⟨fun z => cells.contains z, Pt.zero, Dir.N⟩

/-- A one-corridor family: `near` blocks stay put, `far` blocks (given at parameter 0) move with the
corridor parameter along the drift `δ.v`. -/
structure Fam1 where
  δ : Diag
  near : List Pt
  far : List Pt
deriving Repr

def Fam1.cells (F : Fam1) (n : Nat) : List Pt :=
  F.near ++ F.far.map (fun b => b + Pt.smul (n : Int) F.δ.v)

theorem Fam1.mem_cells (F : Fam1) (n : Nat) (z : Pt) :
    z ∈ F.cells n ↔ z ∈ F.near ∨ ∃ b ∈ F.far, z = b + Pt.smul (n : Int) F.δ.v := by
  simp [Fam1.cells, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, hb, rfl⟩
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, hb, rfl⟩

theorem contains_iff (l : List Pt) (z : Pt) : l.contains z = true ↔ z ∈ l := by
  simp

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Consecutive members are related initially by R_id, with the far zone moving out by 4 each time. -/
theorem fam_init (F : Fam1) (n : Nat) (C : Int)
    (hfar : ∀ b ∈ F.far, F.δ.phi (b + Pt.smul (n : Int) F.δ.v) ≥ C - 4)
    (hnear : ∀ b ∈ F.near, F.δ.phi b < C - 16) :
    ∀ k : Nat, Rid F.δ (C + 4 * (k : Int)) (initState (F.cells (n + k))) (initState (F.cells (n + k + 1))) := by
  intro k
  have phis : ∀ (b : Pt) (m : Nat), F.δ.phi (b + Pt.smul (m : Int) F.δ.v) = F.δ.phi b + 4 * (m : Int) := by
    intro b m; rw [Diag.phi_add, Diag.phi_smul, Diag.phi_v]; omega
  refine ⟨⟨by simp [initState]; exact (Pt.add_zero _).symm, rfl, ?_⟩, ?_⟩
  · intro z hz
    simp only [initState, Pt.add_zero]
    apply bool_eq_of_iff
    rw [contains_iff, contains_iff, Fam1.mem_cells, Fam1.mem_cells]
    constructor
    · rintro (h | ⟨b, hb, rfl⟩)
      · exact Or.inl h
      · exfalso; have := hfar b hb; rw [phis] at this hz; push_cast at hz; omega
    · rintro (h | ⟨b, hb, rfl⟩)
      · exact Or.inl h
      · exfalso; have := hfar b hb; rw [phis] at this hz; push_cast at hz; omega
  · intro z hz
    simp only [initState]
    apply bool_eq_of_iff
    rw [contains_iff, contains_iff, Fam1.mem_cells, Fam1.mem_cells]
    constructor
    · rintro (h | ⟨b, hb, rfl⟩)
      · exfalso; have := hnear z h; omega
      · refine Or.inr ⟨b, hb, ?_⟩
        apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega
    · rintro (h | ⟨b, hb, hzb⟩)
      · exfalso; have := hnear _ h; simp at this; omega
      · refine Or.inr ⟨b, hb, ?_⟩
        have : z = z - F.δ.v + F.δ.v := (Pt.sub_add_cancel z F.δ.v).symm
        rw [this, hzb]
        apply Pt.ext' <;> simp <;> push_cast <;> simp only [Int.add_mul, Int.one_mul] <;> omega

end TwoBlack
