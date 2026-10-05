/-
  Mutation test for the partition check (not part of the library build): damaged child lists and a
  wrong zone must make `checkPart` fail.
-/
import TwoBlack.PartData

namespace TwoBlack.PartMut
open TwoBlack

def F0 : Fam1 := ⟨.mm, [], [⟨-33, -7⟩]⟩
def F19 : Fam1 := ⟨.mm, [], [⟨-33, -14⟩]⟩

def runWith (F : Fam1) (f : List (FamD × List Nat) → List (FamD × List Nat)) : Bool :=
  match partHintFor F with
  | some (H, P) => checkPart F H P (f (kidsIn chanTable F))
  | none => false

/-- Remove the `i`-th child. -/
def dropAt (i : Nat) (ks : List (FamD × List Nat)) : List (FamD × List Nat) := ks.take i ++ ks.drop (i + 1)

theorem ok0 : runWith F0 id = true := by native_decide
theorem drop_first : runWith F0 (dropAt 0) = false := by native_decide
theorem drop_middle : runWith F0 (dropAt 500) = false := by native_decide
theorem drop_tail : runWith F0 (fun ks => ks.take (ks.length - 1)) = false := by native_decide
theorem ok19 : runWith F19 id = true := by native_decide
theorem drop_split : runWith F19 (fun ks => ks.filter (fun c => c.2 != [10, 30])) = false := by native_decide
theorem drop_fixed : runWith F19 (dropAt 0) = false := by native_decide
theorem wrong_zone : (match partHintFor F19 with
    | some (H, P) => checkPart F19 { H with D := 25 } P (kidsIn chanTable F19)
    | none => false) = false := by native_decide

end TwoBlack.PartMut
