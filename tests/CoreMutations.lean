import TwoBlack.OneBlack
namespace TwoBlack.AuditMutations
open TwoBlack Std
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
-- Two directions of finite-support board agreement must both be enforced.
example : agreeB (fun _ => true) Pt.zero (HashSet.ofList [⟨0, 0⟩]) {} = false := by native_decide
example : agreeB (fun _ => true) Pt.zero {} (HashSet.ofList [⟨0, 0⟩]) = false := by native_decide
example : agreeB (fun _ => true) Pt.zero (HashSet.ofList [⟨0, 0⟩]) (HashSet.ofList [⟨0, 0⟩]) = true := by native_decide
-- Certificate rejects a wrong heading and drift, and does not accept a zero search budget.
def f : FState := frun 10504 (FState.init [])
example : certAt f = true := by native_decide
example : certAt2 f { frun 104 f with dir := f.dir.right } = false := by native_decide
example : certAt2 f { frun 104 f with pos := f.pos } = false := by native_decide
example : certB [] 0 = false := by native_decide
-- Corrupt the verified first channel's hint in several distinct ways.
def channel : Fam1 := ⟨.mm, [], [⟨-33, -7⟩]⟩
def hint : Hint1 := ⟨40, 21, 197, [12310], 15392, ⟨-2, -2⟩, 419⟩
example : check1 channel hint = true := by native_decide
example : check1 channel { hint with u := ⟨0, 0⟩ } = false := by native_decide
example : check1 channel { hint with C := hint.D + 40 } = false := by native_decide
example : check1 channel { hint with ms := [0] } = false := by native_decide
example : check1 channel { hint with ms := [12310, 12310] } = false := by native_decide
example : check1 channel { hint with A := 100000 } = false := by native_decide
example : check0 [] { blankHint with periods := 0 } level1Families = false := by native_decide
example : check0 [] { blankHint with t1 := 0 } level1Families = false := by native_decide
end TwoBlack.AuditMutations
