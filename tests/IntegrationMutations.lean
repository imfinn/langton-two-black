import TwoBlack

namespace TwoBlack.AuditIntegrationMutations
open TwoBlack Std
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- The coverage checker must reject missing concrete and two-parameter tables.
example : coverLoop [] (FState.init []) {} 0 blankT2 = false := by native_decide
example : perpCovered chanTable [] = false := by native_decide
example : parCovered chanTable [] = false := by native_decide
-- The concrete coverage checker intentionally allows unused trailing entries.
-- This documents why its soundness statement proves coverage rather than exact table equality.
example : coverLoop parentTable (FState.init []) {} 0 blankT2 = true := cover_ok
example : coverLoop [] (FState.init []) {} 0 0 = true := by rfl
example : coverLoop (parentTable ++ parentTable.take 1) (FState.init []) {} 0 blankT2 = true := by native_decide
-- The table's informational tau field is not used by this Boolean coverage check.
example : coverLoop (parentTable.map (fun e => { e with tau := 0 }))
    (FState.init []) {} 0 blankT2 = true := by native_decide

-- Two-corridor native checks must reject corrupt geometric/certificate hints.
def corruptPerp (dropSlabs : Bool) : Bool :=
  match perpTable.head? with
  | some p => perpOK p.1 (if dropSlabs then p.2.1 else { p.2.1 with u := Pt.zero })
      (if dropSlabs then [] else p.2.2)
  | none => true
example : corruptPerp false = false := by native_decide
-- The first perpendicular entry has a raised first base and 28 essential slab hints.
example : corruptPerp true = false := by native_decide

def corruptPar : Bool :=
  match parTable.head? with
  | some p => parOK p.1 p.2.1 { p.2.2.1 with u := Pt.zero } p.2.2.2.1 p.2.2.2.2
  | none => true
example : corruptPar = false := by native_decide

-- The channel partition must reject a wrong first-read time and member base.
def F0 : Fam1 := ⟨.mm, [], [⟨-33, -7⟩]⟩
def altered (baseBad timeBad : Bool) : Bool :=
  match partHintFor F0 with
  | some (H, P) => checkPart F0 (if baseBad then { H with n := 39 } else H)
      (if timeBad then { P with tau := 0 } else P) (kidsIn chanTable F0)
  | none => false
example : altered true false = false := by native_decide
example : altered false true = false := by native_decide
end TwoBlack.AuditIntegrationMutations
