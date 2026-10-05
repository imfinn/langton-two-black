/-
  Theorem A in Lean: the final statements.
-/
import TwoBlack.Parents.All
import TwoBlack.Chan.All
import TwoBlack.PerpData
import TwoBlack.ParData

namespace TwoBlack

/-- The 2,432-entry parent table lists exactly the cells the blank run first reads before its tail cutoff. -/
theorem cover_ok : coverLoop parentTable (FState.init []) {} 0 blankT2 = true := by native_decide

/-- Every pair whose first-read cell is one of the 2,432 concrete level-1 cells reaches the highway. -/
theorem concreteParentsOK : ConcreteParentsOK := concrete_of_table parentTable parentTable_ok cover_ok

/-- **Theorem A, modulo the channel parents.**  Every state with at most two black cells, at any ant
position and heading, reaches the period-104 highway, provided the pairs whose first cell lies deep on one
of the 22 channels do. -/
theorem two_black (hch : ChannelParentsOK) : ∀ s, AtMostTwoBlack s → ReachesP104 s :=
  two_black_of (parentsOK_of concreteParentsOK hch)

/-- **Theorem A, modulo two mathematical statements.**
  * `hpart`: Lemma 6.3 for the 22 one-corridor channel parents, with the child lists computed by the
    C++ checker (`chanTable`: 45,452 one-parameter and 506 two-parameter children);
  * `hk2`: Proposition 5.2 for the 506 two-parameter children (Lemma 5.1(b–d)).
  Everything else — the 2,432 concrete parents and all 45,452 one-parameter children — is checked. -/
theorem two_black' (hpart : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kidsIn chanTable p.1))
    (hk2 : ∀ e ∈ chanTable, ∀ c ∈ e.kids2, FamReaches c) : ∀ s, AtMostTwoBlack s → ReachesP104 s :=
  two_black_of_partition chanTable concreteParentsOK hpart chanTable_ok hk2

/-- **Theorem A, modulo the child partition and the parallel two-parameter children.**
  * `hpart`: Lemma 6.3 for the 22 one-corridor channel parents (child lists from the C++ checker);
  * `hpar`: Proposition 5.2 for the 220 two-parameter children with parallel drifts (Lemma 5.1(c)).
  The 286 perpendicular two-parameter children are discharged by `check2p` (sound by `perp_family`,
  i.e. Lemma 5.1(b)), together with their slabs. -/
theorem two_black'' (hpart : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kidsIn chanTable p.1))
    (hpar : ∀ e ∈ chanTable, ∀ c ∈ e.kids2, isPerp c.1 = false → FamReaches c) :
    ∀ s, AtMostTwoBlack s → ReachesP104 s := by
  apply two_black' hpart
  intro e he c hc
  cases h : isPerp c.1 with
  | true => exact perpCovered_sound perp_covered e he c hc h
  | false => exact hpar e he c hc h

/-- **Theorem A in Lean, modulo Lemma 6.3 for the 22 channel parents.**  Every Langton's-ant state with
at most two black cells, at any ant position and heading, reaches the period-104 highway, provided the
child partition holds for the 22 one-corridor channel parents.  Everything else is proved: Lemmas 4.1 and
5.1 (all parts) and Proposition 5.2 in general, and every concrete case and family by verified computation. -/
theorem two_black_final (hpart : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kidsIn chanTable p.1)) :
    ∀ s, AtMostTwoBlack s → ReachesP104 s :=
  two_black'' hpart (parCovered_sound par_covered)

end TwoBlack
