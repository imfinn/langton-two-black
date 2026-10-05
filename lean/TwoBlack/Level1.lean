/-
  The 22 one-cell channel families: every depth reaches the highway.

  Each family is a single black cell S = b + j·(−2,−2), j ≥ 40, on one of the 22 frontier channels of the
  blank highway (the "tail classes" of Section 6; Ke's 22 channels).  One of them (block ⟨-57,-38⟩ region,
  two switches) is Ke's exceptional backscattering channel.
-/
import TwoBlack.Level1Data

namespace TwoBlack

theorem level1_checks : level1Families.all (fun p => check1 p.1 p.2) = true := by native_decide

theorem level1_families_reach :
    ∀ p ∈ level1Families, ∀ k, ReachesP104 (initState (p.1.cells (p.2.n + k))) := by
  intro p hp k
  exact check1_sound p.1 p.2 (List.all_eq_true.mp level1_checks p hp) k

end TwoBlack
