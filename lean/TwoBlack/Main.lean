/-
  Theorem A, unconditional.
-/
import TwoBlack.Final
import TwoBlack.PartData

namespace TwoBlack

/-- **Theorem A.**  Every Langton's-ant state with at most two black cells, at any ant position and
heading, reaches the period-104 highway.  This is `two_black_final` with its hypothesis, Lemma 6.3 for the
22 channel parents, discharged by `hpart_proved`. -/
theorem theoremA : ∀ s, AtMostTwoBlack s → ReachesP104 s :=
  two_black_final hpart_proved

end TwoBlack
