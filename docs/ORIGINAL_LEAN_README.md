# TwoBlack: a Lean 4 formalization of the corridor calculus for Langton's ant

This is Lean 4.30.0, using the core library only (no Mathlib). The conventions match the C++ and Python checkers and Hao Ke's one-black development: north = +y; turn right on white and left on black; flip the cell; step. `State.dir` is the heading on arrival, and `ReachesP104` is Ke's highway predicate: observations are eventually 104-periodic with one of the four standard drifts.

The main result is `theoremA` (`Main.lean`): every state with at most two black cells, at any ant position and heading, reaches the period-104 highway. It has no hypotheses.

## Main theorems

| Theorem | File | Statement |
|---|---|---|
| `corridor` | `Corridor.lean` | Lemma 4.1, the corridor lemma, for any number of switches |
| `corridor_succ`, `corridor_family` | `Succ.lean` | Lemma 5.1(a) and Proposition 5.2 for one corridor |
| `perp_succ`, `perp_family` | `Perp.lean` | Lemma 5.1(b) and Proposition 5.2 for two perpendicular corridors (with H1′) |
| `par_succ`, `par_family` | `Par.lean` | Lemma 5.1(c) and Proposition 5.2 for two parallel corridors (with a checkable form of H3) |
| `check1_sound`, `check2p_sound`, `check2par_sound` | `Check*.lean` | soundness of the executable family checkers |
| `descent` | `Tail.lean` | Lemma 6.1, descent along the tail |
| `check0_sound` | `Parent0.lean` | Lemma 6.3 for parents without a corridor; certificates are searched for inside Lean |
| `level1_families_reach` | `Level1.lean` | all 22 one-cell channel families, at every depth ≥ 40 |
| `one_black` | `General.lean` | `∀ s, ExactlyOneBlack s → ReachesP104 s`, by the corridor calculus |
| `two_black_of` | `TheoremA.lean` | Theorem A from the hypothesis `ParentsOK` |
| `two_black`, `two_black'`, `two_black''` | `Final.lean` | Theorem A from progressively weaker hypotheses |
| `two_black_final` | `Final.lean` | `hpart → ∀ s, AtMostTwoBlack s → ReachesP104 s` |
| `step_first`, `step_new` | `Step.lean` | Lemma 6.4, the one-step lemma |
| `step_chain`, `unroll` | `Step.lean` | its hypotheses for every member; Corollary 6.5 |
| `checkPart_sound` | `PartCheck.lean` | Lemma 6.3 for a channel parent, from a check on member 40 |
| `hpart_proved` | `PartData.lean` | `hpart`, for all 22 channel parents |
| **`theoremA`** | `Main.lean` | **`∀ s, AtMostTwoBlack s → ReachesP104 s`, with no hypotheses** |

`theoremA` is `two_black_final hpart_proved`. Everything is proved, either in general or by verified computation. The computations cover about 4.5 million concrete cases, about 100,000 families and the partition for the 22 channel parents.

## Building

```sh
lake build                       # everything: about 19 CPU-hours, ~10 h on 2 cores
lake build TwoBlack.General      # up to the one-black theorem (about a minute)
```

`lakefile.toml` sets `precompileModules = true`, so `native_decide` runs compiled native code. That is about 30× faster than the interpreter.

## Trust

`#print axioms` on any theorem shows `propext`, `Quot.sound` and `Classical.choice`. Theorems that rest on a finite computation also show a `…native_decide.ax…` axiom, meaning they trust Lean's compiler to evaluate a Boolean checker. That is the same trust model as Ke's development.

`Axioms.lean` prints the axioms of the main theorems. For `theoremA` these are `propext`, `Quot.sound` and `Classical.choice`, plus 61 `native_decide` axioms.

`TwoBlack/PartMut.lean` is a mutation test for the partition check and is not part of the default build. Run it with `lake build TwoBlack.PartMut`. Damaged child lists, and a wrong zone for the two-switch parent, must make the check fail.

## Data

- `Level1Data.lean` holds the hints for the 22 channel families.
- `Parents/Chunk*.lean` hold the 2,432 concrete parents with hints for their 22 tail families each.
- `Chan/Data*.lean` hold the children of the 22 channel parents, and `PerpData.lean` and `ParData.lean` the hints for their two-parameter children.
- `PartData.lean` holds the hints for the partition check of the 22 channel parents.

All of these are generated from the C++ checker's output by the `gen_lean_*.py` scripts in `code/`. Hints are never trusted: the Lean checkers recompute and verify everything they use.
