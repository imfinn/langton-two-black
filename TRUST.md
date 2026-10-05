# Trust and the meaning of Lean validation

The formal conclusion is `∀ s, AtMostTwoBlack s → ReachesP104 s` in the supplied Lean 4.30.0 definitions. It is a computer-assisted proof using `native_decide`, with ordinary proofs of the checkers' soundness and the unbounded assembly. It is not a proof whose finite computations are all reduced by the kernel.

## A. What Lean checks mathematically

The kernel checks the proof terms for the infinite-board dynamics, simulator correspondence, coupling, half-plane certificates, corridor transport/succession, one- and two-parameter family induction, tail descent, checker soundness, child partition transport, pose normalization, and final assembly. Standard logical axioms appearing in the final dependency report are `propext`, `Quot.sound`, and `Classical.choice`.

These proofs explain why successful finite checks imply statements about every relevant family depth, arbitrary late first reads, and arbitrary integer cell placements. There is no bounded-distance premise in the final statement.

## B. Native computation and compiler trust

In Lean 4.30.0, `native_decide` compiles and evaluates a closed Boolean expression. When the value is true, Lean's `nativeEqTrue` inserts a fresh auxiliary axiom asserting the Boolean equality and returns it to the proof. The implementation is visible in [Lean's pinned Native.lean](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Meta/Native.lean). It is inappropriate to describe this as the kernel independently rechecking the entire computation.

The final theorem's fresh dependency report contains 61 generated computation axioms plus the three standard axioms; the fresh result is in `audit/2026-10-05/theoremA-axioms.out` and `axioms.json`. The generated names are auxiliary implementation details. The assertions they stand for, their source locations and aggregation are described in `docs/PROOF_MAP.md`.

Accepting the computation premises trusts the correctness of Lean's compiler/code generation, native evaluator/runtime, compiled Lean core/Std operations (including integer arithmetic and hash sets), host compilation/linking where used by Lake, and the execution platform. Lean's kernel and official toolchain are also trusted to check/load the ordinary proofs correctly. The audit uses an official pinned toolchain, not a compiler supplied inside the archive.

No user-authored `axiom`, `sorry`, `admit`, unsafe proof definition, external solver, custom declaration injection, or checker bypass was found in the supplied source. This does not remove the deliberate native-computation trust boundary. `maxHeartbeats = 0` and raised recursion-depth settings change resource limits, not logical soundness.

A successful source build and `#print axioms` establish which axioms a theorem uses. They do not themselves prove the compiler correct. This audit did not rebuild Lean's implementation from source, formally verify its compiler, or attempt to replace these native proofs with kernel reduction.

## C. Reproducibility and data

`lean-toolchain` pins `leanprover/lean4:v4.30.0`; the project has no external Lake packages or Mathlib. All proof data needed to build are ordinary Lean literals included in `lean/TwoBlack`. The fresh audit build began with no project `.olean`, native libraries, or `.lake` directory. See `AUDIT.md` for machine, exact command, duration and exit status.

The imported compiled project modules/native libraries are rebuilt from those source literals. The theorem build does not read `.txt`/`.gz` dumps, call C++ or Python, or accept their exit codes as proofs. A malformed candidate list or hint can affect a theorem only after a Lean checker accepts all the properties required by its ordinary soundness proof, subject to native-execution trust.

The regeneration scripts are not verified programs. Running them may produce candidate data requiring a new Lean build. The preserved dumps allow reproducible generation without repeating the historical large C++ exploration. Rebuilding C++ dumps can change list ordering across C++ standard libraries because of unordered-container iteration; paired dumps must be used together. Fresh audit comparisons found equivalent family/hint data after normalizing order.

## D. External computational evidence

C++ and Python checks provide corroborating evidence, not additional premises of `theoremA`. Their own fixed-grid limits, finite horizons, machine-integer arithmetic, or reported update totals do not impose restrictions on the Lean theorem.

The particular standard highway turn word, F1, exhaustive historical operation counts, exact/unique partition statistics and detailed transit/extrema statistics are not conclusions of `theoremA`. `ChildPartition1` requires coverage by some listed family, not disjointness. `coverLoop_sound` requires coverage of the necessary first reads and permits extra trailing entries; an independent replay establishes exactness of the supplied concrete table separately. The theorem's native inputs are all checked for the sufficient mathematical properties used in the proof, not every descriptive claim a generator prints.

Mutation tests show that representative corrupted inputs are rejected. They are regression evidence; they neither prove complete bug freedom nor replace the soundness lemmas.

## E. Semantics, literature and novelty

`ReachesP104` is eventual periodicity of position, heading, and the color under the ant, with one of four drifts `(±2, ±2)` every 104 steps. It does not assert translation equality of the full evolving board, identify the blank-board highway's exact turn word, or establish that 104 is the least period.

The cardinality condition is a list of length at most two describing the complete black support; it includes zero cells and leaves pose and coordinates unrestricted. Manual interpretation of these definitions is part of the audit and is detailed in `docs/PROOF_MAP.md`.

Hao Ke's one-black theorem and semantically corresponding observation predicate are acknowledged in `ACKNOWLEDGEMENTS.md`. Comparison with his pinned source was an informal semantic check, not a Lean equivalence theorem or an independent full audit of his proof.

Lean does not certify novelty, priority, bibliography, historical independence, authorship, or manuscript exposition. The literature search here was limited, so the manuscript's “to our knowledge” qualification is retained.
