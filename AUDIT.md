# Independent proof-artifact audit — 5 October 2026

## Verdict

The unmodified supplied proof artifact passed a fresh Lean 4.30.0 source build, the intended-type check, the actual axiom audit, and the supplied plus added adversarial tests. The theorem is accepted as a computer-assisted observation-periodicity result under the explicit native-compilation trust assumptions below.

The accepted conclusion is eventual period-104 observation periodicity with one of the four drifts `(±2, ±2)`, for all initial states whose complete board support has at most two black cells, with arbitrary ant pose and arbitrary integer coordinates. It is a computer-assisted result relative to Lean's standard logical axioms and its native-computation trust boundary. No mathematical or formalization defect in that soundness/assembly chain was found in the inspected source. The theorem does not certify whole-board translational equality, the precise standard turn word, a least-period claim, literature priority, or every C++/Python statistic.

## Artifact provenance and method

The supplied archive was unpacked into a fresh temporary directory before any publication repository was created. Included logs and manuscript statements were treated as untrusted assertions, not accepted as proof. The working repository was assembled only after completion of the independent validation. All original 89 Lean files, the toolchain/configuration, raw dump/sample files, and the paper are preserved byte-for-byte; documentation and helper scripts were added separately. Code changes are listed below.

| Input | SHA-256 |
|---|---|
| `langton_two_black_lean.zip` | `76d7165e470d298e95bdbefaf8c1f09e51615c931649ac8bf3441fad5e46e3f4` |
| `TWO_BLACK_CELLS (2).md` | `031d56f6b35ef79b270c5e3935556f1acb7e0a0b7b6d19fe6b839d3e64b3fce4` |

The separately supplied Markdown is byte-identical to the archive's `paper/TWO_BLACK_CELLS.md`. The archive has 142 entries including directories and 13,447,834 unpacked bytes. Its top-level structure is `README.md`, `lean/`, `code/`, `paper/`, and `runs/`. It supplies no compiled project artifacts, no external package manifest/dependencies, and no explicit license. File hashes/sizes are retained in `audit/2026-10-05/original-files.json`; preservation checks are in `preservation.json`.

## Toolchain and clean build

- Toolchain: `leanprover/lean4:v4.30.0`, official release, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, target `arm64-apple-darwin24.6.0`.
- Lake: `5.0.0-src+d024af0`.
- Lean's bundled C compiler: Clang 19.1.2, LLVM commit `7ba7d8e2f7b6445b60679da826210cdde29eaf8b`.
- Configuration: one `lean_lib` named `TwoBlack`, `defaultTargets = ["TwoBlack"]`, `precompileModules = true`; zero external Lake packages, no Mathlib. The fresh `lake-manifest.json` has an empty packages list.
- Machine: macOS 26.6.2, arm64, 10 logical cores, 32 GiB RAM; Lake's default concurrency, no configured remote artifact cache. Exact tool output is in `tool-versions.json`.
- An auxiliary fresh `lake --no-cache build TwoBlack.PartCheck TwoBlack.Check2Par` compiled the generic proof layers while the default build computed table checks; its 29-declaration axiom report is also preserved. All outputs were generated locally from the unchanged extracted source.
- Command: `lake build`, in the freshly extracted `lean/` directory with no `.lake`, `.olean`, or supplied native libraries. The log shows local compilation and no project cache download. The recommended third-party command additionally uses explicit `--no-cache`.
- Result: success, exit code 0, all 261 jobs completed; all 32 parent chunks, 22 child modules, perpendicular/parallel tables, the partition, coverage and final assembly passed.
- Timing: 5,452.71 seconds elapsed (1 h 30 min 53 s rounded), 2026-10-05 17:49:01–19:19:54 UTC. The original clean command ran alongside the documented independent/auxiliary audit checks; this is wall time, not an isolated CPU-time benchmark.
- Linker warnings about nonexistent `/usr/local/lib` were benign; the result is determined by the build exit status, not the warning-free appearance of an upstream log.

The original proof was validated before maintainer edits. The publication copy's original Lean source and configuration hashes match it exactly. No copied build directory is part of the repository. Elan installed the official binary toolchain; the Lean compiler and its shipped core/Std were not themselves rebuilt or formally verified.

## Source and axiom audit

All authored Lean, C++, header and Python source was searched for `sorry`, `admit`, authored axioms, unsafe declarations, `implemented_by`, `extern`, opaque/partial proof paths, custom elaborator/declaration injection, file IO/external proof calls and checker-bypass settings. The scan covered the entire supplied source, excluding newly created build outputs and treating documentation/comments separately.

Findings: no authored Lean proof holes, custom logical axioms, unsafe proof declarations, external-solver acceptance, or declaration-injection bypass. The only custom proof macro is `pt_ext`, which expands to coordinate extensionality, simplification and `omega`. Resource settings `maxRecDepth` and `maxHeartbeats` do not disable checking. There are 61 native calls in the theorem's proof graph and eight more in the separately built original mutation module. These calls intentionally generate auxiliary axioms and must not be concealed by the “no custom axioms” source-scan statement.

Fresh commands:

```sh
lake env lean Axioms.lean
lake env lean /tmp/langton-audit.xPW28y/TheoremAAxioms.lean
lake env lean /tmp/langton-audit.xPW28y/ExtraAxioms.lean
```

The actual `#print axioms theoremA` report has **64 unique axioms**: `propext`, `Classical.choice`, `Quot.sound`, and **61 generated native-computation axioms**. There is no `sorryAx` or other axiom. The 61 exact check names were matched independently against the expected groups: 2 blank, 1 initial-family, 32 parent-chunk, 22 child-module, 1 perpendicular, 1 parallel, 1 concrete-coverage and 1 partition. All three fresh axiom-report commands exited 0; metadata is in `axiom-checks-meta.json`.

The full names and output are in `theoremA-axioms.out`, `axioms.json`, `axioms-all.out`, and `extra-axioms.out`. The added repository file `lean/TheoremAAxioms.lean` literally runs the requested `#print axioms theoremA` after opening the namespace and checks its intended type. The general `check1_sound`, `check0_sound`, `check2p_sound`, and `check2par_sound` proofs use only the standard axioms. The channel-specific `checkPart_sound` also inherits the single native premise `blank_check` through `blank_facts`; the final theorem inherits the full computation set. `TRUST.md` explains the distinction.

## Semantics and unrestricted scope

Inspected directly:

1. `State` has an arbitrary `Pt → Bool` infinite board, an arbitrary integer point and a four-way heading. `step` reads, turns right on white/left on black, flips the arrival cell, then advances in the new heading. North is positive y.
2. `AtMostTwoBlack` describes the entire board by membership in a list of length at most two. Duplicate list entries collapse to one black cell. There is no requirement that the ant begin on white or black, at the origin, or near a black cell.
3. `PermanentP104` repeats position/heading/read-color observations at each of the 104 phases, for every future cycle, with the stated diagonal drift. `ReachesP104` existentially chooses a finite start time. It asserts neither full-board equality nor an exact standard turn word/least period.
4. Translation and quarter-turn rotation commute with the dynamics and preserve the drift set. `canonCell` and `reaches_of_canonical` justify canonical pose reduction and restoration.
5. No radius/distance restriction appears in the final type, parent obligations, or family induction. Finite budgets and cutoffs verify representative finite facts. Tail descent and corridor induction cover all larger parameters and arbitrarily late reads. Unread cells are coupled separately.

Yes: the user's intended claim is obtained when “trajectory becomes period-104 up to translation” means these trajectory observations. A reading requiring the entire evolving board to be a translated copy would be stronger than the actual declaration.

## Soundness and dependency trace

`docs/PROOF_MAP.md` gives the full layer-by-layer trace, a dependency diagram, checker obligations, all 61 native groups, and their literal inputs. The audit inspected:

- half-plane agreement/translation closure and induction to all future periods;
- overlapping near/far corridor relations, strict disjoint switch windows, board-strip equality and all-time read bounds;
- corridor succession and induction to every one-parameter member;
- perpendicular double induction using zero cross-projections and H1′;
- parallel double induction using side/band/foreign-zone conditions, drift signs, and per-block initial conditions on every row;
- tail descent with pre-tail bound and separating margin;
- internal certificate searches tied to actual 104-step runs, and concrete-parent finite/tail/unread cases;
- concrete-table coverage and its connection to checked parent identities/divergence bounds;
- the one-step lemma, hypothesis transport and unrolling for channel depth;
- the member-40 partition checker, including the exceptional two-switch D = 52 hint, direct child equality/base matching, tail children and all-depth soundness;
- one-/two-parameter child reachability, raised bases and required slabs;
- first-read ordering of the original pair, duplicate/empty/singleton/unread cases, and arbitrary-pose assembly `two_black_final hpart_proved`.

No C++/Python program is executed by these Lean checkers. All inputs affecting the theorem are source literals in `Level1Data`, `Parents/Chunk*`, `Chan/Data*`, `PerpData`, `ParData`, `PartData`, and the small blank hints/constants. The clean build recreates compiled project modules/native libraries. Their upstream raw dumps and generator programs are regeneration provenance, not accepted logical premises.

The final checker proves sufficient coverage and reachability. It need not reject every irrelevant alteration: `coverLoop` allows unused trailing table entries and ignores `PEntry.tau`; `ChildPartition1` supplies at least one matching child, not uniqueness. This is sound for the final theorem but matters when describing exact partitions.

## Fresh counts and regeneration checks

| Item | Independently counted |
|---|---:|
| Original Lean files | 89 |
| Blank first reads before cutoff 14976 / concrete parent entries | 2,432 |
| Concrete-parent tail-family entries | 53,504 |
| One-cell channel parents | 22 |
| One-parameter channel children | 45,452 |
| Two-parameter channel children | 506 = 286 perpendicular + 220 parallel |
| Slab hints | 572 = 120 perpendicular + 452 parallel |

An independent Python replay of the blank dynamics confirms that the supplied concrete table is exactly the 2,432 first reads in order. This exactness is additional computational evidence; the Lean `coverLoop_sound` declaration proves the coverage needed for the theorem.

The original generators were rerun against decompressed supplied dumps, and the initial 22 family hints were regenerated separately using fresh C++ inspection plus Python simulation. Of the 60 generated/copied data-related files in that replay, 51 were byte-identical; eight channel files differed only by the generator's added `maxHeartbeats 0` resource setting, and `ParData.lean` lacked the crucial `par_covered` theorem. This is a real regeneration failure, despite the supplied proof source containing that theorem.

Fresh C++ `level1`, `chandump`, `perpdump`, `pardump`, and `leandump` runs completed. C++ standard-library unordered iteration changes parent/child/family order on this machine; comparisons normalized order and used each fresh two-corridor dump with its paired fresh channel dump. All concrete-parent and channel family/hint data, and the 286/220 two-corridor entries/slabs, match the preserved data in substance. Raw byte equality is not claimed.

## Fresh tests and independent corroboration

All 35 Lean assertions elaborated successfully against the fresh build:

| Lean test | Assertions and observed outcome | Fresh result |
|---|---|---|
| Original `TwoBlack.PartMut` | 2 positive controls, 6 corrupt partition inputs rejected | exit 0, 9.39 s including its build |
| Added `CoreMutations` | 3 positive controls, 12 corrupt board/certificate/corridor inputs rejected | exit 0; 15 assertions |
| Added `IntegrationMutations` | 8 corrupt table/slab/drift/partition inputs rejected; 4 coverage controls passed | exit 0, 15.88 s; 12 assertions |

The integration controls explicitly demonstrate that zero-horizon coverage, an unused trailing entry, and alteration of the unused informational `PEntry.tau` field can be accepted. These are not counterexamples to coverage soundness. The damaged required input tests fail as expected. The original test source and the added test sources are retained; fresh exits/log paths are in `lean-tests-meta.json`.

| External check rerun | Result |
|---|---|
| C++ `XVAL=1 calc level1` | 22 family checks and 2,433 direct checks pass (includes the blank); 44 extra-member cross-checks, no mismatch; 39,993,304 updates |
| Python `indep_family.py famdump_all.txt` | 311 accepted, 0 rejected, 0 data mismatches |
| Python `indep_family.py famdump_conc.txt` | 269 accepted, 0 rejected, 0 data mismatches |
| Python `indep_family.py famdump2.txt` | 506 accepted, 0 rejected, 0 data mismatches |
| Independent C++ detector on `v2dump.txt` | 3,004 configurations, 79,637,831 updates, 0 mismatches; sampled certificates identify the standard 104 word |
| Python coverage on preserved `childdump`, extra horizon 80 | 174 sampled parents, 350 members, 962,875 new-cell tests; 0 uncovered, 0 multiply covered, no uncertified parent skipped |
| Python mutation test, 20 random single drops | 2 positive baseline tests and 82 corrupt-list tests; all expected outcomes observed |

These finite tests support implementation agreement and representative rejection behavior; they do not prove the unbounded theorem or compiler correctness. The original Python coverage/mutation programs do not reliably signal failed summaries with nonzero process exit codes; the audit checked their actual summary/diagnostic content. The added wrapper does the same.

Not independently rerun: the historical full `level2` calculation (about 134 billion updates), all 201,124 historical predictions, the older 4,969-configuration detector report, and every other section-8 timing/statistic. Supplied `runs/*.out`/build logs remain labelled historical upstream evidence. No historical number is promoted to fresh audit evidence.

## Reproducibility defects and maintainer changes

1. The supplied parallel-data generator writes the literal table but omits `par_covered`, so its output cannot reproduce `Final.lean`. The maintained generator now emits exactly the supplied proof declaration.
2. The initial-hint generator invokes `./calc_v2`, while the documented compile command produces `calc`, and the 22-family seed input is not included. It now accepts `CALC` (default `./calc`); the regeneration driver reconstructs the seed list from preserved channel-parent records.
3. The C++ source relies on GNU `<bits/stdc++.h>` and fails with Apple's default `g++`/Clang. The audit first compiled the original algorithms through a temporary standard-header shim. The maintained `standard_headers.hpp` supplies those same headers; only include directives change. No C++ dynamics/checking algorithm is changed.
4. Upstream instructions use nonexistent `v2_dump.txt`, omit the path to sample family dumps, omit decompression and two-corridor generation steps, and do not fully document the initial family regeneration. Correct commands are in `REPRODUCIBILITY.md`.
5. Generator resource settings differ in eight channel files; this is documented, and the driver verifies content equality modulo only that option. Fresh C++ unordered iteration is not byte deterministic across platforms; paired raw dumps must be used.
6. Added a concise README, trust boundary, reproducibility guide, proof/dependency map, manuscript comparison, fresh evidence/manifests, Ke acknowledgement, validation scripts, and adversarial tests. Preserved both original READMEs for provenance and the original draft without silently editing its claims.
7. Build directories, compiled binaries, decompressed transient dumps, virtual environments and local rerun outputs are ignored. No remote publication, license selection or authorship invention was performed.

Maintainer verification succeeded:

- Both C++ programs compiled with `c++ -std=c++17 -O2` using the portable header, with exit 0. The repaired-build level-1 check and 3,004-configuration independent detector were rerun and again passed.
- All 13 Python source files and the Bash validation helper passed syntax checks; the maintained source scan reports 90 Lean files with no holes, authored axioms or bypass hooks.
- The repaired regeneration driver completed in 3.497 s: 82 of 90 Lean files were byte-identical and eight differed only by the documented `maxHeartbeats 0` option. `ParData.lean` now reproduces the supplied native proof declaration exactly.
- The maintained `validate.sh` completed end-to-end in a temporary harness pointing to the independently audited source and its fresh local build cache, with the maintained scripts/tests. This verifies paths, exit propagation, axiom parsing and test invocation, including a relative custom output directory. It does not constitute a second clean build of the publication checkout. The original full clean build already checks the identical preserved proof source.
- The updated optional wrapper's summary patterns were checked against the fresh external logs; the full long Python suite was not needlessly repeated after the wrapper was added. The generated candidate project was compared, not independently compiled a second time.

Exact commands/results are in `maintainer-verification.json`, `maintained-helper-meta.json`, `maintained-regeneration-meta.json`, and the associated logs.

## Manuscript and literature

`docs/MANUSCRIPT_REVIEW.md` contains 97 substantive comparison rows covering every paragraph, table row and bullet in sections 9–10. Main corrections are the contradictory standard-only axiom wording, “no hypotheses”, stronger-than-declared exact coverage, the precise observation meaning, aggregate native trust, and separation of historical/external statistics from formally established facts.

A limited primary-source search inspected Hao Ke's pinned one-black development and selected cited papers; it did not establish exhaustive priority. Ke's semantics agree in substance; no cross-project formal equivalence or full rebuild of his proof was undertaken. The manuscript's “to our knowledge” qualification remains appropriate as a qualification, not a Lean-certified novelty result. `ACKNOWLEDGEMENTS.md` records sources and a bibliographic clarification of Etse's article 49 in LIPIcs volume 386.

## Reproduce

Use `bash ./scripts/validate.sh --clean`, or the explicit commands in `REPRODUCIBILITY.md`. The theorem, axiom report and test modules are all available as source. The dated audit logs document this run; third parties should generate and inspect their own.
