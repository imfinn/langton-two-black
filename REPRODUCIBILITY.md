# Reproducing the validation

Run commands from the repository root unless a `cd` is shown. The proof build requires the official Lean toolchain through elan and a working native compiler/linker. It does not require Python, NumPy, Mathlib, C++ generators, or any raw dump. Python 3 is used by the convenience audit/regeneration scripts; NumPy and C++ are optional cross-check dependencies.

The repository also supplies a manual **Validate theoremA** GitHub Actions workflow. Run it from the Actions page to build from source on Ubuntu, print the axioms and run mutation tests. It uses the pinned Lean 4.30.0 toolchain and retains fresh logs as a workflow artifact. No project build cache is restored. Its runtime can be substantial; the supplied audit records a local Mac build, not a completed GitHub-hosted run.

## The theorem, from source

```sh
cd lean
elan toolchain install leanprover/lean4:v4.30.0
lean --version
lake --version
lake clean
lake --no-cache build
lake env lean TheoremAAxioms.lean
lake env lean Axioms.lean
```

`TheoremAAxioms.lean` imports the library, checks the intended type and literally runs `#print axioms theoremA` with `TwoBlack` opened. `Axioms.lean` is the original, broader axiom report. The expected final report has three standard axioms plus 61 generated native-computation axioms, with no `sorryAx`. See `TRUST.md` for their interpretation; a build success is not a kernel-only certificate.

A fresh source build starts with no project compiled artifacts. `lake clean` removes build products; `--no-cache` disables use of Lake's build-artifact cache. No external package dependencies are declared. The archive had no compiled project artifacts, and the independent audit built in a new extraction. Large native checks dominate the runtime; allow substantial time, and consult the recorded hardware and fresh timing in `AUDIT.md`. Historical 19-CPU-hour figures are not a promise for another machine.

The complete convenience command adds scans, records logs under an ignored local directory, and checks the final axiom counts:

```sh
./scripts/validate.sh --clean
```

Without `--clean`, it resumes/reuses the current build. The supplied audit evidence is never an input to the validation script.

## Mutation and adversarial tests

After the theorem build:

```sh
cd lean
lake build TwoBlack.PartMut
lake env lean ../tests/CoreMutations.lean
lake env lean ../tests/IntegrationMutations.lean
```

`PartMut` has two undamaged positive controls and six damaged partition inputs. The core tests cover both directions of board-support agreement, bad headings/drifts, missing search budgets, invalid corridor separation, switch lists and half-plane cuts. The integration tests cover missing concrete and two-corridor tables, bad two-corridor drifts, missing required slabs, and incorrect partition member/time hints. They also document the coverage checker's intentionally permissive horizon-zero behavior. Each file must elaborate successfully; negative tests assert a Boolean result is false.

These test modules do not contribute axioms to `theoremA`. They use native computation themselves and share its compiler trust boundary.

## Regenerate the included proof data from preserved dumps

The candidate inputs are preserved in `runs/*.txt.gz`. Generation alone is not validation; any replacement data require another Lean build. The maintained scripts fix the original parallel generator's missing `par_covered` theorem and the initial-hint generator's `calc_v2` executable mismatch.

The audit used Python 3.9.6, NumPy 2.0.2, and Apple Clang 17. The following environment keeps NumPy at the audited version. Use a supported Python interpreter if the system Python cannot create the environment.

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r code/requirements-crosscheck.txt
c++ -std=c++17 -O2 -o code/calc code/calculus.cpp
python3 scripts/regenerate_data.py --output /tmp/two-black-regenerated --calc ./code/calc
```

The output is a complete source project copied without build artifacts, then supplied with regenerated data. The script writes a comparison report and requires agreement with the shipped files after ignoring only `set_option maxHeartbeats 0` lines: the original channel generator adds that option to eight files where it was absent in the archive. That option is a resource limit, not proof data. All other generated content must agree. The Level1 seed list is reconstructed from the archived channel-parent records, and its hints are independently regenerated with C++ inspection and Python simulation. The part generator performs its own Python replay before writing `PartData.lean`.

Then validate the regenerated project:

```sh
cd /tmp/two-black-regenerated/lean
lake --no-cache build
lake env lean Axioms.lean
```

The optional raw C++ dump generation commands are:

```sh
cd code
./calc leandump > leandump.txt
./calc chandump > chandump.txt
./calc perpdump > perpdump.txt
./calc pardump > pardump.txt
```

Use the corresponding fresh `chandump` with its fresh `perpdump` and `pardump`: their indices depend on list order. Unordered-container iteration differs across standard libraries, so fresh dumps can describe the same families/hints in a different order. The independent audit confirmed semantic equality after order normalization; byte-for-byte raw dump equality is not promised. The preserved dumps are the deterministic inputs for the bundled regeneration script.

## Independent C++/Python corroboration

These checks are optional and outside the proof's trust premises:

```sh
c++ -std=c++17 -O2 -o code/indep code/indep.cpp
cd code
XVAL=1 ./calc level1
./indep file ../runs/v2dump.txt
python3 indep_family.py ../runs/famdump_all.txt
python3 indep_family.py ../runs/famdump_conc.txt
python3 indep_family.py ../runs/famdump2.txt
gzip -dc ../runs/childdump.txt.gz > childdump.txt
python3 indep_cover.py childdump.txt 80
python3 mutation_test.py childdump.txt 20
```

Read the summary lines as well as process exit codes: the original Python coverage/mutation programs can print failure diagnostics without exiting nonzero. `scripts/crosscheck.py` wraps the recorded checks and rejects unsuccessful summary results. It requires `code/calc`, `code/indep`, Python and NumPy, and stores fresh logs in an ignored local output directory:

```sh
python3 scripts/crosscheck.py
```

The audit did not repeat the historical full `level2` exploration (about 134 billion updates) or establish every statistic in section 8. The preserved historical logs in `runs/` are clearly labelled as upstream evidence. The fresh run summaries are in `audit/2026-10-05/`.
