# Fresh independent evidence, 5 October 2026

These records were generated during this audit from the supplied source and independently rerun programs. Historical upstream records are kept separately in `../../runs/`.

- `clean-build.log`, `clean-build-meta.json`: original source in a fresh extraction, no project build artifacts; 261 jobs, exit 0.
- `theoremA-axioms.out`, `axioms.json`, `native-groups.json`: actual requested axiom report and independently matched groups.
- `axioms-all.out`, `generic-axioms.out`, `extra-axioms.out`: deeper soundness and assembly dependency reports.
- `lean-tests-meta.json`, mutation logs: original and added Lean assertions; empty Lean logs mean all asserted examples elaborated without diagnostics.
- `cpp-*`, `fresh-*`, `indep_family-*`, `mutation_test-*`, `python-tests-meta.json`: independent finite reruns and order-normalized dump comparisons.
- `regen-comparison.json`, `original-generator-*`: reproduction defects in the supplied generators.
- `maintained-*`, `maintainer-verification.json`: actual checks after the documented helper/portability repairs. The helper harness reused the independently fresh source build; it was not a second clean build.
- `original-files.json`, `preservation.json`: supplied file hashes and proof/paper preservation.
- `literature-checks.json`, `ke-tree.json`: limited primary-source inspection, not an exhaustive priority certificate.

Temporary paths identify this run; follow `../../REPRODUCIBILITY.md` to create new local outputs. Included logs are evidence to inspect, never inputs to the Lean theorem.
