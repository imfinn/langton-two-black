# Provenance

This repository preserves the supplied `langton_two_black_lean.zip` and accompanying revision-4 draft dated 5 October 2026. The draft supplied separately was byte-identical to the copy in the archive.

| Supplied input | SHA-256 |
|---|---|
| `langton_two_black_lean.zip` | `76d7165e470d298e95bdbefaf8c1f09e51615c931649ac8bf3441fad5e46e3f4` |
| `TWO_BLACK_CELLS (2).md` | `031d56f6b35ef79b270c5e3935556f1acb7e0a0b7b6d19fe6b839d3e64b3fce4` |

All 89 original Lean files, the toolchain/configuration, and the manuscript are preserved byte-for-byte. The original README files are retained under `docs/ORIGINAL_README.md` and `docs/ORIGINAL_LEAN_README.md`. Generator/portability repairs are itemized in [AUDIT.md](AUDIT.md).

The [revised manuscript (revision 5)](paper/TWO_BLACK_CELLS_REVISED.md), independent audit, literature assessment, documentation, validation helpers, and illustrative animation were prepared in the accompanying Codex-assisted audit and publication session. They are separate from the original proof and manuscript. The revised manuscript incorporates the audit and literature corrections without changing any Lean source or check data; its [revision notes](paper/REVISION_NOTES.md) explain the differences. The original artifact did not supply author metadata or an explicit license. Publication under the repository owner's account does not establish authorship of the proof or add a license grant.

## Evidence labels

- `paper/TWO_BLACK_CELLS.md` is the original revision 4; `paper/TWO_BLACK_CELLS_REVISED.md` is the corrected reading copy.
- `audit/2026-10-05/` contains fresh results produced by the independent audit.
- `runs/` contains supplied historical records and raw inputs for regeneration.
- `docs/assets/` contains finite illustrative simulations generated for the README.
- The Lean theorem build consumes the literal data included in the Lean source. It does not execute the upstream C++/Python generators, replay the animation, or accept a build log as a proof.

The dated audit records the initial validated artifact. Later documentation or presentation changes do not change that recorded run. Third parties should produce their own clean-build logs with `scripts/validate.sh --clean`.

## Citation

For now, cite the manuscript title and revision date, together with this repository URL and a commit identifier. Author attribution and a publication DOI can be added when supplied. Cite Hao Ke's earlier one-black-cell result as recorded in [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md).
