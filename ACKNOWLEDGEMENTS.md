# Acknowledgements and related work

Hao Ke proved the prior exactly-one-black-cell result for classical Langton's ant with arbitrary ant position and heading. His development is available in [langtons-ant-core](https://github.com/kehao95/langtons-ant-core), with the [one-black theorem and artifact at the inspected commit](https://github.com/kehao95/langtons-ant-core/tree/3e9fa6229cc5667e2869887d21e07c6ea55697a5/one_black).

Ke's repository gives this citation:

> Hao Ke. *Every One-Black-Cell Langton Ant Reaches the Period-104 Highway: A Lean-Checked Proof.* Zenodo, 2026. [doi:10.5281/zenodo.22086968](https://doi.org/10.5281/zenodo.22086968).

The citation is independently corroborated by [Ke's pinned README](https://github.com/kehao95/langtons-ant-core/blob/3e9fa6229cc5667e2869887d21e07c6ea55697a5/README.md). The DOI's landing-page metadata was not retrievable in this audit, so its details are attributed to the author's repository.

The two-black development supplies its own `one_black` proof through corridor families. Its arrival-heading convention, RL update rule, and eventual translating observation predicate agree in substance with [Ke's pinned Semantics.lean](https://github.com/kehao95/langtons-ant-core/blob/3e9fa6229cc5667e2869887d21e07c6ea55697a5/one_black/lean/OneBlack/Semantics.lean). This audit inspected those definitions; it did not rebuild Ke's proof or establish a formal cross-project equivalence theorem. Acknowledgement does not imply his endorsement of this artifact.

The supplied draft also cites earlier finite-grid experiments and work constraining possible highways or escape times. Such results and historical/novelty claims are outside the Lean statement. The audit performed only a limited primary-source search, so this repository does not strengthen the draft's “to our knowledge” wording.

A bibliographic clarification: the draft's Etse reference is article 49 in LIPIcs volume 386, pages 49:1–49:17, MFCS 2026. The [publisher record](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2026.49) supplies DOI `10.4230/LIPIcs.MFCS.2026.49`. Writing “LIPIcs 49” alone is ambiguous; the original draft is preserved, and the [revised manuscript](paper/TWO_BLACK_CELLS_REVISED.md) incorporates the corrected citation.

The archive did not provide author/maintainer metadata or an explicit license for this artifact. This repository preserves that provenance and does not invent attribution or a license grant. See [PROVENANCE.md](PROVENANCE.md).

The later [independent literature assessment](docs/LITERATURE_REVIEW.md) extends the context review, while retaining qualified novelty wording. It distinguishes earlier circuit constructions ending in highways, bounded experiments, generalized-rule results and conditional constraints on periodic traces from the unrestricted two-cell theorem. *Ants on the highway* was published in *Natural Computing* 24, 497–509 (2025), [doi:10.1007/s11047-025-10018-9](https://link.springer.com/article/10.1007/s11047-025-10018-9); the preserved draft lists its 2024 preprint, while the revised manuscript includes the journal citation and earlier circuit constructions.
