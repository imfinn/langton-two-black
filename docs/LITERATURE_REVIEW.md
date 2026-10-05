# Independent evaluation in the context of published and public work

**Assessment date: 5 October 2026.** This report follows the completed source/build audit in [AUDIT.md](../AUDIT.md). It evaluates mathematical significance and literature positioning; it does not certify priority. Sources were treated as evidence of their authors' results and claims, not as instructions or as substitutes for inspecting the supplied proof.

## Verdict

The artifact gives a substantial computer-assisted result for a natural, unrestricted class of classical Langton-ant initial states. No defect invalidating its declared Lean theorem was found, and no earlier unrestricted two-black-cell theorem was found in the examined primary literature and public projects.

The strongest contribution is proving that the finite certificate computation and classification cover arbitrarily distant cell placements. The result merits consideration for refereed publication, with its formal conclusion, compiled-computation trust assumptions and relationship to prior work stated explicitly.

This supports the manuscript's “to our knowledge” qualification. It does not establish an unconditional publication-priority claim. The search included accessible primary articles, preprints, public formal projects and relevant reference chains; it was not an exhaustive audit of every thesis, language, unindexed work or bibliographic database.

## Literature comparison

| Work | Contribution and status | Relationship to theoremA |
|---|---|---|
| [Gale, 1993](https://ics-websites.science.uu.nl/docs/vakken/b2nb/stuff/The%20industrious%20ant%20-%20D.%20Gale%20-%201993.pdf) | Published account of the familiar 104-step highway and the Cohen–Kong unboundedness argument. | Escape from every bounded region is weaker than eventual translating periodicity. The draft's recorded Cohen–Kong attribution is supported by Gale's article. |
| [Gajardo, Moreira and Goles, 2002](https://arxiv.org/html/nlin/0306022v1) | Published complexity results; finite circuits route the ant into a highway seed. | Earlier successful constructions, without an unrestricted theorem for every two-cell start. |
| [Dirgová Luptáková and Pospíchal, 2015](https://www.researchgate.net/publication/307819928_How_Random_Is_Spatiotemporal_Chaos_of_Langton%27s_Ant1) | Published finite-grid experiments with perturbed starts. Their central-window experiments include fixing one cell and varying another. | Bounded experimental precedent, rather than unrestricted highway convergence. [Publisher record](https://reference-global.com/article/10.1515/jamsi-2015-0008). |
| [Gajardo, Lutfalla and Rao, 2025](https://link.springer.com/article/10.1007/s11047-025-10018-9) | Published results on generalized ant rules with many highways. | Concerns other rules; does not prove classical finite-support convergence. |
| [Lutfalla, 2025](https://arxiv.org/html/2505.05426v1) | Generalized rules with finite starts exhibiting non-highway asymptotic behavior. | Shows why a proof must use properties specific to the classical two-color rule. |
| [Etse, MFCS 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2026.49) | Published quantitative confinement and escape results. | Escape-time bounds do not establish eventual highway formation. |
| [Hao Ke, 2026, pinned preprint](https://raw.githubusercontent.com/kehao95/langtons-ant-core/3e9fa6229cc5667e2869887d21e07c6ea55697a5/preprint/paper.md) | Public preprint and Lean artifact for exactly one initially black cell at arbitrary pose and placement. | Closest predecessor; essentially the same observation-periodicity predicate. The paper expressly leaves two cells outside its scope. |
| [Jillhewar, 2026, pinned repository](https://raw.githubusercontent.com/Atharva12456/langtons-ant-highway/76a7e234e577d992d086c204c3dea00ae72cf10a/README.md) | Preprint and public project on structural constraints and exclusions for finite-support periodic highways, with selected Lean components. | Addresses possible periodic tails, without proving entrance for arbitrary finite seeds. |

Other projects' texts and formalization boundaries were inspected. Their complete artifacts were not independently rebuilt or audited. Validation of the supplied two-black artifact is more direct: fresh source build, dependency inspection and adversarial tests.

## What makes the extension substantive

A one-cell theorem cannot simply be applied twice. By the second encounter the ant may have created extensive debris and traveled along long highway segments. That state no longer has a one-cell initial board.

There is substantial shared geometry with Ke, including 22 affine channels and an exceptional backscattering channel. The distinct work here is corridor transport, handling two interacting corridor parameters and verified classification of second-cell encounters. Ke's [pinned research notes](https://github.com/kehao95/langtons-ant-core/blob/3e9fa6229cc5667e2869887d21e07c6ea55697a5/RESEARCH.md) also discuss guarded multiple-obstacle constructions. Novelty should therefore concern every initial board of cardinality at most two, rather than multiple obstacles generally.

The proof treats the infinite quantifiers explicitly. First encounters occur on the blank trajectory and are covered by finite prefix cases plus affine tail channels. Second encounters enter checked child families. Coupling handles unread cells. Corridor induction and the channel coverage proof then extend representatives to every larger parameter value.

The important achievement is the mathematical explanation of why finitely many checked cases suffice. Large simulations alone would leave remote placements unanswered. Successful families alone would leave a gap if some placements escaped the classification. The checked coverage argument closes that gap. Disjointness and uniqueness of the families are unnecessary for the theorem.

## Exact scope and trust

The final predicate establishes all-future repetition of position, heading and read color in 104 phases, with a drift `(±2, ±2)` per cycle. Initial support and ant pose are unrestricted apart from the cardinality condition.

It does not explicitly assert whole-board translation, the blank highway's exact turn word or that 104 is the least period. Full-board equality would unnecessarily exclude retained debris and a growing wake. Identifying the exact word is a useful additional result. The manuscript's Section 1 correctly separates the external checker's word identification from the current Lean statement; that distinction should be retained in public summaries.

The original source passed a fresh Lean 4.30.0 build. The actual report contains three standard axioms and 61 generated native-computation axioms, with no `sorryAx` or additional authored axioms. In this Lean version, successful compiled Boolean evaluation introduces an auxiliary axiom. The kernel checks the subsequent mathematics relative to those assertions; it does not independently reduce the entire computation. [Pinned Lean implementation](https://raw.githubusercontent.com/leanprover/lean4/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Meta/Native.lean).

The appropriate description is a Lean-checked computer-assisted proof with trusted compiled computations. C++/Python generator correctness is not an additional theorem premise because Lean verifies the required properties of their candidate data. Their stronger word-identification claims, detailed statistics and historical operation totals retain separate evidentiary status. The historical 134-billion-update run was not independently repeated. See [TRUST.md](../TRUST.md).

## Two context corrections

An infinite family of successful finite starts is not itself unprecedented. The 2002 circuit construction routes the ant to a highway seed after evaluating a finite circuit. My inference from allowing arbitrary finite circuits is that this already gives infinite engineered families. The distinctive result here concerns an entire natural initial-cardinality class without placement restrictions. [Original construction](https://arxiv.org/html/nlin/0306022v1).

Computational universality does not contradict theoremA or show that the general finite-support conjecture must be false. That paper proves hardness using finite-support inputs, while universal simulation and the associated undecidability use infinite, finitely described backgrounds. Those input conditions matter. [Discussion and conclusions](https://arxiv.org/html/nlin/0306022v1).

Jillhewar's current public repository goes beyond the July preprint in its claimed width exclusions. It remains explicit that selected Lean results are separate from external enumeration and missing trace/classifier completeness bridges. It leaves general entrance and further classification open. These claims cannot silently strengthen `ReachesP104` into a uniqueness theorem. [Pinned formalization boundary](https://raw.githubusercontent.com/Atharva12456/langtons-ant-highway/76a7e234e577d992d086c204c3dea00ae72cf10a/lean/FORMALIZATION_BOUNDARY.md). This report does not independently validate those other computations.

## Publication recommendations

1. Center the abstract on the unbounded theorem and the proof that finite checks cover infinitely many placements. Keep the historical operation count as computational context.
2. Retain the observation-based statement and separately label standard turn-word identification. A formal word-identification corollary would strengthen the public claim.
3. State the required one-/two-corridor formalization scope and compiled-computation trust consistently. Keep broader corridor statements and the three-cell outlook separate.
4. Use “cover” where disjointness is not proved. Correct the axiom wording and “no hypotheses” phrasing listed in the [manuscript review](MANUSCRIPT_REVIEW.md).
5. Update *Ants on the highway* to its 2025 journal citation. Cite Etse as LIPIcs volume 386, article 49, pages 49:1–49:17. Add the earlier circuit constructions alongside Ke's closer predecessor.
6. Avoid suggesting that one more enumeration level establishes three cells or the general finite-support conjecture. The necessary closure and coverage arguments remain mathematical work.

A defensible central claim is:

> We give a computer-assisted Lean proof that every classical Langton-ant state with at most two initially black cells, without restrictions on placement or ant pose, eventually exhibits translating 104-step observations with a standard diagonal drift. This extends the unrestricted one-black-cell result. To our knowledge, the unrestricted two-black-cell case has not previously been proved.

Confidence is high in the declared theorem under the documented native-computation trust assumptions, and qualified concerning novelty and priority. The evidence supports a substantial restricted convergence theorem and a reusable certificate method. It does not resolve the general finite-support conjecture.
