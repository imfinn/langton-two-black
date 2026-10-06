# Changes in manuscript revision 5

Revision 5, dated 5 October 2026, incorporates the independent artifact audit and literature assessment into the mathematical exposition. The [revised manuscript](TWO_BLACK_CELLS_REVISED.md) is the current reading copy. The [original revision 4](TWO_BLACK_CELLS.md) remains byte-for-byte unchanged.

**The theorem, all original Lean sources and the checked data are unchanged.** This revision corrects the description of the result and its evidence; it does not claim a new proof run or an extension to three cells.

| Correction | Where to find it |
|---|---|
| State permanent repetition of position, arrival heading and read colour with one of the four diagonal drifts; distinguish whole-board translation, the exact turn word and least period. | Abstract; §1; §§10.1, 10.4 |
| Retain the `AtMostTwoBlack` premise and say “no remaining auxiliary hypotheses”, rather than “no hypotheses”. | Abstract; §9.1 |
| Report all three standard and 61 native-computation axioms together. Explain that the kernel checks ordinary proofs relative to the compiled-computation assertions. | §§9.1, 10.2 |
| Restrict the claimed formal family induction to the required one- and two-corridor cases; retain arbitrary switch count for the corridor lemma. | Abstract; §§1, 2.2, 5, 9.1 |
| Make strict separation of switch windows explicit as (C6); include the initial relation in the corridor hypotheses. | §§3–5 |
| Describe the time formula as a transferred, sufficient certificate time, without a claim of earliest entry. | §§4–5 |
| Distinguish the stronger external checker conditions from the sufficient Lean variants, including the weaker parallel hypothesis. | §§2.1, 3, 5, 9.2 |
| State the concrete-table result as coverage, and the channel-ray result as containment. Exact table agreement is separately reproduced computational evidence. | §§8.2, 9.1 |
| Explain that child classification supplies at least one covering family; uniqueness and disjointness are not formal conclusions. | §§6.1, 8.2, 9.1 |
| Specify that a second cell is “later” when unread through the first cell's encounter. An unread cell preserves observations, although its board colour differs. | §§7, 9.1 |
| Label the historical large-run statistics and discovery claims; list fresh builds, mutations and independent checks separately. | §§8, 9.2–9.3 |
| Add clean-build, literal `#print axioms theoremA`, mutation-test and regeneration instructions, including the generator repairs. | §§9.3–9.4 |
| Separate theorem correctness, native/compiler trust, reproducibility, external cross-checks and literature claims. | §10 |
| Update the 2025 journal citation for *Ants on the highway*, correct Etse's volume/article citation, and add earlier circuit constructions. Retain Ke's prior one-cell acknowledgement and qualified novelty wording. | §1; References |
| Describe the three-cell and general finite-support outlook as proposals requiring further mathematical proofs. Distinguish the input conditions of universality results. | §11 |

The [97-row manuscript comparison](../docs/MANUSCRIPT_REVIEW.md) continues to refer to the original revision-4 lines, so its audit record remains interpretable. The [independent literature assessment](../docs/LITERATURE_REVIEW.md), [AUDIT.md](../AUDIT.md) and [TRUST.md](../TRUST.md) retain the underlying evidence and qualifications. No historical log has been relabelled as a newly run validation.
