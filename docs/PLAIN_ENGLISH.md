# Why two black cells are enough to make this difficult

The theorem concerns the board at the start. The ant subsequently paints thousands of cells and can build a long trail of old debris. When it eventually meets the second initially black cell, its surroundings can therefore be quite complicated.

A proof for one initially black cell cannot simply be applied twice: the state at the second encounter usually has many black cells.

## An infinite grid needs an infinite argument

Checking every pair of cells in a large box would leave all pairs outside that box unanswered. Even a very long simulation would leave open a late encounter with a distant cell.

The proof instead describes infinite collections of initial boards using a finite set of families. A family parameter measures how much longer a highway corridor is. Two parameters allow two lengths to vary independently. The checker verifies a representative together with geometric conditions that justify every larger member.

## Stretching the journey

Imagine the ant moving along a repeating highway between two regions of debris. Put one more 104-update piece into that stretch. The corridor lemma states exactly how the altered journey follows the original one: each relevant crossing includes the inserted piece, and the surrounding states agree in specified regions, with the appropriate translation and time delay.

The proof checks the board agreements needed for that statement. A repeating position trace alone would not suffice, because a changed cell color could change the next turn.

The succession lemmas show that the conditions survive lengthening. Induction therefore gives a result for every added length. The formal development covers the required single corridors, perpendicular pairs and parallel pairs, including back-and-forth travel.

This is how a finite representative can answer questions about cells a million squares apart, or farther still.

## Accounting for the second cell

Before the first initially black cell is read, the ant follows the blank-board trajectory. Possible first encounters fall into finite prefix cases and 22 infinite affine channels.

After that encounter, the proof asks where the second initially black cell can first affect the run. Its descriptions include cells near debris, cells along a corridor, and cells on a later tail. Each relevant case belongs to a checked child family. A first-read/coupling argument deals with an initial cell that is never encountered.

The important final step is proving that these descriptions cover every relevant placement at every family depth. Lean verifies that coverage argument, so the result does not depend on extending an experimental trend beyond the checked range.

## Why the final repetition lasts

A highway certificate compares one period with its translated successor in a half-plane. The ant's period lies in that region, and the region is preserved in the direction of travel. Coupling and induction prove that the translated observations continue forever.

The conclusion concerns position, heading and the color read. Old debris may remain behind. The exact turn word of the familiar blank-start highway is identified by the external computations and is not an extra conclusion of the current Lean declaration.

## What is new, and what came earlier

The contribution here is the corridor calculus together with a complete classification of second-cell encounters for the unrestricted two-cell case. Half-plane certificates, translating highways, engineered successful seeds and prior one-cell work provide context and foundations. Hao Ke's unrestricted one-black-cell theorem is acknowledged in [ACKNOWLEDGEMENTS.md](../ACKNOWLEDGEMENTS.md).

The work gives a restricted theorem about the classical rule. It does not establish convergence for all finite initial boards, or prove that the same classification extends to three initial cells. The [literature assessment](LITERATURE_REVIEW.md) explains those boundaries.

For exact mathematical statements and source names, read the [proof map](PROOF_MAP.md). For compiler trust, read [TRUST.md](../TRUST.md).
