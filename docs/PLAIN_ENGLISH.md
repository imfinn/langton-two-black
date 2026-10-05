# How the two-cell proof works

Langton's ant follows a tiny rule: turn right on white, turn left on black, flip the cell, and move forward. The theorem says that, starting with at most two black cells on an otherwise white infinite grid, the ant eventually follows a repeating 104-step pattern along a diagonal. The cells can be anywhere.

The hard part is what happens before that repetition begins. The ant can paint a large area and travel a long way before it reaches the second initially black cell. At that encounter, the board may already contain thousands of black cells. A theorem about starting with one black cell therefore cannot simply be applied a second time.

## How a finite proof covers an infinite grid

There are infinitely many ways to place the two cells. The proof organizes them into families whose members share a common structure. Within a family, a number describes the length of a repeating stretch of highway. In some families, two lengths can vary independently.

The proof checks a starting member and proves a rule for extending it. That rule can be applied again and again, so it covers every larger length. This is how a finite collection of calculations supports a statement about cells a million squares apart, or farther still.

## Lengthen a repeating stretch

Imagine the ant traveling along a repeating highway between two regions it has already painted. Insert one more 104-step piece into that stretch. The proof must explain how this altered route connects to the rest of the journey.

The corridor lemma answers that question. Each relevant crossing includes the extra piece. The journey before and after the crossing still matches the original journey in the required regions, with a shift in position and a delay in time. The proof checks the cell colors as well as the ant's route, because a different color would change its next turn.

The next step is showing that the same conditions hold after the extension. The argument can then be repeated for every longer corridor. It also accounts for journeys back and forth and for two corridors that run parallel or meet at right angles.

## Find every place the second cell can matter

Until the ant reads an initially black cell, it follows exactly the walk it would take on a blank board. The proof uses that walk to classify the possible first encounters: an early part of the journey and 22 repeating channels extending into the distance.

After the first encounter, the question becomes where the second cell can change the journey. It might be near an area already painted, along a corridor, or farther down a highway. These encounters lead to further families of journeys.

The classification must cover every possible encounter for every corridor length. The proof establishes that coverage, connecting the checked cases to all possible placements. It also handles a cell that the ant never reaches: an unread cell cannot change any of the ant's turns.

## Show that repetition continues forever

Finding a repeated segment is the beginning of the final argument. To prove that the repetition lasts, the proof compares the cells in a segment with those in its shifted successor.

The comparison takes place on one side of a straight line, a region called a half-plane. The ant stays in that region during the segment, and the direction of travel preserves the agreement needed for the next segment. Applying the argument repeatedly proves that the same movement and encountered colors continue for every future cycle.

## What the theorem says

After some finite time, the ant's position, facing direction, and the color it reads repeat every 104 steps, with its position advancing two rows and two columns along one of the four diagonals. The ant may leave old debris behind and keep adding to its painted trail.

The formal statement specifies that repetition and advance. It does not specify the exact sequence of turns in the familiar highway from an all-white start; identification of that sequence comes from separate computational checks. It also does not assert that 104 is the shortest possible period.

The theorem covers zero, one, or two initially black cells. The question for arbitrary finite initial patterns, including a general guarantee for three cells, remains open.

## The contribution and its context

The central ideas are the rules for extending corridors and the complete classification of second-cell encounters. Together, they settle the two-cell case without any restriction on cell placement or the ant's starting position and direction.

[Hao Ke's earlier one-black-cell theorem](../ACKNOWLEDGEMENTS.md) is the closest predecessor. Translating highways, half-plane arguments, and constructions of successful starting patterns provide further context. To our knowledge, the unrestricted two-black-cell case has not previously been proved. The [research review](LITERATURE_REVIEW.md) discusses the earlier work.

Lean checks the mathematical arguments in this development. The finite calculations run as compiled Lean programs, so accepting their results also relies on Lean's compiler and runtime. The [verification report](../AUDIT.md) documents the checks; the [trust explanation](../TRUST.md) gives the technical details.

For the mathematical statements and their Lean source locations, see the [proof map](PROOF_MAP.md).
