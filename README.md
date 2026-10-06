# Two black cells. Anywhere.

**A computer-assisted proof for classical Langton's ant, checked with Lean.**

> **Every start with at most two black cells eventually repeats a 104-step pattern along a diagonal.**
>
> Start with an otherwise white, infinite square grid. Place the black cells anywhere, and put the ant at any position, facing any direction. Eventually, its directions and the colors it encounters repeat every 104 steps. With each repetition, the ant advances **two rows and two columns along one of the four diagonals**.
>
> **There is no bound on how far apart the cells may be.**

```lean
theorem TwoBlack.theoremA :
  ∀ s, AtMostTwoBlack s → ReachesP104 s
```

[Read the paper](paper/TWO_BLACK_CELLS_REVISED.md) · [How the proof works](docs/PLAIN_ENGLISH.md) · [Research context](docs/LITERATURE_REVIEW.md)

![Three Langton-ant simulations beginning with two black cells at different positions, followed by close-ups of their translating highway cycles.](docs/assets/two-black.gif)

*Three starting arrangements, three journeys into diagonal repetition. Teal outlines mark the initial black cells; the teal arrow follows the ant. The animation jumps ahead between scenes. [Static preview](docs/assets/two-black.png) · [About the animation](docs/ANIMATION.md).*

## The rule

On a white cell, turn right. On a black cell, turn left. Flip the cell's color, then move forward one square. These two rules can produce a long, complicated journey before the repeating diagonal motion begins. “Two black cells” describes the initial board; the ant keeps painting cells as it moves.

## Why two cells matter

By the time the ant reaches the second black cell, it may have painted a large area and traveled far from its starting point. The second cell can then alter a journey already in progress. A proof has to account for that history and for every possible distance between the initial cells.

[Hao Ke's earlier theorem](ACKNOWLEDGEMENTS.md) established the unrestricted one-black-cell case. This result extends the guarantee to two cells. The broader question—whether every finite initial pattern eventually produces a repeating diagonal highway—remains open. The [research context](docs/LITERATURE_REVIEW.md) explains how this result fits into earlier work.

## The ideas behind the proof

**Extend a corridor.** Parts of the ant's journey follow a repeating highway between regions it has already painted. The proof shows how to lengthen such a corridor by one 104-step block and account for the extra steps on each crossing. Repeating that argument covers corridors of arbitrary length, including return trips and pairs of interacting corridors.

**Cover every second-cell encounter.** The second cell can affect the ant near its earlier trail, along a corridor, or farther along a highway. The proof groups these possibilities into families, each covering many placements, and shows that the families cover every placement that can change the walk. It also handles cells the ant never visits.

**Make the repetition permanent.** Once a repeating segment is found, the proof checks that the cells ahead give the same turns on the next segment. A geometric argument shows why that agreement continues with every repetition, however far the ant travels.

The corridor arguments and the complete treatment of the second cell are the central ideas behind this extension. The [plain-English explanation](docs/PLAIN_ENGLISH.md) develops them step by step.

## The repeating pattern

The repeating pattern describes the ant's movement, facing direction, and the colors it encounters. Its painted trail can keep growing, with earlier debris left behind. The formal theorem establishes a 104-step repetition and the diagonal advance. The precise sequence of turns in the familiar highway from an all-white start is discussed separately in the [theorem guide](docs/PLAIN_ENGLISH.md#what-the-theorem-says).

## Check the proof

The proof combines mathematical arguments about infinitely many placements with calculations that check a finite collection of cases. Lean checks the mathematical arguments, and the calculations run as compiled Lean programs. Those calculations rely on Lean's compiler and runtime. The [verification report](AUDIT.md) and [technical trust explanation](TRUST.md) give the full details.

To check the result yourself, install [elan](https://github.com/leanprover/elan), Python 3, and a working C compiler, then run:

```sh
git clone https://github.com/imfinn/langton-two-black.git
cd langton-two-black
elan toolchain install leanprover/lean4:v4.30.0
bash ./scripts/validate.sh --clean
```

This builds the proof, prints its logical assumptions, and runs tests that deliberately corrupt the check data to confirm that the checkers reject those changes. The recorded clean build took about 91 minutes; build time varies by machine.

The proof uses **Lean 4.30.0 with no external Lean packages**. All required proof data are included. [Reproduction instructions](REPRODUCIBILITY.md) also cover data generation, independent simulations, and the manual GitHub Actions validation workflow.

## Read further

| Read | What you will find |
|---|---|
| [Paper](paper/TWO_BLACK_CELLS_REVISED.md) | The revised manuscript, incorporating the audit and literature review |
| [How the proof works](docs/PLAIN_ENGLISH.md) | An accessible explanation of the main ideas |
| [Research context](docs/LITERATURE_REVIEW.md) | Earlier results, the contribution here, and questions still open |
| [Formal proof](lean/TwoBlack/Main.lean) and [proof map](docs/PROOF_MAP.md) | The Lean theorem and the arguments it depends on |
| [Verification report](AUDIT.md) and [trust explanation](TRUST.md) | What was checked and the assumptions needed to accept the result |
| [Manuscript review](docs/MANUSCRIPT_REVIEW.md) | Comparison with the original manuscript and the corrections now incorporated |
| [Reproduction instructions](REPRODUCIBILITY.md) | Build commands, data generators, tests, and recorded evidence |

[Original manuscript](paper/TWO_BLACK_CELLS.md) · [Manuscript revision notes](paper/REVISION_NOTES.md)

[Acknowledgements and references](ACKNOWLEDGEMENTS.md) · [Source provenance and licensing](PROVENANCE.md)
