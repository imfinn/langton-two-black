# Two-cell animation

The animation follows three ants from different two-cell starting arrangements into repeating diagonal motion. Each ant starts at `(0, 0)` facing north, on an otherwise white grid:

| Panel | Initial black cells |
|---|---|
| Near the ant | `(2, 1)`, `(-3, 5)` |
| Across the grid | `(-6, 4)`, `(5, -3)` |
| Another arrangement | `(6, -4)`, `(-10, 0)` |

North points upward. Each ant turns right on white or left on black, flips the cell, and moves forward. The teal arrow shows its position and facing direction. Teal outlines mark where the two black cells began, even after the ant has changed their colors.

First you see the early steps, then a later part of the exploration, and finally a close-up beginning at step 35,000. The animation jumps ahead between scenes. In the close-up, the camera stays still while the ant advances along its highway, one 104-step cycle at a time.

These three examples illustrate the theorem. The proof explains why the eventual repetition lasts forever and covers every placement of up to two initial black cells. The animation's simulator is separate from that proof.

## Regenerate

The optional renderer requires Python 3.9 or newer and Pillow. It has no effect on the Lean build.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r docs/animation-requirements.txt
.venv/bin/python scripts/render_animation.py
```

Outputs:

- `docs/assets/two-black.gif`: the animated README image.
- `docs/assets/two-black.png`: a static initial-state preview.
- `docs/assets/animation.json`: seeds, sampled times, observed late-window drifts and file hashes.

The renderer uses an installed DejaVu Sans, Liberation Sans, Arial or Vera font, with a Pillow fallback. Pixel output may differ across platforms because fonts and rendering libraries differ. The simulation rule and sample times are fixed.

The original independent Python checker can also reproduce the sampled states through `code/indep_family.py`'s `run` and `snapshots` functions. That comparison was performed during publication preparation.
