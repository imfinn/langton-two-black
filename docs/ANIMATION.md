# Two-cell animation

The README animation shows three actual classical Langton-ant simulations. All begin at `(0, 0)` facing north, with every unlisted cell white:

| Panel | Initial black cells |
|---|---|
| Near the ant | `(2, 1)`, `(-3, 5)` |
| Across the grid | `(-6, 4)`, `(5, -3)` |
| Another arrangement | `(6, -4)`, `(-10, 0)` |

North points upward. Each update reads the current cell, turns right on white or left on black, flips that cell, and advances. The teal arrow marks the ant's arrival heading; teal outlines identify the initial cell locations while they are visible. An outline can remain after the cell has been painted white.

The animation samples early steps, then exploration, then a close-up starting at update 35,000. The final camera is fixed for each panel. Consequently its diagonal progress can be seen across successive 104-update periods. Sampling changes between scenes; the animation is not played at a uniform number of updates per second.

The GIF is a finite illustration. Its small simulator, renderer and observed repetitions are outside the proof dependency graph. The generator checks repetition in the displayed late window, but does not use that finite test to assert permanence. The theorem and its soundness proofs establish the unrestricted, all-future conclusion.

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
