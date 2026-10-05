# Two black cells, revision 4: paper, Lean formalization, checkers and runs

## Contents

- `paper/TWO_BLACK_CELLS.md` is the paper, revision 4. §6.1 gives the one-step proof of Lemma 6.3 used by Lean, §9 covers the Lean formalization and §10 the trust boundary.
- `lean/` is the Lean 4 project (Lean 4.30.0, core library only). Its `README.md` lists the main theorems.
- `code/` holds the C++ checker, the independent Python checkers, the independent detector and the Lean data generators.
- `runs/` holds every output referenced in the paper.

## What is formally verified (Lean, no `sorry`)

- **General lemmas:**
  - Lemma 2.1 (coupling) and Lemma 2.2 (half-plane certificate ⇒ highway);
  - Lemma 4.1 (the corridor lemma);
  - all of Lemma 5.1, parts (a), (b) and (c);
  - Proposition 5.2 for one corridor and for two corridors, perpendicular or parallel;
  - Lemma 6.1 (tail descent), Lemma 6.3 for parents without a corridor, and Lemma 6.4 with Corollary 6.5 (the one-step lemma behind Lemma 6.3 for the channel parents);
  - translation and rotation invariance;
  - soundness of executable checkers for one- and two-corridor families.
- **One black cell:** `one_black : ∀ s, ExactlyOneBlack s → ReachesP104 s`. This is an independent proof of Ke's theorem.
- **Two black cells (Theorem A):** `theoremA : ∀ s, AtMostTwoBlack s → ReachesP104 s`, with **no hypotheses**.

  What is not proved in general is discharged by verified computation (`native_decide`):
  - the 2,432 concrete parents, about 4.5 million certificate searches and 53,504 families;
  - the 45,452 one-parameter, 286 perpendicular and 220 parallel channel children, with their 572 slab families;
  - the partition check (Lemma 6.3) on member 40 of each of the 22 channel parents.

  `runs/axioms.out` shows that `theoremA` depends only on `propext`, `Quot.sound` and `Classical.choice`, plus the `native_decide` computation axioms. The C++ and Python code is not part of the trust base: it generates hints and child lists, and Lean verifies everything it uses.

## Reproducing

**C++ and Python** (as in revision 2):
```sh
cd code && g++ -O2 -march=native -o calc calculus.cpp && g++ -O2 -o indep indep.cpp
XVAL=1 ./calc level1
XVAL=1 ONLY=0 ./calc level2                    # family half
XVAL=1 NSHARD=2 SHARD=0 ONLY=1 ./calc level2   # concrete half, shard 0 of 2 (repeat with SHARD=1)
REPS=30 ./calc covertest                       # Lemma 6.3 coverage, in C++
STRIDE=16 ./calc childdump > childdump.txt
python3 indep_cover.py childdump.txt 80        # independent coverage test (exact integer solver)
python3 mutation_test.py childdump.txt 20      # mutation test of the coverage checker
python3 indep_family.py famdump2.txt           # independent family checker (dump file as argument)
./indep file ../runs/v2_dump.txt               # independent highway detector
```

**Lean:**
```sh
./calc leandump > leandump.txt && python3 gen_lean_parents.py leandump.txt ../lean 32
./calc chandump > chandump.txt && python3 gen_lean_channels.py chandump.txt ../lean
python3 gen_lean_part.py chandump.txt ../lean    # partition hints; replays the check in Python first
cd ../lean && lake build && lake env lean Axioms.lean
```
The generated data files are already included. A full `lake build` takes about 19 CPU-hours, about 10 hours on 2 cores. Most of that is the 2,432 concrete parents; the partition check for the channel parents takes about 25 seconds. The one-black part takes about a minute (`lake build TwoBlack.General`).

`lake build TwoBlack.PartMut` runs the mutation test of the partition check. The build logs, the axiom audit and the partition replay (`gen_lean_part.out`) are in `runs/`.
