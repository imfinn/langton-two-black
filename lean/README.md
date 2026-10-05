# Read and check the formal proof

The proof uses Lean 4.30.0 and its bundled core/Std libraries. All required proof data are included in this directory.

The main theorem is:

```lean
theorem TwoBlack.theoremA :
  ∀ s, AtMostTwoBlack s → ReachesP104 s
```

It says that every initial state with at most two black cells eventually has a repeating 104-step walk with diagonal advance. The cells and the ant can start anywhere, and the ant can face any direction.

Start with [the theorem declaration](TwoBlack/Main.lean) or follow the argument through the [proof map](../docs/PROOF_MAP.md). [Reproduction instructions](../REPRODUCIBILITY.md) explain how to build the proof and regenerate its data. The [trust explanation](../TRUST.md) describes the role of compiled computations.

The [original project README](../docs/ORIGINAL_LEAN_README.md) is also available.
