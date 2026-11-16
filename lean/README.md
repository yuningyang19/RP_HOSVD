# Lean proofs

This directory contains Lean statements and proofs for the paper's numbered results. See [COVERAGE.md](COVERAGE.md) for the correspondence between the paper and Lean modules.

With elan installed, run from this directory:

```sh
lake exe cache get
lake build
python3 scripts/check_targets.py
```

Lean and Mathlib versions are specified in `lean-toolchain` and `lake-manifest.json`. `RPHOSVD.lean` imports the proof modules; `Audit.lean` checks their theorem types and axioms.

The convention is τ² = sum of the discarded squared singular values. Lean indices are zero based. [MixedNotes.md](MixedNotes.md) describes the arithmetic models used by the mixed-precision and backward-error results.
