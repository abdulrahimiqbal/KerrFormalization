# KerrFormalization (early scaffold)

This directory contains the first three Lean modules for the pseudo-Riemannian
linear-algebra layer:

- `KerrFormalization/PseudoRiemannian/BilinearMetric.lean`
- `KerrFormalization/PseudoRiemannian/NondegenerateMetric.lean`
- `KerrFormalization/PseudoRiemannian/Musical.lean`

Compilation was requested during drafting, but this container does not currently
have `lean`, `lake`, or `elan` installed, so no actual `lake build` was possible
here.

The files were tightened against the current Mathlib docs, especially the API for
`LinearMap.BilinForm.Nondegenerate`, `toDual`, `toDual_def`, and
`apply_toDual_symm_apply`.
