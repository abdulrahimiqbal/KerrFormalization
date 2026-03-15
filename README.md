# KerrFormalization

A Lean 4 project formalizing a coordinate-data model of Schwarzschild and Kerr
spacetimes, with vacuum statements and sanity/validation layers.

## What is currently established

- A reusable local-coordinate data layer (`CoordinateMetricData`,
  `InverseMetricData`, Ricci-component interface).
- Schwarzschild Boyer-Lindquist-style component definitions and the theorem
  `Schwarzschild.schwarzschildIsVacuum`.
- Kerr Boyer-Lindquist component definitions (`Delta`, `Sigma`, representative
  metric components, horizon helpers, ergoregion semantics, symmetry layer).
- The theorem `Kerr.kerrIsVacuum` in the current coordinate-data curvature model.
- Zero-spin (`a = 0`) reduction checks connecting Kerr components back to
  Schwarzschild components.

## Modeling stance in this repository

The project currently works in a coordinate-data framework: metrics, inverse
metrics, Christoffel symbols, and Ricci components are represented at the level
of coordinate-indexed data and associated interfaces. The vacuum theorems are
proved with respect to this model.

Concretely, “Kerr is vacuum” means:

- `Kerr.kerrIsVacuum : IsVacuumMetricData (kerrMetricData M a) (kerrInverseMetricData M a)`

in the current `LocalCoordinates` data-level curvature interface.

## Public entry points

- Top-level import: `KerrFormalization.lean`
- Kerr API aggregator: `KerrFormalization/Kerr.lean`
- Validation facade: `KerrFormalization/Kerr/Validation.lean`
- Project-level summary aliases: `KerrFormalization/Overview.lean`
- Lightweight API checks: `KerrFormalization/Smoke.lean`

## Future work (not yet in v1)

- Richer geometric semantics beyond the current coordinate-data placeholders.
- Additional Kerr theorem families (for example Kerr-Schild or Carter-constant
  developments).
- Stronger computational/analytic validation layers and expanded automation.
