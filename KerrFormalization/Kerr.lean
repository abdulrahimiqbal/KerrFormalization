import KerrFormalization.Kerr.Basic
import KerrFormalization.Kerr.BoyerLindquist
import KerrFormalization.Kerr.InverseMetric
import KerrFormalization.Kerr.ComponentLemmas
import KerrFormalization.Kerr.Horizons
import KerrFormalization.Kerr.Symmetries
import KerrFormalization.Kerr.Ergoregion
import KerrFormalization.Kerr.Christoffel
import KerrFormalization.Kerr.Sanity
import KerrFormalization.Kerr.ReductionToSchwarzschild
import KerrFormalization.Kerr.Validation

/-!
# Kerr public surface

Aggregator for the Kerr coordinate-data development:
- Boyer-Lindquist definitions and metric components
- inverse metric, symmetry, and validation layers
- symmetry, horizon, ergoregion, and zero-spin reduction checks
- validation-friendly re-exports

STATUS (March 2026): Ricci/vacuum modules exist but are intentionally not
re-exported from this public surface because their component proofs are
incomplete.
-/
