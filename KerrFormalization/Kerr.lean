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
import KerrFormalization.Kerr.KillingTensor
import KerrFormalization.Kerr.Geodesic
import KerrFormalization.Kerr.Conservation

/-!
# Kerr public surface

Aggregator for the Kerr coordinate-data development.

The exact Phase I metric/inverse definitions now flow through the exact module
pair `Kerr.BoyerLindquistExact` and `Kerr.InverseMetricExact`, while this file
keeps the compatibility re-exports that the rest of the repository uses.

STATUS (March 2026): Ricci/vacuum modules exist but are intentionally not
re-exported from this public surface because their component proofs are
incomplete.
-/
