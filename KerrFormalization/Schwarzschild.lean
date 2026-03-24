import KerrFormalization.Schwarzschild.Basic
import KerrFormalization.Schwarzschild.Metric
import KerrFormalization.Schwarzschild.InverseMetric
import KerrFormalization.Schwarzschild.Christoffel
import KerrFormalization.Schwarzschild.ComponentLemmas
import KerrFormalization.Schwarzschild.VacuumPrelude

/-!
# Schwarzschild public surface

Aggregator for Schwarzschild coordinate-data definitions, components,
and foundational curvature-prelude data.

The exact Phase I metric/inverse definitions now flow through the exact module
pair `Schwarzschild.MetricExact` and `Schwarzschild.InverseMetricExact`, while
this file keeps the compatibility re-exports used elsewhere in the repository.

STATUS (March 2026): Ricci/vacuum modules are intentionally not re-exported
from this public surface because their Ricci-component proofs are incomplete.
-/
