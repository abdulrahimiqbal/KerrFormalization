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

STATUS (March 2026): Ricci/vacuum modules are intentionally not re-exported
from this public surface because their Ricci-component proofs are incomplete.
-/
