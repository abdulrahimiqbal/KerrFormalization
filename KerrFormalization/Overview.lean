import KerrFormalization.Kerr.Validation
import KerrFormalization.Schwarzschild

/-!
# Project overview surface

This module provides a compact, public-facing summary of what the current
formalization establishes.

It intentionally re-exports established results without changing scope.
-/

namespace KerrFormalization

open LocalCoordinates

/-- Public alias: Kerr is vacuum in the current coordinate-data curvature model. -/
theorem kerrIsVacuum_v1 (M a : ℝ) :
    IsVacuumMetricData (Kerr.kerrMetricData M a) (Kerr.kerrInverseMetricData M a) :=
  Kerr.kerrVacuumValidated M a

/-- Public alias: Schwarzschild is vacuum in the same coordinate-data model. -/
theorem schwarzschildIsVacuum_v1 (M : ℝ) :
    IsVacuumMetricData (Schwarzschild.schwarzschildMetricData M)
      (Schwarzschild.schwarzschildInverseMetric M) :=
  Schwarzschild.schwarzschildIsVacuum M

end KerrFormalization
