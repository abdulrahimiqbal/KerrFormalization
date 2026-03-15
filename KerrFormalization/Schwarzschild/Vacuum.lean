import KerrFormalization.Schwarzschild.Ricci
import KerrFormalization.LocalCoordinates.Vacuum

/-!
# Schwarzschild vacuum theorem

This file records vacuum statements for Schwarzschild in the current
coordinate-data layer.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Every Schwarzschild Ricci component vanishes in the current data-level curvature model. -/
theorem schwarzschildRicciZero (M : ℝ) (x : CoordinateSpace 4) (μ ν : Fin 4) :
    schwarzschildRicciComponents M x μ ν = 0 := by
  exact ricci_component_zero M x μ ν

/-- Schwarzschild is vacuum in the current coordinate-data framework. -/
theorem schwarzschildIsVacuum (M : ℝ) :
    IsVacuumMetricData (schwarzschildMetricData M) (schwarzschildInverseMetric M) := by
  intro x μ ν
  exact schwarzschildRicciZero M x μ ν

end Schwarzschild
end KerrFormalization
