import KerrFormalization.Kerr.Ricci
import KerrFormalization.LocalCoordinates.Vacuum

/-!
# Kerr vacuum theorem

This file records vacuum statements for Kerr in the current coordinate-data
layer.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Every Kerr Ricci component vanishes in the current data-level curvature model. -/
theorem kerrRicciZero (M a : ℝ) (x : CoordinateSpace 4) (μ ν : Fin 4) :
    kerrRicciComponents M a x μ ν = 0 := by
  exact ricci_component_zero M a x μ ν

/-- Kerr is vacuum in the current coordinate-data framework. -/
theorem kerrIsVacuum (M a : ℝ) :
    IsVacuumMetricData (kerrMetricData M a) (kerrInverseMetricWithDeriv M a) := by
  intro x μ ν
  exact kerrRicciZero M a x μ ν

end Kerr
end KerrFormalization
