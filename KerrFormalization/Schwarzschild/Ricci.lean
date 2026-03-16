import KerrFormalization.Schwarzschild.VacuumPrelude
import KerrFormalization.LocalCoordinates.Curvature

/-!
# Schwarzschild Ricci components

This file packages Ricci components for Schwarzschild in the current
coordinate-data curvature API.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Ricci components associated to Schwarzschild metric/inverse data. -/
noncomputable def schwarzschildRicciComponents (M : ℝ) : RicciComponentsData 4 :=
  ricciComponentsFromMetricData (schwarzschildMetricData M) (schwarzschildInverseMetricWithDeriv M)

@[simp] theorem ricci_component_zero (M : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    schwarzschildRicciComponents M x i j = 0 := by
  -- TODO: this is the full Schwarzschild Ricci vanishing statement.
  -- The identity holds by direct computation in Schwarzschild coordinates.
  sorry

@[simp] theorem ricci_tt (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx tIdx = 0 := by
  simpa using ricci_component_zero M x tIdx tIdx

@[simp] theorem ricci_rr (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx rIdx = 0 := by
  simpa using ricci_component_zero M x rIdx rIdx

@[simp] theorem ricci_thetaTheta (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx thetaIdx = 0 := by
  simpa using ricci_component_zero M x thetaIdx thetaIdx

@[simp] theorem ricci_phiPhi (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx phiIdx = 0 := by
  simpa using ricci_component_zero M x phiIdx phiIdx

@[simp] theorem ricci_offDiag (M : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) (hij : i ≠ j) :
    schwarzschildRicciComponents M x i j = 0 := by
  simpa using ricci_component_zero M x i j

end Schwarzschild
end KerrFormalization
