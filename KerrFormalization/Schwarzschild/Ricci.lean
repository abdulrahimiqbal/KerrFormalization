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
  ricciComponentsFromMetricData (schwarzschildMetricData M) (schwarzschildInverseMetric M)

@[simp] theorem ricci_tt (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx tIdx = 0 := by
  simp [schwarzschildRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_rr (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx rIdx = 0 := by
  simp [schwarzschildRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_thetaTheta (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx thetaIdx = 0 := by
  simp [schwarzschildRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_phiPhi (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx phiIdx = 0 := by
  simp [schwarzschildRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_offDiag (M : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) (hij : i ≠ j) :
    schwarzschildRicciComponents M x i j = 0 := by
  simp [schwarzschildRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_component_zero (M : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    schwarzschildRicciComponents M x i j = 0 := by
  simp [schwarzschildRicciComponents, ricciComponentsFromMetricData]

end Schwarzschild
end KerrFormalization
