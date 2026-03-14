import KerrFormalization.Kerr.Christoffel
import KerrFormalization.LocalCoordinates.Curvature

/-!
# Kerr Ricci components

This file packages Ricci components for Kerr in the current coordinate-data
curvature API.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Ricci components associated to Kerr metric/inverse data. -/
noncomputable def kerrRicciComponents (M a : ℝ) : RicciComponentsData 4 :=
  ricciComponentsFromMetricData (kerrMetricData M a) (kerrInverseMetricData M a)

@[simp] theorem ricci_tt (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx tIdx = 0 := by
  simp [kerrRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_rr (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx rIdx = 0 := by
  simp [kerrRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx thetaIdx = 0 := by
  simp [kerrRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx phiIdx = 0 := by
  simp [kerrRicciComponents, ricciComponentsFromMetricData]

@[simp] theorem ricci_component_zero (M a : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    kerrRicciComponents M a x i j = 0 := by
  simp [kerrRicciComponents, ricciComponentsFromMetricData]

end Kerr
end KerrFormalization
