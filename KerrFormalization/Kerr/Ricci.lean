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
  ricciComponentsFromMetricData (kerrMetricData M a) (kerrInverseMetricWithDeriv M a)

@[simp] theorem ricci_tt (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx tIdx = 0 := by
  -- TODO: this is the real Kerr Ricci (t,t) component identity.
  -- The identity holds by direct computation in Boyer-Lindquist coordinates.
  sorry

@[simp] theorem ricci_rr (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx rIdx = 0 := by
  -- TODO: this is the real Kerr Ricci (r,r) component identity.
  -- The identity holds by direct computation in Boyer-Lindquist coordinates.
  sorry

@[simp] theorem ricci_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx thetaIdx = 0 := by
  -- TODO: this is the real Kerr Ricci (θ,θ) component identity.
  -- The identity holds by direct computation in Boyer-Lindquist coordinates.
  sorry

@[simp] theorem ricci_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx phiIdx = 0 := by
  -- TODO: this is the real Kerr Ricci (φ,φ) component identity.
  -- The identity holds by direct computation in Boyer-Lindquist coordinates.
  sorry

@[simp] theorem ricci_component_zero (M a : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    kerrRicciComponents M a x i j = 0 := by
  -- TODO: this is the full Kerr Ricci vanishing statement.
  -- The identity holds by direct computation in Boyer-Lindquist coordinates.
  sorry

end Kerr
end KerrFormalization
