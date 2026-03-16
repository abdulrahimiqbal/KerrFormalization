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

lemma ricci_00 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx tIdx = 0 := by
  -- TODO: Kerr Ricci (0,0) real-pipeline algebraic identity.
  sorry

lemma ricci_01 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx rIdx = 0 := by
  -- TODO: Kerr Ricci (0,1) real-pipeline algebraic identity.
  sorry

lemma ricci_02 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx thetaIdx = 0 := by
  -- TODO: Kerr Ricci (0,2) real-pipeline algebraic identity.
  sorry

lemma ricci_03 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx phiIdx = 0 := by
  -- TODO: Kerr Ricci (0,3) real-pipeline algebraic identity.
  sorry

lemma ricci_10 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx tIdx = 0 := by
  -- TODO: Kerr Ricci (1,0) real-pipeline algebraic identity.
  sorry

lemma ricci_11 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx rIdx = 0 := by
  -- TODO: Kerr Ricci (1,1) real-pipeline algebraic identity.
  sorry

lemma ricci_12 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx thetaIdx = 0 := by
  -- TODO: Kerr Ricci (1,2) real-pipeline algebraic identity.
  sorry

lemma ricci_13 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx phiIdx = 0 := by
  -- TODO: Kerr Ricci (1,3) real-pipeline algebraic identity.
  sorry

lemma ricci_20 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx tIdx = 0 := by
  -- TODO: Kerr Ricci (2,0) real-pipeline algebraic identity.
  sorry

lemma ricci_21 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx rIdx = 0 := by
  -- TODO: Kerr Ricci (2,1) real-pipeline algebraic identity.
  sorry

lemma ricci_22 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx thetaIdx = 0 := by
  -- TODO: Kerr Ricci (2,2) real-pipeline algebraic identity.
  sorry

lemma ricci_23 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx phiIdx = 0 := by
  -- TODO: Kerr Ricci (2,3) real-pipeline algebraic identity.
  sorry

lemma ricci_30 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx tIdx = 0 := by
  -- TODO: Kerr Ricci (3,0) real-pipeline algebraic identity.
  sorry

lemma ricci_31 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx rIdx = 0 := by
  -- TODO: Kerr Ricci (3,1) real-pipeline algebraic identity.
  sorry

lemma ricci_32 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx thetaIdx = 0 := by
  -- TODO: Kerr Ricci (3,2) real-pipeline algebraic identity.
  sorry

lemma ricci_33 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx phiIdx = 0 := by
  -- TODO: Kerr Ricci (3,3) real-pipeline algebraic identity.
  sorry

@[simp] theorem ricci_component_zero (M a : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    kerrRicciComponents M a x i j = 0 := by
  fin_cases i <;> fin_cases j
  · simpa using ricci_00 M a x
  · simpa using ricci_01 M a x
  · simpa using ricci_02 M a x
  · simpa using ricci_03 M a x
  · simpa using ricci_10 M a x
  · simpa using ricci_11 M a x
  · simpa using ricci_12 M a x
  · simpa using ricci_13 M a x
  · simpa using ricci_20 M a x
  · simpa using ricci_21 M a x
  · simpa using ricci_22 M a x
  · simpa using ricci_23 M a x
  · simpa using ricci_30 M a x
  · simpa using ricci_31 M a x
  · simpa using ricci_32 M a x
  · simpa using ricci_33 M a x

@[simp] theorem ricci_tt (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx tIdx = 0 := by
  simpa using ricci_00 M a x

@[simp] theorem ricci_rr (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx rIdx = 0 := by
  simpa using ricci_11 M a x

@[simp] theorem ricci_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx thetaIdx = 0 := by
  simpa using ricci_22 M a x

@[simp] theorem ricci_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx phiIdx = 0 := by
  simpa using ricci_33 M a x

end Kerr
end KerrFormalization
