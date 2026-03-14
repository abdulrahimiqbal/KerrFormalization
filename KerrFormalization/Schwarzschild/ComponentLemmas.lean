import KerrFormalization.Schwarzschild.Christoffel
import KerrFormalization.LocalCoordinates.DiagonalMetricLemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Explicit Schwarzschild component lemmas

A first robust batch of metric, derivative, and Christoffel component lemmas in
Schwarzschild coordinates.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

section MetricComponents

theorem metric_tt (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (schwarzschildMetricData M) x tIdx tIdx = -(lapse M (x rIdx)) := by
  unfold CoordinateMetricData.value schwarzschildMetricData CoordinateMetricData.diagonal
  simp [schwarzschildDiag, gttField, tIdx, rIdx, thetaIdx, phiIdx]

theorem metric_rr (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (schwarzschildMetricData M) x rIdx rIdx = (lapse M (x rIdx))⁻¹ := by
  unfold CoordinateMetricData.value schwarzschildMetricData CoordinateMetricData.diagonal
  simp [schwarzschildDiag, grrField, tIdx, rIdx, thetaIdx, phiIdx]

theorem metric_phiPhi (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (schwarzschildMetricData M) x phiIdx phiIdx =
      (x rIdx)^2 * (Real.sin (x thetaIdx))^2 := by
  unfold CoordinateMetricData.value schwarzschildMetricData CoordinateMetricData.diagonal
  simp [schwarzschildDiag, gPhiPhiField, tIdx, rIdx, thetaIdx, phiIdx]

theorem metric_offDiag (M : ℝ) (x : CoordinateSpace 4)
    (i j : Fin 4) (hij : i ≠ j) :
    CoordinateMetricData.value (schwarzschildMetricData M) x i j = 0 := by
  simpa [schwarzschildMetricData] using
    (CoordinateMetricData.value_diagonal_offDiag (domain := exteriorDomain M)
      (diag := schwarzschildDiag M) (x := x) (i := i) (j := j) hij)

end MetricComponents

section PartialComponents

theorem partial_tt_r (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.partialValue (schwarzschildMetricData M) rIdx x tIdx tIdx =
      -(2 * M) / (x rIdx)^2 := by
  unfold CoordinateMetricData.partialValue schwarzschildMetricData CoordinateMetricData.diagonal
  simp [schwarzschildDiag, gttField, tIdx, rIdx, thetaIdx, phiIdx]

theorem partial_rr_r (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.partialValue (schwarzschildMetricData M) rIdx x rIdx rIdx =
      -((2 * M) / (x rIdx)^2) / (lapse M (x rIdx))^2 := by
  unfold CoordinateMetricData.partialValue schwarzschildMetricData CoordinateMetricData.diagonal
  simp [schwarzschildDiag, grrField, tIdx, rIdx, thetaIdx, phiIdx]

theorem partial_phiPhi_theta (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.partialValue (schwarzschildMetricData M) thetaIdx x phiIdx phiIdx =
      (x rIdx)^2 * (2 * Real.sin (x thetaIdx) * Real.cos (x thetaIdx)) := by
  unfold CoordinateMetricData.partialValue schwarzschildMetricData CoordinateMetricData.diagonal
  simp [schwarzschildDiag, gPhiPhiField, tIdx, rIdx, thetaIdx, phiIdx]

theorem partial_offDiag_zero (M : ℝ) (k : Fin 4) (x : CoordinateSpace 4)
    (i j : Fin 4) (hij : i ≠ j) :
    CoordinateMetricData.partialValue (schwarzschildMetricData M) k x i j = 0 := by
  simpa [schwarzschildMetricData] using
    (CoordinateMetricData.partialValue_diagonal_offDiag (domain := exteriorDomain M)
      (diag := schwarzschildDiag M) (k := k) (x := x) (i := i) (j := j) hij)

end PartialComponents

section ChristoffelComponents

theorem christoffel_t_tt_zero (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildChristoffel M x tIdx tIdx tIdx = 0 := by
  unfold schwarzschildChristoffel LocalCoordinates.christoffelFromMetricData
  simp [CoordinateMetricData.partialValue, schwarzschildMetricData, CoordinateMetricData.diagonal,
    schwarzschildDiag, gttField, grrField, gThetaThetaField, gPhiPhiField,
    schwarzschildInverseMetric, tIdx, rIdx, thetaIdx, phiIdx]

theorem christoffel_r_tt (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildChristoffel M x rIdx tIdx tIdx =
      (M / (x rIdx)^2) * lapse M (x rIdx) := by
  unfold schwarzschildChristoffel LocalCoordinates.christoffelFromMetricData
  simp [CoordinateMetricData.partialValue, schwarzschildMetricData, CoordinateMetricData.diagonal,
    schwarzschildDiag, gttField, grrField, gThetaThetaField, gPhiPhiField,
    schwarzschildInverseMetric, tIdx, rIdx, thetaIdx, phiIdx]
  ring_nf

end ChristoffelComponents

end Schwarzschild
end KerrFormalization
