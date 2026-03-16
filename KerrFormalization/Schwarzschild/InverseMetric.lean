import KerrFormalization.Schwarzschild.Metric

/-!
# Schwarzschild inverse metric components

This file isolates the inverse-metric layer for Schwarzschild coordinates.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Pointwise inverse Schwarzschild metric components in Schwarzschild coordinates. -/
noncomputable def schwarzschildInverseMetric (M : ℝ) : InverseMetricData 4 :=
  fun x i j =>
    if h : i = j then
      if i = tIdx then -((lapse M (x rIdx))⁻¹)
      else if i = rIdx then lapse M (x rIdx)
      else if i = thetaIdx then ((x rIdx)^2)⁻¹
      else if i = phiIdx then (((x rIdx)^2) * (Real.sin (x thetaIdx))^2)⁻¹
      else 0
    else 0

/-- Inverse Schwarzschild metric data together with supplied first derivatives. -/
noncomputable def schwarzschildInverseMetricWithDeriv (M : ℝ) : InverseMetricDataWithDeriv 4 where
  value := schwarzschildInverseMetric M
  deriv := fun k x i j =>
    if hij : i = j then
      if i = tIdx then
        if k = rIdx then ((2 * M) / (x rIdx)^2) / (lapse M (x rIdx))^2 else 0
      else if i = rIdx then
        if k = rIdx then (2 * M) / (x rIdx)^2 else 0
      else if i = thetaIdx then
        if k = rIdx then -(2 / (x rIdx)^3) else 0
      else if i = phiIdx then
        if k = rIdx then
          -(2 / ((x rIdx)^3 * (Real.sin (x thetaIdx))^2))
        else if k = thetaIdx then
          -(2 * Real.cos (x thetaIdx) / ((x rIdx)^2 * (Real.sin (x thetaIdx))^3))
        else 0
      else 0
    else 0

@[simp] theorem inverse_tt (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildInverseMetric M x tIdx tIdx = -((lapse M (x rIdx))⁻¹) := by
  simp [schwarzschildInverseMetric, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem inverse_rr (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildInverseMetric M x rIdx rIdx = lapse M (x rIdx) := by
  simp [schwarzschildInverseMetric, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem inverse_thetaTheta (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildInverseMetric M x thetaIdx thetaIdx = ((x rIdx)^2)⁻¹ := by
  simp [schwarzschildInverseMetric, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem inverse_phiPhi (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildInverseMetric M x phiIdx phiIdx =
      (((x rIdx)^2) * (Real.sin (x thetaIdx))^2)⁻¹ := by
  simp [schwarzschildInverseMetric, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem inverse_offDiag (M : ℝ) (x : CoordinateSpace 4)
    (i j : Fin 4) (hij : i ≠ j) :
    schwarzschildInverseMetric M x i j = 0 := by
  simp [schwarzschildInverseMetric, hij]

end Schwarzschild
end KerrFormalization
