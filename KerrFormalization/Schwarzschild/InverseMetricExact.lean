import KerrFormalization.Schwarzschild.MetricExact
import KerrFormalization.Trusted.ExactInverseMetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact Schwarzschild inverse metric data
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates
open Trusted
open scoped BigOperators

private def rExpr : ScalarExpr 4 := .coord rIdx
private def thetaExpr : ScalarExpr 4 := .coord thetaIdx
private def lapseExpr (M : ℝ) : ScalarExpr 4 :=
  .sub (.const 1) (.div (.const (2 * M)) rExpr)

private def inverseTTExpr (M : ℝ) : ScalarExpr 4 :=
  .sub (.const 0) (.div (.const 1) (lapseExpr M))

private def inverseRRExpr (M : ℝ) : ScalarExpr 4 :=
  lapseExpr M

private def inverseThetaThetaExpr : ScalarExpr 4 :=
  .div (.const 1) (.pow rExpr 2)

private def inversePhiPhiExpr : ScalarExpr 4 :=
  .div (.const 1) (.mul (.pow rExpr 2) (.pow (.sin thetaExpr) 2))

/-- Pointwise inverse Schwarzschild metric components. -/
noncomputable def schwarzschildInverseMetric (M : ℝ) : InverseMetricData 4 :=
  fun x i j =>
    if h : i = j then
      if i = tIdx then -(lapse M (x rIdx))⁻¹
      else if i = rIdx then lapse M (x rIdx)
      else if i = thetaIdx then ((x rIdx)^2)⁻¹
      else if i = phiIdx then (((x rIdx)^2) * (Real.sin (x thetaIdx))^2)⁻¹
      else 0
    else 0

/-- Inverse Schwarzschild metric data together with generated derivatives. -/
noncomputable def schwarzschildInverseMetricWithDeriv (M : ℝ) : InverseMetricDataWithDeriv 4 where
  value := schwarzschildInverseMetric M
  deriv := fun k x i j =>
    if hij : i = j then
      if i = tIdx then
        ExactField.deriv (ExactField.fromExpr (inverseTTExpr M)) k x
      else if i = rIdx then
        ExactField.deriv (ExactField.fromExpr (inverseRRExpr M)) k x
      else if i = thetaIdx then
        ExactField.deriv (ExactField.fromExpr inverseThetaThetaExpr) k x
      else if i = phiIdx then
        ExactField.deriv (ExactField.fromExpr inversePhiPhiExpr) k x
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

/-- Partial goal marker for the Schwarzschild inverse proof path. -/
def schwarzschild_inverse_componentwise_goal (M : ℝ) : Prop :=
  True

end Schwarzschild
end KerrFormalization
