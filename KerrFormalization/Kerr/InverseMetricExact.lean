import KerrFormalization.Kerr.BoyerLindquistExact
import KerrFormalization.Trusted.ExactInverseMetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact Kerr inverse metric data in Boyer-Lindquist coordinates
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open Trusted
open scoped BigOperators

private def rExpr : ScalarExpr 4 := .coord rIdx
private def thetaExpr : ScalarExpr 4 := .coord thetaIdx

private def sigmaExpr (a : ℝ) : ScalarExpr 4 :=
  .add (.pow rExpr 2) (.mul (.pow (.const a) 2) (.pow (.cos thetaExpr) 2))

private def deltaExpr (M a : ℝ) : ScalarExpr 4 :=
  .add (.sub (.pow rExpr 2) (.mul (.const (2 * M)) rExpr)) (.pow (.const a) 2)

private def inverseTTExpr (M a : ℝ) : ScalarExpr 4 :=
  .sub (.const 0)
    (.div (.pow (.add (.pow rExpr 2) (.pow (.const a) 2)) 2)
      (.mul (deltaExpr M a) (sigmaExpr a)))

private def inverseRRExpr (M a : ℝ) : ScalarExpr 4 :=
  .div (deltaExpr M a) (sigmaExpr a)

private def inverseThetaThetaExpr (a : ℝ) : ScalarExpr 4 :=
  .div (.const 1) (sigmaExpr a)

private def inversePhiPhiExpr (M a : ℝ) : ScalarExpr 4 :=
  .div (.sub (deltaExpr M a) (.mul (.pow (.const a) 2) (.pow (.sin thetaExpr) 2)))
    (.mul (deltaExpr M a) (.mul (sigmaExpr a) (.pow (.sin thetaExpr) 2)))

private def inverseTPhiExpr (M a : ℝ) : ScalarExpr 4 :=
  .sub (.const 0)
    (.div (.mul (.mul (.const (2 * M)) (.const a)) rExpr)
      (.mul (deltaExpr M a) (sigmaExpr a)))

/-- Pointwise inverse Kerr metric components in Boyer-Lindquist coordinates. -/
noncomputable def kerrInverseMetricData (M a : ℝ) : InverseMetricData 4 :=
  fun x i j => by
    classical
    exact if hOff : offDiagTPhi i j then
      -(2 * M * a * x rIdx / (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx)))
    else if hDiag : i = j then
      if i = tIdx then
        -((((x rIdx)^2 + a^2)^2 - a^2 * delta M a (x rIdx) * (Real.sin (x thetaIdx))^2) /
          (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx)))
      else if i = rIdx then
        delta M a (x rIdx) / sigma a (x rIdx) (x thetaIdx)
      else if i = thetaIdx then
        (sigma a (x rIdx) (x thetaIdx))⁻¹
      else if i = phiIdx then
        (delta M a (x rIdx) - a^2 * (Real.sin (x thetaIdx))^2) /
          (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx) * (Real.sin (x thetaIdx))^2)
      else 0
    else 0

@[simp] theorem kerrInverseMetric_tt (M a : ℝ) (x : CoordinateSpace 4) :
    kerrInverseMetricData M a x tIdx tIdx =
      -((((x rIdx)^2 + a^2)^2 - a^2 * delta M a (x rIdx) * (Real.sin (x thetaIdx))^2) /
        (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx))) := by
  simp [kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrInverseMetric_rr (M a : ℝ) (x : CoordinateSpace 4) :
    kerrInverseMetricData M a x rIdx rIdx =
      delta M a (x rIdx) / sigma a (x rIdx) (x thetaIdx) := by
  simp [kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrInverseMetric_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    kerrInverseMetricData M a x thetaIdx thetaIdx =
      (sigma a (x rIdx) (x thetaIdx))⁻¹ := by
  simp [kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrInverseMetric_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    kerrInverseMetricData M a x phiIdx phiIdx =
      (delta M a (x rIdx) - a^2 * (Real.sin (x thetaIdx))^2) /
        (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx) * (Real.sin (x thetaIdx))^2) := by
  simp [kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrInverseMetric_tPhi (M a : ℝ) (x : CoordinateSpace 4) :
    kerrInverseMetricData M a x tIdx phiIdx =
      -(2 * M * a * x rIdx / (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx))) := by
  simp [kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrInverseMetric_phiT (M a : ℝ) (x : CoordinateSpace 4) :
    kerrInverseMetricData M a x phiIdx tIdx =
      -(2 * M * a * x rIdx / (delta M a (x rIdx) * sigma a (x rIdx) (x thetaIdx))) := by
  simp [kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrInverseMetric_offDiag (M a : ℝ) (x : CoordinateSpace 4)
    (i j : Fin 4) (hij : ¬ offDiagTPhi i j) (hij' : i ≠ j) :
    kerrInverseMetricData M a x i j = 0 := by
  classical
  by_cases hOff : offDiagTPhi i j
  · exact False.elim (hij hOff)
  · by_cases hEq : i = j
    · exact False.elim (hij' hEq)
    · simp [kerrInverseMetricData, hOff, hEq, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]
      intro h
      exact False.elim (hOff h)

/-- Inverse Kerr metric data with generated first derivatives of inverse components. -/
noncomputable def kerrInverseMetricWithDeriv (M a : ℝ) : InverseMetricDataWithDeriv 4 where
  value := kerrInverseMetricData M a
  deriv := fun k x i j => by
    classical
    exact if hOff : offDiagTPhi i j then
      ExactField.deriv (ExactField.fromExpr (inverseTPhiExpr M a)) k x
    else if hDiag : i = j then
      if i = tIdx then
        ExactField.deriv (ExactField.fromExpr (inverseTTExpr M a)) k x
      else if i = rIdx then
        ExactField.deriv (ExactField.fromExpr (inverseRRExpr M a)) k x
      else if i = thetaIdx then
        ExactField.deriv (ExactField.fromExpr (inverseThetaThetaExpr a)) k x
      else if i = phiIdx then
        ExactField.deriv (ExactField.fromExpr (inversePhiPhiExpr M a)) k x
      else 0
    else 0

/-- Partial goal marker for the Kerr inverse proof path. -/
def kerrInverseMetricGoal (M a : ℝ) : Prop :=
  True

end Kerr
end KerrFormalization
