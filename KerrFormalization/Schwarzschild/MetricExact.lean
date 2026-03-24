import KerrFormalization.Trusted.ExactField
import KerrFormalization.Trusted.ExactMetricData
import KerrFormalization.Schwarzschild.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact Schwarzschild metric data

This is the Phase I canary lane for the trusted exact-expression kernel.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates
open Trusted

private def rExpr : ScalarExpr 4 := .coord rIdx
private def thetaExpr : ScalarExpr 4 := .coord thetaIdx
private def lapseExpr (M : ℝ) : ScalarExpr 4 :=
  .sub (.const 1) (.div (.const (2 * M)) rExpr)

private def gttExpr (M : ℝ) : ScalarExpr 4 :=
  .sub (.const 0) (lapseExpr M)

private def grrExpr (M : ℝ) : ScalarExpr 4 :=
  .div (.const 1) (lapseExpr M)

private def gThetaThetaExpr : ScalarExpr 4 :=
  .pow rExpr 2

private def gPhiPhiExpr : ScalarExpr 4 :=
  .mul (.pow rExpr 2) (.pow (.sin thetaExpr) 2)

/-- The `g_tt` component of the Schwarzschild metric. -/
noncomputable def gttField (M : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => -(lapse M (x rIdx))
  deriv := ExactField.deriv (ExactField.fromExpr (gttExpr M))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (gttExpr M))

/-- The `g_rr` component of the Schwarzschild metric. -/
noncomputable def grrField (M : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => (lapse M (x rIdx))⁻¹
  deriv := ExactField.deriv (ExactField.fromExpr (grrExpr M))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (grrExpr M))

/-- The `g_{θθ}` component of the Schwarzschild metric. -/
noncomputable def gThetaThetaField : CoordinateScalarField 4 where
  toFun := fun x => (x rIdx)^2
  deriv := ExactField.deriv (ExactField.fromExpr gThetaThetaExpr)
  deriv2 := ExactField.deriv2 (ExactField.fromExpr gThetaThetaExpr)

/-- The `g_{φφ}` component of the Schwarzschild metric. -/
noncomputable def gPhiPhiField : CoordinateScalarField 4 where
  toFun := fun x => (x rIdx)^2 * (Real.sin (x thetaIdx))^2
  deriv := ExactField.deriv (ExactField.fromExpr gPhiPhiExpr)
  deriv2 := ExactField.deriv2 (ExactField.fromExpr gPhiPhiExpr)

/-- Diagonal entries of the Schwarzschild metric. -/
noncomputable def schwarzschildDiag (M : ℝ) : Fin 4 → CoordinateScalarField 4
  | i =>
      if i = tIdx then gttField M
      else if i = rIdx then grrField M
      else if i = thetaIdx then gThetaThetaField
      else if i = phiIdx then gPhiPhiField
      else (ExactField.const 0).toCoordinateScalarField

/-- Schwarzschild metric data on the exterior domain. -/
noncomputable def schwarzschildMetricData (M : ℝ) : CoordinateMetricData 4 where
  domain := exteriorDomain M
  component := fun i j =>
    if i = j then schwarzschildDiag M i else (ExactField.const 0).toCoordinateScalarField
  symmetric := by
    intro i j x
    by_cases hij : i = j
    · subst hij
      simp [schwarzschildDiag]
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      simp [hij, hji]
  deriv_symmetric := by
    intro i j k x
    by_cases hij : i = j
    · subst hij
      simp [schwarzschildDiag]
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      simp [hij, hji]
  deriv2_symmetric := by
    intro i j k l x
    by_cases hij : i = j
    · subst hij
      simp [schwarzschildDiag]
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      simp [hij, hji]

@[simp] theorem gttField_apply (M : ℝ) (x : CoordinateSpace 4) :
    gttField M x = -(lapse M (x rIdx)) := rfl

@[simp] theorem grrField_apply (M : ℝ) (x : CoordinateSpace 4) :
    grrField M x = (lapse M (x rIdx))⁻¹ := rfl

@[simp] theorem gThetaThetaField_apply (x : CoordinateSpace 4) :
    gThetaThetaField x = (x rIdx)^2 := rfl

@[simp] theorem gPhiPhiField_apply (x : CoordinateSpace 4) :
    gPhiPhiField x = (x rIdx)^2 * (Real.sin (x thetaIdx))^2 := rfl

end Schwarzschild
end KerrFormalization
