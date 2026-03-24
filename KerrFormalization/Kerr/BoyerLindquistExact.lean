import KerrFormalization.Trusted.ExactField
import KerrFormalization.Trusted.ExactMetricData
import KerrFormalization.Kerr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact Kerr metric data in Boyer-Lindquist coordinates
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open Trusted

private def rExpr : ScalarExpr 4 := .coord rIdx
private def thetaExpr : ScalarExpr 4 := .coord thetaIdx

private def sigmaExpr (a : ℝ) : ScalarExpr 4 :=
  .add (.pow rExpr 2) (.mul (.pow (.const a) 2) (.pow (.cos thetaExpr) 2))

private def deltaExpr (M a : ℝ) : ScalarExpr 4 :=
  .add (.sub (.pow rExpr 2) (.mul (.const (2 * M)) rExpr)) (.pow (.const a) 2)

private def gttExpr (M a : ℝ) : ScalarExpr 4 :=
  .sub (.const 0) (.sub (.const 1)
    (.div (.mul (.mul (.const 2) (.const M)) rExpr) (sigmaExpr a)))

private def grrExpr (M a : ℝ) : ScalarExpr 4 :=
  .div (sigmaExpr a) (deltaExpr M a)

private def gThetaThetaExpr (a : ℝ) : ScalarExpr 4 :=
  sigmaExpr a

private def gtPhiExpr (M a : ℝ) : ScalarExpr 4 :=
  .sub (.const 0)
    (.div (.mul (.mul (.mul (.const 2) (.const M)) (.const a)) rExpr)
      (sigmaExpr a))

private def gPhiPhiExpr (M a : ℝ) : ScalarExpr 4 :=
  .div
    (.mul
      (.sub
        (.pow (.add (.pow rExpr 2) (.pow (.const a) 2)) 2)
        (.mul (.mul (.pow (.const a) 2) (deltaExpr M a)) (.pow (.sin thetaExpr) 2)))
      (.pow (.sin thetaExpr) 2))
    (sigmaExpr a)

/-- Boyer-Lindquist domain where the exact Kerr formulas are nonsingular. -/
def boyerLindquistDomain (M a : ℝ) : CoordinateDomain 4 :=
  fun x => sigma a (x rIdx) (x thetaIdx) ≠ 0 ∧ delta M a (x rIdx) ≠ 0

/-- `g_tt` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gttField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => -(1 - (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx))
  deriv := ExactField.deriv (ExactField.fromExpr (gttExpr M a))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (gttExpr M a))

/-- `g_rr` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def grrField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => sigma a (x rIdx) (x thetaIdx) / delta M a (x rIdx)
  deriv := ExactField.deriv (ExactField.fromExpr (grrExpr M a))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (grrExpr M a))

/-- `g_θθ = Σ` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gThetaThetaField (a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => sigma a (x rIdx) (x thetaIdx)
  deriv := ExactField.deriv (ExactField.fromExpr (gThetaThetaExpr a))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (gThetaThetaExpr a))

/-- `g_tφ` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gtPhiField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x =>
    -(2 * M * a * x rIdx * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx))
  deriv := ExactField.deriv (ExactField.fromExpr (gtPhiExpr M a))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (gtPhiExpr M a))

/-- `g_φφ` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gPhiPhiField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x =>
    (((x rIdx)^2 + a^2)^2 - a^2 * delta M a (x rIdx) * (Real.sin (x thetaIdx))^2)
      * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx)
  deriv := ExactField.deriv (ExactField.fromExpr (gPhiPhiExpr M a))
  deriv2 := ExactField.deriv2 (ExactField.fromExpr (gPhiPhiExpr M a))

/-- Diagonal Kerr component selector. -/
noncomputable def kerrDiagField (M a : ℝ) : Fin 4 → CoordinateScalarField 4
  | i =>
      if i = tIdx then gttField M a
      else if i = rIdx then grrField M a
      else if i = thetaIdx then gThetaThetaField a
      else if i = phiIdx then gPhiPhiField M a
      else (ExactField.const 0).toCoordinateScalarField

/-- Kerr metric data in Boyer-Lindquist coordinates. -/
noncomputable def kerrMetricData (M a : ℝ) : CoordinateMetricData 4 where
  domain := boyerLindquistDomain M a
  component := by
    classical
    intro i j
    exact if hOff : offDiagTPhi i j then gtPhiField M a
      else if hDiag : i = j then kerrDiagField M a i
      else (ExactField.const 0).toCoordinateScalarField
  symmetric := by
    intro i j x
    fin_cases i <;> fin_cases j <;> simp [offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]
  deriv_symmetric := by
    intro i j k x
    fin_cases i <;> fin_cases j <;> simp [offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]
  deriv2_symmetric := by
    intro i j k l x
    fin_cases i <;> fin_cases j <;> simp [offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem gttField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    gttField M a x = -(1 - (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx)) := rfl

@[simp] theorem grrField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    grrField M a x = sigma a (x rIdx) (x thetaIdx) / delta M a (x rIdx) := rfl

@[simp] theorem gThetaThetaField_apply (a : ℝ) (x : CoordinateSpace 4) :
    gThetaThetaField a x = sigma a (x rIdx) (x thetaIdx) := rfl

@[simp] theorem gtPhiField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    gtPhiField M a x =
      -(2 * M * a * x rIdx * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx)) := rfl

@[simp] theorem gPhiPhiField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    gPhiPhiField M a x =
      (((x rIdx)^2 + a^2)^2 - a^2 * delta M a (x rIdx) * (Real.sin (x thetaIdx))^2)
        * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx) := rfl

end Kerr
end KerrFormalization
