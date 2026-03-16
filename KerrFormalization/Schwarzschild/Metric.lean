import KerrFormalization.Schwarzschild.Basic
import KerrFormalization.LocalCoordinates.MetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Schwarzschild metric data in coordinates

This file encodes the diagonal Schwarzschild metric in Schwarzschild coordinates
as component scalar fields with supplied first coordinate derivatives.
The derivative data is explicit and intended for later use in Christoffel-symbol
and curvature computations.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- The `g_tt` component field of the Schwarzschild metric. -/
noncomputable def gttField (M : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => -(lapse M (x rIdx))
  deriv := fun k x =>
    if k = rIdx then -(2 * M) / (x rIdx)^2 else 0
  deriv2 := fun k l x =>
    if k = rIdx ∧ l = rIdx then 4 * M / (x rIdx)^3 else 0

/-- The `g_rr` component field of the Schwarzschild metric. -/
noncomputable def grrField (M : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => (lapse M (x rIdx))⁻¹
  deriv := fun k x =>
    if k = rIdx then
      -((2 * M) / (x rIdx)^2) / (lapse M (x rIdx))^2
    else 0
  deriv2 := fun k l x =>
    if k = rIdx ∧ l = rIdx then
      (4 * M / (x rIdx)^3) / (lapse M (x rIdx))^2
        + (8 * M^2 / (x rIdx)^4) / (lapse M (x rIdx))^3
    else 0

/-- The `g_{θθ}` component field of the Schwarzschild metric. -/
noncomputable def gThetaThetaField : CoordinateScalarField 4 where
  toFun := fun x => (x rIdx)^2
  deriv := fun k x =>
    if k = rIdx then 2 * x rIdx else 0
  deriv2 := fun k l _ =>
    if k = rIdx ∧ l = rIdx then 2 else 0

/-- The `g_{φφ}` component field of the Schwarzschild metric. -/
noncomputable def gPhiPhiField : CoordinateScalarField 4 where
  toFun := fun x => (x rIdx)^2 * (Real.sin (x thetaIdx))^2
  deriv := fun k x =>
    if k = rIdx then
      2 * x rIdx * (Real.sin (x thetaIdx))^2
    else if k = thetaIdx then
      (x rIdx)^2 * (2 * Real.sin (x thetaIdx) * Real.cos (x thetaIdx))
    else 0
  deriv2 := fun k l x =>
    if k = rIdx ∧ l = rIdx then
      2 * (Real.sin (x thetaIdx))^2
    else if k = thetaIdx ∧ l = thetaIdx then
      (x rIdx)^2 * (2 * ((Real.cos (x thetaIdx))^2 - (Real.sin (x thetaIdx))^2))
    else if (k = rIdx ∧ l = thetaIdx) ∨ (k = thetaIdx ∧ l = rIdx) then
      4 * x rIdx * Real.sin (x thetaIdx) * Real.cos (x thetaIdx)
    else 0

/-- Diagonal entries of the Schwarzschild metric. -/
noncomputable def schwarzschildDiag (M : ℝ) : Fin 4 → CoordinateScalarField 4
  | i =>
      if i = tIdx then gttField M
      else if i = rIdx then grrField M
      else if i = thetaIdx then gThetaThetaField
      else if i = phiIdx then gPhiPhiField
      else CoordinateScalarField.zero 4

/-- Schwarzschild metric data on the exterior domain. -/
noncomputable def schwarzschildMetricData (M : ℝ) : CoordinateMetricData 4 :=
  CoordinateMetricData.diagonal (exteriorDomain M) (schwarzschildDiag M)

example (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (schwarzschildMetricData M) x tIdx tIdx = -(lapse M (x rIdx)) := by
  simp [schwarzschildMetricData, CoordinateMetricData.value, CoordinateMetricData.diagonal,
    schwarzschildDiag, tIdx, gttField]

example (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.partialValue (schwarzschildMetricData M) rIdx x tIdx tIdx =
      -(2 * M) / (x rIdx)^2 := by
  simp [schwarzschildMetricData, CoordinateMetricData.partialValue, CoordinateMetricData.diagonal,
    schwarzschildDiag, tIdx, rIdx, gttField]

example (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.partialValue (schwarzschildMetricData M) thetaIdx x phiIdx phiIdx =
      (x rIdx)^2 * (2 * Real.sin (x thetaIdx) * Real.cos (x thetaIdx)) := by
  unfold CoordinateMetricData.partialValue schwarzschildMetricData CoordinateMetricData.diagonal
  simp only [if_pos rfl]
  have hφt : phiIdx ≠ tIdx := by decide
  have hφr : phiIdx ≠ rIdx := by decide
  have hφθ : phiIdx ≠ thetaIdx := by decide
  have hθr : thetaIdx ≠ rIdx := by decide
  change (gPhiPhiField.deriv thetaIdx x) =
    (x rIdx)^2 * (2 * Real.sin (x thetaIdx) * Real.cos (x thetaIdx))
  simp [schwarzschildDiag, gPhiPhiField, hφt, hφr, hφθ, hθr]

#check schwarzschildMetricData
end Schwarzschild
end KerrFormalization
