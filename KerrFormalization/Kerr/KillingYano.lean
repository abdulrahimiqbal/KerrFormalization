import KerrFormalization.Trusted.ExactField
import KerrFormalization.Kerr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Kerr Killing-Yano 2-form in Boyer-Lindquist coordinates

This file records the standard Kerr Killing-Yano 2-form as the Hodge dual of
the principal closed conformal Killing-Yano tensor. The component convention
used here matches the common literature formula

`f = a cos θ (dr ∧ (dt - a sin²θ dφ)) - r sin θ (dθ ∧ (a dt - (r² + a²) dφ))`.

The file is intentionally pointwise and exact-expression based, following the
same pattern as `BoyerLindquistExact.lean`.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open Trusted

private def rExpr : ScalarExpr 4 := .coord rIdx
private def thetaExpr : ScalarExpr 4 := .coord thetaIdx

private def aCosExpr (a : ℝ) : ScalarExpr 4 :=
  .mul (.const a) (.cos thetaExpr)

private def aRsinExpr (a : ℝ) : ScalarExpr 4 :=
  .mul (.mul (.const a) rExpr) (.sin thetaExpr)

private def a2CosSin2Expr (a : ℝ) : ScalarExpr 4 :=
  .mul (.mul (.pow (.const a) 2) (.cos thetaExpr)) (.pow (.sin thetaExpr) 2)

private def rRRplusA2SinExpr (a : ℝ) : ScalarExpr 4 :=
  .mul (.mul rExpr (.add (.pow rExpr 2) (.pow (.const a) 2))) (.sin thetaExpr)

private def killingYanoExpr (a : ℝ) (i j : Fin 4) : ScalarExpr 4 :=
  match i.val, j.val with
  | 0, 0 => .const 0
  | 0, 1 => .sub (.const 0) (aCosExpr a)
  | 0, 2 => aRsinExpr a
  | 0, 3 => .const 0
  | 1, 0 => aCosExpr a
  | 1, 1 => .const 0
  | 1, 2 => .const 0
  | 1, 3 => .sub (.const 0) (a2CosSin2Expr a)
  | 2, 0 => .sub (.const 0) (aRsinExpr a)
  | 2, 1 => .const 0
  | 2, 2 => .const 0
  | 2, 3 => rRRplusA2SinExpr a
  | 3, 0 => .const 0
  | 3, 1 => a2CosSin2Expr a
  | 3, 2 => .sub (.const 0) (rRRplusA2SinExpr a)
  | 3, 3 => .const 0
  | _, _ => .const 0

/-- The standard Kerr Killing-Yano 2-form components. -/
noncomputable def killingYanoComponent (M a : ℝ) (i j : Fin 4) : ExactField 4 :=
  ExactField.fromExpr (killingYanoExpr a i j)

/-- Pointwise antisymmetry of the Kerr Killing-Yano 2-form. -/
theorem killingYanoComponent_antisymm (M a : ℝ) (x : CoordinateSpace 4)
    (i j : Fin 4) :
    killingYanoComponent M a i j x = - killingYanoComponent M a j i x := by
  -- TODO: prove by exhaustive `Fin 4` case split after a dedicated simp lemma
  -- for `ScalarExpr.eval` over the exact KY expression tree.
  sorry

-- TODO: Aristotle should verify the component list below one index block at a time.

@[simp] theorem killingYanoComponent_tt (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a tIdx tIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_tr (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a tIdx rIdx x = -(a * Real.cos (x thetaIdx)) := by
  -- TODO: unfold the exact expression tree and normalize the `0 - _` form.
  sorry

@[simp] theorem killingYanoComponent_ttheta (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a tIdx thetaIdx x = a * x rIdx * Real.sin (x thetaIdx) := by
  -- TODO: unfold the exact expression tree and normalize the product form.
  sorry

@[simp] theorem killingYanoComponent_tphi (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a tIdx phiIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_rt (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a rIdx tIdx x = a * Real.cos (x thetaIdx) := by
  -- TODO: unfold the exact expression tree and normalize the coefficient order.
  sorry

@[simp] theorem killingYanoComponent_rr (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a rIdx rIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_rtheta (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a rIdx thetaIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_rphi (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a rIdx phiIdx x =
      -(a ^ 2 * Real.cos (x thetaIdx) * (Real.sin (x thetaIdx)) ^ 2) := by
  -- TODO: unfold the exact expression tree and normalize the `0 - _` form.
  sorry

@[simp] theorem killingYanoComponent_theta_t (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a thetaIdx tIdx x = -(a * x rIdx * Real.sin (x thetaIdx)) := by
  -- TODO: unfold the exact expression tree and normalize the `0 - _` form.
  sorry

@[simp] theorem killingYanoComponent_theta_r (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a thetaIdx rIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_theta_theta (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a thetaIdx thetaIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_theta_phi (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a thetaIdx phiIdx x =
      x rIdx * ((x rIdx)^2 + a^2) * Real.sin (x thetaIdx) := by
  -- TODO: unfold the exact expression tree and normalize the polynomial form.
  sorry

@[simp] theorem killingYanoComponent_phi_t (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a phiIdx tIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

@[simp] theorem killingYanoComponent_phi_r (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a phiIdx rIdx x =
      a ^ 2 * Real.cos (x thetaIdx) * (Real.sin (x thetaIdx)) ^ 2 := by
  -- TODO: unfold the exact expression tree and normalize the product form.
  sorry

@[simp] theorem killingYanoComponent_phi_theta (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a phiIdx thetaIdx x =
      -(x rIdx * ((x rIdx)^2 + a^2) * Real.sin (x thetaIdx)) := by
  -- TODO: unfold the exact expression tree and normalize the `0 - _` form.
  sorry

@[simp] theorem killingYanoComponent_phi_phi (M a : ℝ) (x : CoordinateSpace 4) :
    killingYanoComponent M a phiIdx phiIdx x = 0 := by
  -- TODO: reduce the exact AST evaluation to the concrete zero expression.
  sorry

end Kerr
end KerrFormalization
