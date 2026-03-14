import KerrFormalization.Kerr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kerr horizon helper definitions and lemmas
-/

namespace KerrFormalization
namespace Kerr

/-- Outer Kerr horizon radius `r_+ = M + sqrt(M^2 - a^2)`. -/
noncomputable def outerHorizon (M a : ℝ) : ℝ :=
  M + Real.sqrt (M^2 - a^2)

/-- Inner Kerr horizon radius `r_- = M - sqrt(M^2 - a^2)`. -/
noncomputable def innerHorizon (M a : ℝ) : ℝ :=
  M - Real.sqrt (M^2 - a^2)

@[simp] theorem outerHorizon_def (M a : ℝ) :
    outerHorizon M a = M + Real.sqrt (M ^ 2 - a ^ 2) := rfl

@[simp] theorem innerHorizon_def (M a : ℝ) :
    innerHorizon M a = M - Real.sqrt (M ^ 2 - a ^ 2) := rfl

theorem horizon_sum (M a : ℝ) :
    outerHorizon M a + innerHorizon M a = 2 * M := by
  unfold outerHorizon innerHorizon
  ring

theorem horizon_difference (M a : ℝ) :
    outerHorizon M a - innerHorizon M a = 2 * Real.sqrt (M ^ 2 - a ^ 2) := by
  unfold outerHorizon innerHorizon
  ring

theorem horizon_product (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    outerHorizon M a * innerHorizon M a = a ^ 2 := by
  unfold outerHorizon innerHorizon
  have hs : (Real.sqrt (M ^ 2 - a ^ 2)) ^ 2 = M ^ 2 - a ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt hdisc
  nlinarith [hs]

theorem innerHorizon_le_outerHorizon (M a : ℝ) :
    innerHorizon M a ≤ outerHorizon M a := by
  unfold innerHorizon outerHorizon
  nlinarith [Real.sqrt_nonneg (M ^ 2 - a ^ 2)]

theorem outerHorizon_nonneg_discriminant (M a : ℝ) :
    0 ≤ outerHorizon M a - innerHorizon M a := by
  rw [horizon_difference]
  positivity

theorem delta_outerHorizon_eq_zero (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    delta M a (outerHorizon M a) = 0 := by
  unfold delta outerHorizon
  have hs : (Real.sqrt (M ^ 2 - a ^ 2)) ^ 2 = M ^ 2 - a ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt hdisc
  nlinarith [hs]

theorem delta_innerHorizon_eq_zero (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    delta M a (innerHorizon M a) = 0 := by
  unfold delta innerHorizon
  have hs : (Real.sqrt (M ^ 2 - a ^ 2)) ^ 2 = M ^ 2 - a ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt hdisc
  nlinarith [hs]

end Kerr
end KerrFormalization
