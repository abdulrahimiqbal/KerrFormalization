/-
  KerrTest.lean
  
  One file. Defines Kerr, tests it. Run `lake build` — if it compiles, it works.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KerrTest

-- ══════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════

noncomputable def Delta (M a r : ℝ) : ℝ := r ^ 2 - 2 * M * r + a ^ 2
noncomputable def Sigma (a r θ : ℝ) : ℝ := r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2
noncomputable def r_plus (M a : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2)
noncomputable def r_minus (M a : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - a ^ 2)
noncomputable def r_ergo (M a θ : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2 * (Real.cos θ) ^ 2)
noncomputable def Ω_H (M a : ℝ) : ℝ := a / ((r_plus M a) ^ 2 + a ^ 2)
noncomputable def A_H (M a : ℝ) : ℝ := 4 * Real.pi * ((r_plus M a) ^ 2 + a ^ 2)

noncomputable def g_tt (M a r θ : ℝ) : ℝ := -(1 - 2 * M * r / Sigma a r θ)
noncomputable def g_tφ (M a r θ : ℝ) : ℝ := -2 * M * a * r * (Real.sin θ) ^ 2 / Sigma a r θ
noncomputable def g_rr (M a r θ : ℝ) : ℝ := Sigma a r θ / Delta M a r
noncomputable def g_θθ (_M a r θ : ℝ) : ℝ := Sigma a r θ
noncomputable def g_φφ (M a r θ : ℝ) : ℝ :=
  (Real.sin θ) ^ 2 * (r ^ 2 + a ^ 2 + 2 * M * a ^ 2 * r * (Real.sin θ) ^ 2 / Sigma a r θ)

-- ══════════════════════════════════════════════
-- TESTS — if these compile, Kerr basics are correct
-- ══════════════════════════════════════════════

-- 1. Delta = 0 at outer horizon
theorem horizon_outer (M a : ℝ) (h : a ^ 2 ≤ M ^ 2) :
    Delta M a (r_plus M a) = 0 := by
  unfold Delta r_plus
  have h0 : M ^ 2 - a ^ 2 ≥ 0 := by linarith
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (M ^ 2 - a ^ 2)]

-- 2. Delta = 0 at inner horizon
theorem horizon_inner (M a : ℝ) (h : a ^ 2 ≤ M ^ 2) :
    Delta M a (r_minus M a) = 0 := by
  unfold Delta r_minus
  have h0 : M ^ 2 - a ^ 2 ≥ 0 := by linarith
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (M ^ 2 - a ^ 2)]

-- 3. Outer horizon ≥ inner horizon
theorem outer_ge_inner (M a : ℝ) (_h : a ^ 2 ≤ M ^ 2) :
    r_plus M a ≥ r_minus M a := by
  unfold r_plus r_minus
  linarith [Real.sqrt_nonneg (M ^ 2 - a ^ 2)]

-- 4. Extremal case: horizons merge at r = M
theorem extremal_merge (M : ℝ) : r_plus M M = r_minus M M := by
  unfold r_plus r_minus; simp [sub_self, Real.sqrt_zero]

theorem extremal_at_M (M : ℝ) : r_plus M M = M := by
  unfold r_plus; simp [sub_self, Real.sqrt_zero]

-- 5. No spin -> Sigma = r²
theorem sigma_no_spin (r θ : ℝ) : Sigma 0 r θ = r ^ 2 := by
  unfold Sigma
  ring

-- 6. No spin -> Delta = r² - 2Mr
theorem delta_no_spin (M r : ℝ) : Delta M 0 r = r ^ 2 - 2 * M * r := by
  unfold Delta
  ring

-- 7. No frame dragging without spin
theorem no_drag_no_spin (M r θ : ℝ) : g_tφ M 0 r θ = 0 := by
  simp [g_tφ, Sigma]

-- 8. Ergosphere touches horizon at poles
theorem ergo_pole (M a : ℝ) : r_ergo M a 0 = r_plus M a := by
  unfold r_ergo r_plus; simp [Real.cos_zero]

-- 9. Ergosphere at equator reaches r = 2M
theorem ergo_equator (M a : ℝ) (hM : 0 ≤ M) : r_ergo M a (Real.pi / 2) = 2 * M := by
  unfold r_ergo
  simp [Real.cos_pi_div_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
  ring

-- 10. Sigma is nonneg everywhere
theorem sigma_nonneg (a r θ : ℝ) : Sigma a r θ ≥ 0 := by
  unfold Sigma
  positivity

-- 11. Schwarzschild area = 16πM²
theorem area_schwarzschild (M : ℝ) (hM : 0 ≤ M) : A_H M 0 = 16 * Real.pi * M ^ 2 := by
  unfold A_H r_plus
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
  ring

-- 12. No horizon rotation without spin
theorem no_horizon_spin (M : ℝ) : Ω_H M 0 = 0 := by
  unfold Ω_H; simp

-- 13. g_tt reduces to Schwarzschild when a = 0
theorem gtt_schwarzschild (M r θ : ℝ) (hr : r ≠ 0) :
    g_tt M 0 r θ = -(1 - 2 * M / r) := by
  unfold g_tt Sigma
  simp
  field_simp [hr]

end KerrTest
