import KerrFormalization.Paper2.Round2ExplicitDefs

open scoped BigOperators

/-!
# Probe A: Killing Equation Component `(1,1,1)`

Paper 2 Round 2 prime target. This file uses the explicit Kerr and deformed
`Δ_ε` component formulas from `Round2ExplicitDefs` so that the radial sector is
actually `Δ`-sensitive.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

private lemma fin4_sum (f : Fin 4 → ℝ) :
    ∑ s : Fin 4, f s = f 0 + f 1 + f 2 + f 3 := by
  exact Fin.sum_univ_four f

section ExactKerr

/-- The `(r,r,r)` Christoffel-Killing contraction in exact Kerr. -/
theorem killing_equation_111_kerr
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx rIdx *
        killingTensorFormCExplicit M a r θ σ rIdx = 0 := by
  unfold kerrChristoffelExplicit killingTensorFormCExplicit
  simp +decide [Fin.sum_univ_four]

end ExactKerr

section DeformedKerr

/-- The `rr` Christoffel slice for the deformed `Δ_ε` model. -/
noncomputable def christoffelDeformed_rr (M a r θ ε : ℝ) (σ : Fin 4) : ℝ :=
  christoffelDeformed M a r θ ε σ rIdx rIdx

/-- The `σr` slice of the deformed Form C tensor. -/
noncomputable def killingTensorDeformed_r (M a r θ ε : ℝ) (σ : Fin 4) : ℝ :=
  killingTensorDeformed M a r θ ε σ rIdx

/-- The `(r,r,r)` contraction in the deformed `Δ_ε` model. -/
theorem killing_equation_111_deformed_value
    (M a r θ ε : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : sigma a r θ ≠ 0)
    (hΔε : DeltaEps M a r ε ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∑ σ : Fin 4,
      christoffelDeformed_rr M a r θ ε σ *
        killingTensorDeformed_r M a r θ ε σ =
    2 * a ^ 2 * (Real.cos θ) ^ 2 * kerrN M a r θ / (delta M a r) ^ 2 -
    2 * a ^ 2 * (Real.cos θ) ^ 2 * (kerrN M a r θ + r * ε) /
      (DeltaEps M a r ε * delta M a r) := by
  simp only [fin4_sum]
  simp only [christoffelDeformed_rr, killingTensorDeformed_r,
    christoffelDeformed, killingTensorDeformed]
  simp +decide
  ring

-- The original `killing_equation_111_deformed` claim that the deformed
-- contraction vanishes unconditionally is false for `ε ≠ 0`. The explicit
-- value above is generically nonzero and isolates the first Paper 2 boundary.

/-- The deformed sum factored as a single `ε`-dependent product. -/
private lemma deformed_sum_eq_eps_factor
    (M a r θ ε : ℝ)
    (hΔ : delta M a r ≠ 0)
    (hΔε : DeltaEps M a r ε ≠ 0) :
    2 * a ^ 2 * (Real.cos θ) ^ 2 * kerrN M a r θ / (delta M a r) ^ 2 -
    2 * a ^ 2 * (Real.cos θ) ^ 2 * (kerrN M a r θ + r * ε) /
      (DeltaEps M a r ε * delta M a r) =
    2 * a ^ 2 * (Real.cos θ) ^ 2 * ε * (kerrN M a r θ - r * delta M a r) /
      ((delta M a r) ^ 2 * DeltaEps M a r ε) := by
  rw [div_sub_div, div_eq_div_iff] <;> first | positivity | ring
  rw [show DeltaEps M a r ε = delta M a r + ε * r by rfl]
  ring

/-- Key algebraic identity: `N - rΔ = -(r - M)Σ`. -/
private lemma kerrN_sub_r_delta (M a r θ : ℝ) :
    kerrN M a r θ - r * delta M a r = -(r - M) * sigma a r θ := by
  unfold kerrN delta sigma
  ring

/-- Diagnostic version: if the deformed contraction still vanishes, does that force `ε = 0`? -/
theorem killing_equation_111_deformed_diagnostic
    (M a r θ ε : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hrM : r ≠ M)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hΔε : DeltaEps M a r ε ≠ 0)
    (hsin : Real.sin θ ≠ 0)
    (hcos : Real.cos θ ≠ 0) :
    (∑ σ : Fin 4,
      christoffelDeformed_rr M a r θ ε σ *
        killingTensorDeformed_r M a r θ ε σ = 0) →
    ε = 0 := by
  intro h
  have hsum :
      2 * a ^ 2 * (Real.cos θ) ^ 2 * ε * (kerrN M a r θ - r * delta M a r) /
        ((delta M a r) ^ 2 * DeltaEps M a r ε) = 0 := by
    rw [← h, killing_equation_111_deformed_value]
    · convert (deformed_sum_eq_eps_factor M a r θ ε hΔ hΔε).symm using 1
    · exact hM
    · exact le_of_lt ha
    · exact haM
    · exact hr
    · exact hθ
    · exact hΣ
    · exact hΔε
    · exact hsin
  simp_all +decide [mul_assoc, mul_eq_zero, div_eq_iff]
  have hε_or_core : ε = 0 ∨ kerrN M a r θ - r * delta M a r = 0 := by
    exact hsum.resolve_left ha.ne'
  exact hε_or_core.resolve_right (by
    rw [kerrN_sub_r_delta]
    exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hrM)) hΣ)

end DeformedKerr

end Paper2
end KerrFormalization
