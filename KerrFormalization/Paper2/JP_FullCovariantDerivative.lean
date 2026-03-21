import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# JP Full Covariant Derivative — The Closing Argument

The key observation is connection-theoretic, not Kerr-specific:
if the tensor `K` is fixed and only the connection changes, then the partial
derivative terms cancel in the difference of the two covariant derivatives.

This file formalizes that cancellation and the special diagonal case relevant to
the Johannsen-Psaltis equatorial argument.
-/

noncomputable section

open scoped BigOperators

/-- Difference of two covariant derivatives acting on the same `(0,2)` tensor. -/
theorem covariant_derivative_difference
    (T : Fin 4 → Fin 4 → ℝ)
    (Gamma1 Gamma2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (alpha beta gamma : Fin 4) :
    (dT alpha beta gamma - ∑ sigma : Fin 4, Gamma1 sigma alpha beta * T sigma gamma
       - ∑ sigma : Fin 4, Gamma1 sigma alpha gamma * T beta sigma) -
      (dT alpha beta gamma - ∑ sigma : Fin 4, Gamma2 sigma alpha beta * T sigma gamma
       - ∑ sigma : Fin 4, Gamma2 sigma alpha gamma * T beta sigma) =
      -(∑ sigma : Fin 4, (Gamma1 sigma alpha beta - Gamma2 sigma alpha beta) * T sigma gamma) -
       (∑ sigma : Fin 4, (Gamma1 sigma alpha gamma - Gamma2 sigma alpha gamma) * T beta sigma) := by
  ring_nf
  rw [sub_eq_add_neg]
  ring

/-- If `K` is Killing for `GammaKerr`, then the full residual for `GammaJP`
is exactly the Christoffel-contraction residual. -/
theorem killing_residual_is_christoffel_contraction
    (K : Fin 4 → Fin 4 → ℝ)
    (GammaJP GammaKerr : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dK : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (alpha beta gamma : Fin 4)
    (h_killing :
      dK alpha beta gamma - ∑ sigma : Fin 4, GammaKerr sigma alpha beta * K sigma gamma
        - ∑ sigma : Fin 4, GammaKerr sigma alpha gamma * K beta sigma = 0) :
    dK alpha beta gamma - ∑ sigma : Fin 4, GammaJP sigma alpha beta * K sigma gamma
      - ∑ sigma : Fin 4, GammaJP sigma alpha gamma * K beta sigma =
      -(∑ sigma : Fin 4, (GammaJP sigma alpha beta - GammaKerr sigma alpha beta) * K sigma gamma) -
       (∑ sigma : Fin 4, (GammaJP sigma alpha gamma - GammaKerr sigma alpha gamma) * K beta sigma) := by
  have hdiff := covariant_derivative_difference K GammaJP GammaKerr dK alpha beta gamma
  rw [h_killing, sub_zero] at hdiff
  exact hdiff

/-- Diagonal specialization: for `beta = gamma`, symmetry of `K` makes the two
Christoffel-contraction sums identical. -/
theorem diagonal_residual_formula
    (K : Fin 4 → Fin 4 → ℝ)
    (GammaJP GammaKerr : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dK : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (alpha beta : Fin 4)
    (h_sym : ∀ mu nu : Fin 4, K mu nu = K nu mu)
    (h_killing :
      dK alpha beta beta - ∑ sigma : Fin 4, GammaKerr sigma alpha beta * K sigma beta
        - ∑ sigma : Fin 4, GammaKerr sigma alpha beta * K beta sigma = 0) :
    dK alpha beta beta - ∑ sigma : Fin 4, GammaJP sigma alpha beta * K sigma beta
      - ∑ sigma : Fin 4, GammaJP sigma alpha beta * K beta sigma =
      -2 * (∑ sigma : Fin 4, (GammaJP sigma alpha beta - GammaKerr sigma alpha beta) * K sigma beta) := by
  rw [killing_residual_is_christoffel_contraction K GammaJP GammaKerr dK alpha beta beta h_killing]
  congr 1
  ext sigma
  rw [h_sym beta sigma]
  ring

/-- Closing theorem: for a diagonal component, a nonzero Christoffel
contraction residual already forces the full JP covariant derivative residual to
be nonzero. No `∂K` cancellation remains. -/
theorem jp_full_killing_equation_breaks_equatorially
    (K : Fin 4 → Fin 4 → ℝ)
    (GammaJP GammaKerr : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dK : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (alpha beta : Fin 4)
    (h_sym : ∀ mu nu : Fin 4, K mu nu = K nu mu)
    (h_kerr_killing :
      dK alpha beta beta - ∑ sigma : Fin 4, GammaKerr sigma alpha beta * K sigma beta
        - ∑ sigma : Fin 4, GammaKerr sigma alpha beta * K beta sigma = 0)
    (h_contraction_nonzero :
      ∑ sigma : Fin 4, (GammaJP sigma alpha beta - GammaKerr sigma alpha beta) * K sigma beta ≠ 0) :
    dK alpha beta beta - ∑ sigma : Fin 4, GammaJP sigma alpha beta * K sigma beta
      - ∑ sigma : Fin 4, GammaJP sigma alpha beta * K beta sigma ≠ 0 := by
  rw [diagonal_residual_formula K GammaJP GammaKerr dK alpha beta h_sym h_kerr_killing]
  apply mul_ne_zero
  · norm_num
  · exact h_contraction_nonzero

end
