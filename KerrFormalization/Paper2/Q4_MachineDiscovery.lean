import KerrFormalization.Paper2.Round2ExplicitDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-!
# Q4: Machine Discovery — Open-Ended Killing Tensor Search

The methodological moonshot: give Aristotle the metric, the Christoffel
symbols, and the Killing-equation constraints, but do not provide a Killing
tensor witness.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- Existence of a nontrivial symmetric tensor satisfying several live Kerr components. -/
theorem kerr_has_nontrivial_killing_tensor
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∃ (K : Fin 4 → Fin 4 → ℝ),
      (∀ μ ν, K μ ν = K ν μ) ∧
      (∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ rIdx rIdx * K σ rIdx = 0) ∧
      (∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ tIdx tIdx * K σ tIdx = 0) ∧
      (∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ rIdx tIdx * K σ tIdx = 0) ∧
      (K rIdx rIdx * kerrInvMetricExplicit M a r θ tIdx tIdx ≠
        K tIdx tIdx * kerrInvMetricExplicit M a r θ rIdx rIdx) := by
  sorry

/-- Uniqueness question: are two such tensors related up to the metric? -/
theorem killing_tensor_unique_up_to_metric
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a > 0)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (K₁ K₂ : Fin 4 → Fin 4 → ℝ)
    (h1_sym : ∀ μ ν, K₁ μ ν = K₁ ν μ)
    (h2_sym : ∀ μ ν, K₂ μ ν = K₂ ν μ)
    (h1_killing : ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx rIdx * K₁ σ rIdx = 0)
    (h2_killing : ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx rIdx * K₂ σ rIdx = 0)
    (h1_nontriv : ∃ μ ν, K₁ μ ν ≠ 0)
    (h2_nontriv : ∃ μ ν, K₂ μ ν ≠ 0) :
    ∃ (α β : ℝ), ∀ μ ν,
      K₂ μ ν = α * K₁ μ ν + β * kerrInvMetricExplicit M a r θ μ ν := by
  sorry

/-- Semi-guided discovery: fill in the off-diagonal slots from partial data. -/
theorem fill_in_killing_tensor
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a > 0)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0)
    (K_tt : ℝ)
    (K_rr : ℝ) :
    ∃ (K_tphi K_phiphi : ℝ),
      let K : Fin 4 → Fin 4 → ℝ := fun μ ν =>
        match μ.val, ν.val with
        | 0, 0 => K_tt
        | 1, 1 => K_rr
        | 2, 2 => 0
        | 0, 3 => K_tphi
        | 3, 0 => K_tphi
        | 3, 3 => K_phiphi
        | _, _ => 0
      ∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ rIdx tIdx *
          K σ tIdx = 0 := by
  sorry

end Paper2
end KerrFormalization
