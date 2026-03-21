import KerrFormalization.Paper2.Round2ExplicitDefs

open scoped BigOperators

/-!
# Probe C: Killing Equation Component `(1,3,3)`

Paper 2 Round 2 radial-azimuthal probe. This is the highest-sensitivity
Christoffel-only target in the current batch because both `K_{φφ}` and the
relevant `Γ^σ_{rφ}` / `Γ^σ_{φφ}` terms carry explicit `Δ` dependence.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- Exact Kerr, the `∇_r K_{φφ}` contraction piece `Σ_σ Γ^σ_{rφ} K_{σφ}`. -/
theorem killing_equation_133_contraction_A
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx phiIdx *
        killingTensorFormCExplicit M a r θ σ phiIdx = 0 := by
  sorry

/-- Exact Kerr, the full Christoffel contribution in the symmetrized `(r,φ,φ)` equation. -/
theorem killing_equation_133_full_christoffel
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx phiIdx *
          killingTensorFormCExplicit M a r θ σ phiIdx +
        kerrChristoffelExplicit M a r θ σ rIdx phiIdx *
          killingTensorFormCExplicit M a r θ phiIdx σ) +
    2 * (∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ phiIdx rIdx *
          killingTensorFormCExplicit M a r θ σ phiIdx +
        kerrChristoffelExplicit M a r θ σ phiIdx phiIdx *
          killingTensorFormCExplicit M a r θ rIdx σ) = 0 := by
  sorry

end Paper2
end KerrFormalization
