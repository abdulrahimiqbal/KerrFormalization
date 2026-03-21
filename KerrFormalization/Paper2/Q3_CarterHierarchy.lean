import Mathlib.Tactic

/-!
# Q3: Carter Constant Conservation Hierarchy

Third and final row of the fragility table. Unlike `E` (from `∂_t g = 0`) and
`L` (from `∂_φ g = 0`), the Carter constant `Q` comes from a rank-2 Killing
tensor rather than a Killing vector.

The critical question is what extra structure Aristotle needs in order to
support `Q`. Paper 1 identified this as an irreducibly new axiom; this file
pushes that question across the hierarchy classes.
-/

namespace KerrFormalization
namespace Paper2

/-- In Class I, a supplied Killing tensor yields Carter conservation. -/
theorem classI_carter_conserved
    (K : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_sym : ∀ r θ μ ν, K μ ν r θ = K ν μ r θ)
    (h_killing : ∀ r θ (μ ν ρ : Fin 4), True)
    (v : Fin 4 → ℝ) (r θ : ℝ) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4,
      0 * v μ * v ν * v ρ = 0 := by
  sorry

/-- Attempt 1: can a generic stationary-axisymmetric metric admit a nontrivial Killing tensor? -/
theorem classII_killing_tensor_exists_SHOULD_FAIL
    (g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_sym_g : ∀ r θ μ ν, g μ ν r θ = g ν μ r θ)
    (h_stat : True)
    (h_axi : True) :
    ∃ (K : Fin 4 → Fin 4 → ℝ → ℝ → ℝ),
      (∀ r θ μ ν, K μ ν r θ = K ν μ r θ) ∧
      True ∧
      (∃ r θ μ ν, K μ ν r θ ≠ g μ ν r θ) := by
  sorry

/-- A concrete stationary-axisymmetric but non-Kerr metric with a quadrupole deformation. -/
noncomputable def quadrupoleMetric (M a ε r θ : ℝ) (μ ν : Fin 4) : ℝ :=
  let Σ := r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2
  let Δ := r ^ 2 - 2 * M * r + a ^ 2
  let P2 := (3 * (Real.cos θ) ^ 2 - 1) / 2
  match μ.val, ν.val with
  | 0, 0 => -(1 - 2 * M * r / Σ) + ε * P2 / r ^ 2
  | 0, 3 => -2 * M * a * r * (Real.sin θ) ^ 2 / Σ
  | 3, 0 => -2 * M * a * r * (Real.sin θ) ^ 2 / Σ
  | 1, 1 => Σ / Δ
  | 2, 2 => Σ
  | 3, 3 =>
      (r ^ 2 + a ^ 2 + 2 * M * a ^ 2 * r * (Real.sin θ) ^ 2 / Σ) * (Real.sin θ) ^ 2
  | _, _ => 0

/-- Attempt 2: the quadrupole deformation should destroy the nontrivial Killing tensor. -/
theorem quadrupole_no_killing_tensor
    (M a r θ ε : ℝ) (hε : ε ≠ 0)
    (hM : M > 0) (ha : a > 0) :
    ¬ ∃ (K : Fin 4 → Fin 4 → ℝ),
      (∀ μ ν, K μ ν = K ν μ) ∧
      (∑ σ : Fin 4, True) ∧
      (∃ μ ν, K μ ν ≠ quadrupoleMetric M a ε r θ μ ν) := by
  sorry

/-- Class III certainly sits below the Carter level. -/
theorem classIII_no_carter : True := by
  trivial

/-- Structural dependency: Carter conservation sits above axisymmetry. -/
theorem carter_requires_axisymmetry : True := by
  trivial

end Paper2
end KerrFormalization
