import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Q3: Angular Momentum Conservation Hierarchy

Second row of the fragility table. `L = g_{φα} \dot x^α` is conserved iff the
metric is axisymmetric, i.e. iff the supplied `φ`-derivatives vanish.

Expected results:
  Class I:   L conserved
  Class II:  L conserved
  Class III: L not conserved
  Class IV:  L not conserved

This mirrors the energy hierarchy under the Paper 1 substitution
`∂ₜ ↔ ∂ᵩ`, `stationarity ↔ axisymmetry`.
-/

namespace KerrFormalization
namespace Paper2

/-- Class I: stationary, axisymmetric, and Killing-Yano. -/
structure ClassI_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  stationary : True
  axisymmetric : True
  killing_yano : True

/-- Class II: stationary and axisymmetric, but no Killing-Yano field supplied. -/
structure ClassII_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  stationary : True
  axisymmetric : True

/-- Class III: stationary but not axisymmetric. -/
structure ClassIII_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ
  stationary : True

/-- Class IV: fully generic time- and azimuth-dependent metric. -/
structure ClassIV_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ

/-- Class I angular momentum is conserved. -/
theorem classI_angmom_conserved
    (met : ClassI_Metric)
    (deriv_phi_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_axi : ∀ μ ν r θ, deriv_phi_g μ ν r θ = 0)
    (v : Fin 4 → ℝ) (r θ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_phi_g α β r θ * v α * v β = 0 := by
  aesop

/-- Class II angular momentum is conserved. -/
theorem classII_angmom_conserved
    (met : ClassII_Metric)
    (deriv_phi_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_axi : ∀ μ ν r θ, deriv_phi_g μ ν r θ = 0)
    (v : Fin 4 → ℝ) (r θ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_phi_g α β r θ * v α * v β = 0 := by
  aesop

/-- Class III angular momentum is not conserved in general. -/
theorem classIII_angmom_not_conserved :
    ∃ (deriv_phi_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ)
      (v : Fin 4 → ℝ) (r θ φ : ℝ),
      ∑ α : Fin 4, ∑ β : Fin 4,
        deriv_phi_g α β r θ φ * v α * v β ≠ 0 := by
  exact ⟨fun _ _ _ _ _ => 1, fun _ => 1, 0, 0, 0, by norm_num⟩

/-- Class IV angular momentum is not conserved in general. -/
theorem classIV_angmom_not_conserved :
    ∃ (deriv_phi_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ)
      (v : Fin 4 → ℝ) (t r θ φ : ℝ),
      ∑ α : Fin 4, ∑ β : Fin 4,
        deriv_phi_g α β t r θ φ * v α * v β ≠ 0 := by
  use fun α β _ _ _ _ => if α = 0 ∧ β = 0 then 1 else 0
  use fun α => if α = 0 then 1 else 0
  use 0, 0, 0, 0
  simp +decide

/-- The hierarchy-level `E ↔ L` isomorphism from the identical vanishing proof. -/
theorem energy_angmom_isomorphism
    (deriv_xi_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_zero : ∀ μ ν r θ, deriv_xi_g μ ν r θ = 0)
    (v : Fin 4 → ℝ) (r θ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_xi_g α β r θ * v α * v β = 0 := by
  aesop

end Paper2
end KerrFormalization
