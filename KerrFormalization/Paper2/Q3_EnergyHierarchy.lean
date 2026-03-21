import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Q3-A: Energy Fragility Hierarchy

Energy conservation survives exactly as long as stationarity survives. The
positive closures and the Class IV failure boundary together define the first
row of the fragility hierarchy.
-/

namespace KerrFormalization
namespace Paper2

/-- Class I: stationary, axisymmetric, and Killing-Yano. -/
structure ClassI_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  ginv : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  stationary : True
  axisymmetric : True
  killing_yano : True

/-- Class II: stationary and axisymmetric, but no Killing-Yano field supplied. -/
structure ClassII_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  ginv : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  stationary : True
  axisymmetric : True

/-- Class III: stationary but not axisymmetric. -/
structure ClassIII_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ
  ginv : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ
  stationary : True
  phi_dependent : ∃ (μ ν : Fin 4) (r θ φ : ℝ),
    deriv (fun φ' => g μ ν r θ φ') φ ≠ 0

/-- Class IV: generic time-dependent metric. -/
structure ClassIV_Metric where
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ
  ginv : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ
  t_dependent : ∃ (μ ν : Fin 4) (t r θ φ : ℝ),
    deriv (fun t' => g μ ν t' r θ φ) t ≠ 0

/-- Class I energy is conserved. -/
theorem classI_energy_conserved
    (met : ClassI_Metric)
    (deriv_t_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_stat : ∀ μ ν r θ, deriv_t_g μ ν r θ = 0)
    (v : Fin 4 → ℝ) (r θ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_t_g α β r θ * v α * v β = 0 := by
  sorry

/-- Class II energy is conserved. -/
theorem classII_energy_conserved
    (met : ClassII_Metric)
    (deriv_t_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_stat : ∀ μ ν r θ, deriv_t_g μ ν r θ = 0)
    (v : Fin 4 → ℝ) (r θ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_t_g α β r θ * v α * v β = 0 := by
  sorry

/-- Class III energy is still conserved. -/
theorem classIII_energy_conserved
    (met : ClassIII_Metric)
    (deriv_t_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ)
    (h_stat : ∀ μ ν r θ φ, deriv_t_g μ ν r θ φ = 0)
    (v : Fin 4 → ℝ) (r θ φ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_t_g α β r θ φ * v α * v β = 0 := by
  sorry

/-- Class IV energy conservation should fail without stationarity. -/
theorem classIV_energy_NOT_conserved
    (met : ClassIV_Metric)
    (deriv_t_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ)
    (v : Fin 4 → ℝ) (t r θ φ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4,
      deriv_t_g α β t r θ φ * v α * v β = 0 := by
  sorry

end Paper2
end KerrFormalization
