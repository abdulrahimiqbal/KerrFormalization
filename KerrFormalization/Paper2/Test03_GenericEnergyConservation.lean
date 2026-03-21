import KerrFormalization.Kerr.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Test 03: Energy Conservation from Stationarity Alone

Paper 2 core calibration. For a metric whose supplied `t`-derivatives vanish,
the quadratic expression that appears on the right-hand side of the energy
conservation computation should collapse to zero by pure simplification.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Paper2

/-- A generic stationary metric package, with the time-independence encoded in
the absence of an explicit `t` coordinate in the component functions. -/
structure StationaryMetricData where
  /-- Metric components `g(α, β, r, θ)`. -/
  g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  /-- Inverse metric components. -/
  ginv : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  /-- Placeholder witness that the family is intended to be stationary. -/
  stationary : True
  /-- Non-degeneracy packaged minimally for the test harness. -/
  nondegenerate : ∀ r θ : ℝ, ∃ D : ℝ, D ≠ 0

/-- If all supplied `t`-derivatives vanish, then the energy RHS vanishes. -/
theorem stationarity_implies_energy_rhs_zero
    (met : StationaryMetricData)
    (deriv_t_g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ)
    (h_stationary : ∀ μ ν r θ, deriv_t_g μ ν r θ = 0)
    (v : Fin 4 → ℝ)
    (r θ : ℝ) :
    ∑ α : Fin 4, ∑ β : Fin 4, deriv_t_g α β r θ * v α * v β = 0 := by
  sorry

end Paper2
end KerrFormalization
