import KerrFormalization.Kerr.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Test 02: Sigma Derivative Probe

Paper 2 calibration. Can Aristotle verify that `∂Σ/∂r = 2r`,
where `Σ = r² + a² cos² θ`? This probes the boundary between
algebraic Kerr identities and analysis-level derivative reasoning.
-/

namespace KerrFormalization
namespace Paper2

/-- `Σ(r, θ) = r² + a² cos² θ`. -/
noncomputable def Sigma (a r θ : ℝ) : ℝ :=
  r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2

/-- For fixed `a, θ`, the derivative of `r ↦ Σ(a, r, θ)` is `2r`. -/
theorem sigma_deriv_r (a θ r : ℝ) :
    HasDerivAt (fun r' => Sigma a r' θ) (2 * r) r := by
  sorry

/-- Algebraic finite-difference form of the same identity. -/
theorem sigma_difference (a r h θ : ℝ) :
    Sigma a (r + h) θ - Sigma a r θ = 2 * r * h + h ^ 2 := by
  sorry

end Paper2
end KerrFormalization
