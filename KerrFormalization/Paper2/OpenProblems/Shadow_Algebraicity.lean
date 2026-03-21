import KerrFormalization.Paper2.Round2ExplicitDefs
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Tactic

/-!
# Open Problem III: Shadow Algebraicity

This file probes whether the Kerr shadow parameterization survives beyond the
integrable case. The central question is whether the radial equations still
determine a smooth one-parameter family of critical photon data after the
Paper 2 deformation.
-/

namespace KerrFormalization
namespace Paper2
namespace OpenProblems

/-- Null radial potential for Kerr photons. -/
noncomputable def radialPotentialNull (M a E L Q r : ℝ) : ℝ :=
  let D := r ^ 2 - 2 * M * r + a ^ 2
  ((r ^ 2 + a ^ 2) * E - a * L) ^ 2 - D * ((a * E - L) ^ 2 + Q)

/-- Deformed null radial potential with `Δ_ε = Δ + εr`. -/
noncomputable def radialPotentialDeformed (M a ε E L Q r : ℝ) : ℝ :=
  let Dε := r ^ 2 - 2 * M * r + a ^ 2 + ε * r
  ((r ^ 2 + a ^ 2) * E - a * L) ^ 2 - Dε * ((a * E - L) ^ 2 + Q)

/-- Kerr baseline: for each allowed photon-orbit radius one can solve the
two criticality equations `R = 0` and `R' = 0` for the impact data. -/
theorem kerr_shadow_parameterization_exists
    (M a : ℝ) (hM : M > 0) (ha : a ≥ 0) (haM : a < M) :
    ∀ r_ph : ℝ, r_ph > 0 →
      ∃ (ℓ q_sq : ℝ),
        radialPotentialNull M a 1 ℓ q_sq r_ph = 0 ∧
        deriv (radialPotentialNull M a 1 ℓ q_sq) r_ph = 0 ∧
        q_sq ≥ 0 := by
  sorry

/-- Main open deformation question: do the two criticality equations still
define a one-parameter family of photon data after integrability is broken? -/
theorem deformed_shadow_parameterization
    (M a ε : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hε : ε ≠ 0) :
    ∀ r_ph : ℝ, r_ph > 0 →
      ∃ (ℓ q_sq : ℝ),
        radialPotentialDeformed M a ε 1 ℓ q_sq r_ph = 0 ∧
        deriv (radialPotentialDeformed M a ε 1 ℓ q_sq) r_ph = 0 := by
  sorry

/-- First-order epsilon sensitivity of the deformed radial potential. This is
the algebraic input behind any linear shadow-shift formula. -/
theorem shadow_shift_linear_in_epsilon
    (M a L Q r_ph : ℝ) :
    deriv (fun ε => radialPotentialDeformed M a ε 1 L Q r_ph) 0 =
      -r_ph * ((a - L) ^ 2 + Q) := by
  sorry

/-- A weak formal chaos probe: does the twice-differentiated deformed radial
potential acquire additional critical points? New critical points would signal
a more complicated photon-ring structure than the Kerr one-parameter family. -/
theorem shadow_chaos_criterion
    (M a ε L Q : ℝ)
    (hM : M > 0) (ha : a > 0) (hε : ε ≠ 0) :
    ∃ r_crit : ℝ,
      deriv (fun r => deriv (radialPotentialDeformed M a ε 1 L Q) r) r_crit = 0 := by
  sorry

end OpenProblems
end Paper2
end KerrFormalization
