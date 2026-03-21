import KerrFormalization.Paper2.Round2ExplicitDefs
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Tactic

/-!
# Open Problem I: Johannsen-Psaltis Integrability

This file isolates a first-order Johannsen-Psaltis probe using the existing
Paper 2 radial infrastructure. The central question is whether the Kerr Form C
tensor survives the simplest `α₁₃` JP deviation in the live `(r,r,r)` sector.
-/

namespace KerrFormalization
namespace Paper2
namespace OpenProblems

open Kerr
open LocalCoordinates

/-- Kerr metric component evaluated at the Boyer-Lindquist sample point
`(t, r, θ, φ) = (0, r, θ, 0)`. -/
noncomputable def kerrMetricComponentAt (M a r θ : ℝ) (μ ν : Fin 4) : ℝ :=
  CoordinateMetricData.value (kerrMetricData M a) (round2Point r θ) μ ν

/-- The simplest Johannsen-Psaltis deviation profile `h(r,θ)` with only the
`α₁₃` mode turned on. -/
noncomputable def jpDeviation (M a α₁₃ r θ : ℝ) : ℝ :=
  let S := r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2
  α₁₃ * M ^ 3 * r / S ^ 2

/-- Leading-order Johannsen-Psaltis metric with only the `α₁₃` deformation. -/
noncomputable def jpMetric (M a α₁₃ r θ : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun μ ν =>
    let S := r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2
    let D := r ^ 2 - 2 * M * r + a ^ 2
    let h := jpDeviation M a α₁₃ r θ
    match μ.val, ν.val with
    | 0, 0 => -(1 - 2 * M * r / S) * (1 + h)
    | 0, 3 => -(2 * M * a * r * (Real.sin θ) ^ 2 / S) * (1 + h)
    | 3, 0 => -(2 * M * a * r * (Real.sin θ) ^ 2 / S) * (1 + h)
    | 1, 1 => S * (1 + h) / (D + a ^ 2 * h * (Real.sin θ) ^ 2)
    | 2, 2 => S
    | 3, 3 =>
        (Real.sin θ) ^ 2 *
          ((r ^ 2 + a ^ 2) ^ 2 - a ^ 2 * D * (Real.sin θ) ^ 2) / S * (1 + h)
    | _, _ => 0

/-- Sanity check: the simplified JP ansatz reduces to Kerr when `α₁₃ = 0`. -/
theorem jp_reduces_to_kerr
    (M a r θ : ℝ) (μ ν : Fin 4) :
    jpMetric M a 0 r θ μ ν = kerrMetricComponentAt M a r θ μ ν := by
  sorry

/-- A radial proxy for `Γ^r_{rr}` built from the JP `g_rr` entry alone. This
captures the live radial channel that powered Probe A. -/
noncomputable def jpApproxGamma_rrr (M a α₁₃ r θ : ℝ) : ℝ :=
  let grr := jpMetric M a α₁₃ r θ rIdx rIdx
  let dgrr := deriv (fun r' => jpMetric M a α₁₃ r' θ rIdx rIdx) r
  (1 / 2 : ℝ) * (1 / grr) * dgrr

/-- First-order JP proxy question: does the Kerr Form C radial component still
solve the live `(r,r,r)` channel once the JP `g_rr` perturbation is turned on? -/
theorem jp_killing_equation_111_proxy
    (M a α₁₃ r θ : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hα : α₁₃ ≠ 0)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hSig : sigma a r θ ≠ 0)
    (hDel : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    jpApproxGamma_rrr M a α₁₃ r θ *
      killingTensorFormCExplicit M a r θ rIdx rIdx = 0 := by
  sorry

/-- Stronger proxy question: does the JP radial channel admit any symmetric
tensor with a nonzero `K_rr` entry? -/
theorem jp_admits_any_killing_tensor_proxy
    (M a α₁₃ r θ : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hα : α₁₃ ≠ 0)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hSig : sigma a r θ ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∃ (K : Fin 4 → Fin 4 → ℝ),
      (∀ μ ν, K μ ν = K ν μ) ∧
      (jpApproxGamma_rrr M a α₁₃ r θ * K rIdx rIdx = 0) ∧
      (K rIdx rIdx ≠ 0) := by
  sorry

/-- Equatorial diagnostic: unlike the Paper 2 `cos²θ` obstruction, the JP
deviation itself does not vanish on the equator. -/
theorem jp_equatorial_deviation
    (M a r : ℝ)
    (hr : r ≠ 0) :
    jpDeviation M a 1 r (Real.pi / 2) = M ^ 3 / r ^ 3 := by
  sorry

end OpenProblems
end Paper2
end KerrFormalization
