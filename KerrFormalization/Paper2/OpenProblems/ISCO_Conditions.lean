import KerrFormalization.Paper2.Round2ExplicitDefs
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
# Open Problem II: ISCO Existence Conditions

This file formulates ISCO existence as a problem about the equatorial effective
potential. The key open question is which hypotheses, if any, beyond
stationarity and axisymmetry are needed for an ISCO to exist.
-/

namespace KerrFormalization
namespace Paper2
namespace OpenProblems

open Kerr
open LocalCoordinates

/-- Generic equatorial effective potential for a stationary axisymmetric metric
written in inverse-metric variables. -/
noncomputable def equatorialVeff
    (gtt_inv gtphi_inv gphiphi_inv : ℝ → ℝ)
    (E L : ℝ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (gtt_inv r * E ^ 2 + 2 * gtphi_inv r * E * L + gphiphi_inv r * L ^ 2 + 1)

/-- Circular orbit condition `dV_eff/dr = 0`. -/
noncomputable def circularOrbitCondition
    (gtt_inv gtphi_inv gphiphi_inv : ℝ → ℝ)
    (E L r : ℝ) : Prop :=
  deriv (equatorialVeff gtt_inv gtphi_inv gphiphi_inv E L) r = 0

/-- Stability condition `d²V_eff/dr² < 0`. -/
noncomputable def stabilityCondition
    (gtt_inv gtphi_inv gphiphi_inv : ℝ → ℝ)
    (E L r : ℝ) : Prop :=
  deriv (deriv (equatorialVeff gtt_inv gtphi_inv gphiphi_inv E L)) r < 0

/-- Equatorial inverse Kerr components for the `Δ_ε` deformation. -/
noncomputable def deformedInv_tt (M a ε : ℝ) : ℝ → ℝ :=
  fun r => invMetricDeformed M a r (Real.pi / 2) ε tIdx tIdx

noncomputable def deformedInv_tphi (M a ε : ℝ) : ℝ → ℝ :=
  fun r => invMetricDeformed M a r (Real.pi / 2) ε tIdx phiIdx

noncomputable def deformedInv_phiphi (M a ε : ℝ) : ℝ → ℝ :=
  fun r => invMetricDeformed M a r (Real.pi / 2) ε phiIdx phiIdx

/-- The Johannsen-Psaltis `α₁₃` deviation used for the equatorial ISCO probe. -/
noncomputable def jpDeviation (M a α₁₃ r θ : ℝ) : ℝ :=
  let S := r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2
  α₁₃ * M ^ 3 * r / S ^ 2

/-- The equatorial JP metric block. -/
noncomputable def jpMetricEq (M a α₁₃ : ℝ) : ℝ → Fin 4 → Fin 4 → ℝ :=
  fun r μ ν =>
    let θ := Real.pi / 2
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

/-- Inverse of the equatorial `t-φ` block for the JP metric. -/
noncomputable def jpDetEq (M a α₁₃ : ℝ) : ℝ → ℝ :=
  fun r =>
    jpMetricEq M a α₁₃ r tIdx tIdx * jpMetricEq M a α₁₃ r phiIdx phiIdx
      - jpMetricEq M a α₁₃ r tIdx phiIdx ^ 2

noncomputable def jpInv_tt (M a α₁₃ : ℝ) : ℝ → ℝ :=
  fun r => jpMetricEq M a α₁₃ r phiIdx phiIdx / jpDetEq M a α₁₃ r

noncomputable def jpInv_tphi (M a α₁₃ : ℝ) : ℝ → ℝ :=
  fun r => -jpMetricEq M a α₁₃ r tIdx phiIdx / jpDetEq M a α₁₃ r

noncomputable def jpInv_phiphi (M a α₁₃ : ℝ) : ℝ → ℝ :=
  fun r => jpMetricEq M a α₁₃ r tIdx tIdx / jpDetEq M a α₁₃ r

/-- Baseline open problem: can one prove existence of an ISCO from generic
asymptotics and smoothness alone? -/
theorem generic_isco_exists
    (gtt_inv gtphi_inv gphiphi_inv : ℝ → ℝ)
    (h_asymp_tt : Filter.Tendsto gtt_inv Filter.atTop (nhds (-1)))
    (h_asymp_tphi : Filter.Tendsto gtphi_inv Filter.atTop (nhds 0))
    (h_smooth_tt : Differentiable ℝ gtt_inv)
    (h_smooth_tphi : Differentiable ℝ gtphi_inv)
    (h_smooth_phiphi : Differentiable ℝ gphiphi_inv)
    (r_H : ℝ) (hr_H : r_H > 0)
    (h_horizon : Filter.Tendsto gtt_inv (nhds r_H) Filter.atTop) :
    ∃ (E L r_isco : ℝ),
      r_isco > r_H ∧
      circularOrbitCondition gtt_inv gtphi_inv gphiphi_inv E L r_isco ∧
      deriv (deriv (equatorialVeff gtt_inv gtphi_inv gphiphi_inv E L)) r_isco = 0 := by
  sorry

/-- Paper 2 diagnostic: does the equatorial ISCO survive the `Δ ↦ Δ + ε r`
deformation even though the full Carter constant fails away from the equator? -/
theorem deformed_kerr_isco_exists
    (M a ε : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hε : |ε| < M) :
    ∃ (E L r_isco : ℝ),
      r_isco > 0 ∧
      circularOrbitCondition (deformedInv_tt M a ε) (deformedInv_tphi M a ε)
        (deformedInv_phiphi M a ε) E L r_isco ∧
      deriv (deriv
        (equatorialVeff (deformedInv_tt M a ε) (deformedInv_tphi M a ε)
          (deformedInv_phiphi M a ε) E L)) r_isco = 0 := by
  sorry

/-- Johannsen-Psaltis ISCO probe using the exact inverse of the equatorial
`t-φ` block. -/
theorem jp_isco_exists
    (M a α₁₃ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hα : |α₁₃| < 1) :
    ∃ (E L r_isco : ℝ),
      r_isco > 0 ∧
      circularOrbitCondition (jpInv_tt M a α₁₃) (jpInv_tphi M a α₁₃)
        (jpInv_phiphi M a α₁₃) E L r_isco ∧
      deriv (deriv
        (equatorialVeff (jpInv_tt M a α₁₃) (jpInv_tphi M a α₁₃)
          (jpInv_phiphi M a α₁₃) E L)) r_isco = 0 := by
  sorry

end OpenProblems
end Paper2
end KerrFormalization
