import KerrFormalization.Paper2.Round2ExplicitDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Q4 Machine Discovery — Hardened

The original moonshot admitted a sparsity-only witness with `K_rr = 0`.
This retry forces the live radial channel to participate:

- the easy `(t,t,t)` contraction,
- the hard `(r,r,r)` contraction,
- the mixed hot `(r,t,t)` contraction,
- and the explicit requirement `K_rr ≠ 0`.

The theorem statement does not mention Form C. Any successful witness now has to
engage the same radial sector that made Probe A informative.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- Main hardened discovery target: construct a nontrivial symmetric tensor with
genuinely nonzero `K_rr` satisfying both easy and hard Kerr contraction tests.

The additional `hcos` hypothesis excludes the equatorial locus where the known
Form C witness has `K_rr = 0`, so the target is mathematically consistent. -/
theorem kerr_killing_tensor_with_Krr
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hSig : sigma a r θ ≠ 0)
    (hDel : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0)
    (hcos : Real.cos θ ≠ 0) :
    ∃ (K : Fin 4 → Fin 4 → ℝ),
      (∀ μ ν, K μ ν = K ν μ) ∧
      (∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ tIdx tIdx * K σ tIdx = 0) ∧
      (∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ rIdx rIdx * K σ rIdx = 0) ∧
      (∑ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ rIdx tIdx * K σ tIdx = 0) ∧
      (K rIdx rIdx ≠ 0) ∧
      (K rIdx rIdx * kerrInvMetricExplicit M a r θ tIdx tIdx ≠
        K tIdx tIdx * kerrInvMetricExplicit M a r θ rIdx rIdx) := by
  sorry

/-- Component-level obstruction: if the `σr` slice is zero away from `rr`, then
the hard `(r,r,r)` contraction cannot support a nonzero `K_rr` once
`Γ^r_{rr}` is live. This isolates exactly what the previous sparse witness was
missing. -/
theorem rrr_contraction_forces_Krr_channel
    (M a r θ : ℝ)
    (hGamma : kerrChristoffelExplicit M a r θ rIdx rIdx rIdx ≠ 0)
    (K : Fin 4 → Fin 4 → ℝ)
    (htr : K tIdx rIdx = 0)
    (hthr : K thetaIdx rIdx = 0)
    (hphir : K phiIdx rIdx = 0)
    (hcontr : ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx rIdx * K σ rIdx = 0) :
    K rIdx rIdx = 0 := by
  simp [Fin.sum_univ_four, htr, hthr, hphir] at hcontr
  exact (mul_eq_zero.mp hcontr).resolve_left hGamma

/-- Any valid hardened witness with `K_rr ≠ 0` must therefore activate at
least one nontrivial off-diagonal `σr` channel in the live radial equation. -/
theorem hardened_witness_needs_more_than_principal_null_ratio
    (M a r θ : ℝ)
    (hGamma : kerrChristoffelExplicit M a r θ rIdx rIdx rIdx ≠ 0)
    (K : Fin 4 → Fin 4 → ℝ)
    (hKrr : K rIdx rIdx ≠ 0)
    (hcontr : ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx rIdx * K σ rIdx = 0) :
    K tIdx rIdx ≠ 0 ∨ K thetaIdx rIdx ≠ 0 ∨ K phiIdx rIdx ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  exact hKrr (rrr_contraction_forces_Krr_channel M a r θ hGamma K hzero.1 hzero.2.1 hzero.2.2 hcontr)

end Paper2
end KerrFormalization
