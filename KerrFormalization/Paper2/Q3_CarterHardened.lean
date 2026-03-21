import KerrFormalization.Paper2.Round2ExplicitDefs
import KerrFormalization.Paper2.Probe_A_Component111
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Q3 Carter Hierarchy — Hardened

This retry removes the fake `True` Killing-equation placeholder and uses the
live `(r,r,r)` Christoffel contraction from Probe A.

The exact-Kerr side is a real Class I witness. The generic side is phrased as a
sharp obstruction theorem: any candidate that tries to satisfy the live radial
component purely by sparsity cannot keep a nonzero `K_rr` channel once
`Γ^r_{rr}` is genuinely live.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- In exact Kerr, the explicit Form C tensor gives a genuine witness for the
live `(r,r,r)` component, provided we stay away from the equatorial locus where
`K_rr` itself vanishes. -/
theorem classI_carter_conserved_real
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
        kerrChristoffelExplicit M a r θ σ rIdx rIdx *
          K σ rIdx = 0) ∧
      (K rIdx rIdx ≠ 0) := by
  refine ⟨fun μ ν => killingTensorFormCExplicit M a r θ μ ν, ?_, ?_, ?_⟩
  · intro μ ν
    fin_cases μ <;> fin_cases ν <;> simp [killingTensorFormCExplicit]
  · simpa using killing_equation_111_kerr M a r θ hM (le_of_lt ha) haM hr hθ hSig hDel hsin
  · simp [killingTensorFormCExplicit, rIdx]
    exact div_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (neg_ne_zero.mpr (sq_ne_zero_of_ne_zero ha.ne'))
          (sq_ne_zero_of_ne_zero hcos))
        hSig)
      hDel

/-- Hardened obstruction: if the only possibly nonzero `σr` entry is the radial
one itself, then a live `(r,r,r)` contraction forces `K_rr = 0`.

This blocks the previous "mostly-zero witness" strategy from masquerading as a
Class II Carter tensor once the real Probe A component is imposed. -/
theorem classII_sparsity_ansatz_blocked
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

/-- The same obstruction, stated in the form most relevant to the hierarchy:
any candidate with a genuinely nonzero `K_rr` must activate more than the
trivial sparsity pattern in the `σr` slice. -/
theorem classII_nonzero_Krr_needs_live_radial_coupling
    (M a r θ : ℝ)
    (hGamma : kerrChristoffelExplicit M a r θ rIdx rIdx rIdx ≠ 0)
    (K : Fin 4 → Fin 4 → ℝ)
    (hKrr : K rIdx rIdx ≠ 0)
    (hcontr : ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ rIdx rIdx * K σ rIdx = 0) :
    K tIdx rIdx ≠ 0 ∨ K thetaIdx rIdx ≠ 0 ∨ K phiIdx rIdx ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  exact hKrr (classII_sparsity_ansatz_blocked M a r θ hGamma K hzero.1 hzero.2.1 hzero.2.2 hcontr)

end Paper2
end KerrFormalization
