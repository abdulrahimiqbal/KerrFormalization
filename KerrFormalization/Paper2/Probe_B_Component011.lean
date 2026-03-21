import KerrFormalization.Paper2.Round2ExplicitDefs

open scoped BigOperators

/-!
# Probe B: Killing Equation Component `(0,1,1)`

Paper 2 Round 2 mixed time-radial probe. The goal here is to determine whether
the Christoffel contraction in the `(t,r,r)` component already vanishes, or
whether it survives and therefore has to cancel against derivative terms in the
full symmetrized Killing equation.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- Exact Kerr, the Christoffel contraction from the `(t,r,r)` component. -/
theorem killing_equation_011_christoffel_part
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : sigma a r θ ≠ 0)
    (hΔ : delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r θ σ tIdx rIdx *
        killingTensorFormCExplicit M a r θ σ rIdx = 0 := by
  have hzero :
      ∀ σ : Fin 4,
        kerrChristoffelExplicit M a r θ σ tIdx rIdx *
          killingTensorFormCExplicit M a r θ σ rIdx = 0 := by
    intro σ
    by_cases hσ : σ = tIdx ∨ σ = rIdx ∨ σ = thetaIdx ∨ σ = phiIdx
    · aesop (simp_config := { decide := true })
    · fin_cases σ <;> contradiction
  exact Finset.sum_eq_zero fun σ _ => hzero σ

end Paper2
end KerrFormalization
