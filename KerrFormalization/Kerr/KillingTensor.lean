import KerrFormalization.Kerr.BoyerLindquist
import KerrFormalization.Kerr.ComponentLemmas
import KerrFormalization.Kerr.Christoffel

/-!
# Kerr Killing tensor (Form C)

Form C of the Killing tensor, verified against the standard literature
(Kinnersley null vectors / Walker-Penrose) componentwise.

Form C: K_μν = -a²cos²θ · g_μν + r²Σ · (dθ)_μ(dθ)_ν + sin²θ · ω³_μ · ω³_ν
where ω³ = a dt - (r² + a²) dφ

Components (verified):
  K_tt = a² − 2Mra²cos²θ/Σ
  K_rr = −a²cos²θ · Σ/Δ
  K_θθ = r²Σ
  K_tφ = −aΔsin²θ + r² · g_tφ
  K_φφ = a²Δsin⁴θ + r² · g_φφ
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Killing tensor Form C components at a coordinate point.
    Uses explicit verified values, not the abstract formula,
    to avoid coefficient ambiguity in the (dθ)(dθ) term. -/
noncomputable def killingTensorFormC (M a : ℝ) (x : CoordinateSpace 4) :
    Fin 4 → Fin 4 → ℝ :=
  fun μ ν =>
    let r := x rIdx
    let θ := x thetaIdx
    let del := delta M a r
    let sigmaVal := sigma a r θ
    let s := Real.sin θ
    let c := Real.cos θ
    if μ = tIdx ∧ ν = tIdx then
      a ^ 2 - 2 * M * r * a ^ 2 * c ^ 2 / sigmaVal
    else if μ = rIdx ∧ ν = rIdx then
      -(a ^ 2 * c ^ 2 * sigmaVal / del)
    else if μ = thetaIdx ∧ ν = thetaIdx then
      r ^ 2 * sigmaVal
    else if (μ = tIdx ∧ ν = phiIdx) ∨ (μ = phiIdx ∧ ν = tIdx) then
      -(a * del * s ^ 2) +
        r ^ 2 * CoordinateMetricData.value (kerrMetricData M a) x tIdx phiIdx
    else if μ = phiIdx ∧ ν = phiIdx then
      a ^ 2 * del * s ^ 4 +
        r ^ 2 * CoordinateMetricData.value (kerrMetricData M a) x phiIdx phiIdx
    else
      0

/-- Killing tensor is symmetric. -/
theorem killingTensorFormC_symm (M a : ℝ) (x : CoordinateSpace 4)
    (μ ν : Fin 4) :
    killingTensorFormC M a x μ ν = killingTensorFormC M a x ν μ := by
  fin_cases μ <;> fin_cases ν <;>
    simp [killingTensorFormC, tIdx, rIdx, thetaIdx, phiIdx]

/-- Partial derivative of the Killing tensor: ∂_α K_μν.
    Aristotle should compute this from the explicit component definitions. -/
noncomputable def partialKillingTensorFormC (M a : ℝ) (x : CoordinateSpace 4)
    (α μ ν : Fin 4) : ℝ :=
  -- Placeholder: Aristotle will need to differentiate killingTensorFormC
  -- componentwise using the chain rule and the metric partial derivatives.
  0 -- TODO: Aristotle fills this with real derivatives

/-- Covariant derivative of Form C Killing tensor:
    ∇_α K_μν = ∂_α K_μν − Γ^σ_αμ K_σν − Γ^σ_αν K_μσ -/
noncomputable def covDerivKillingFormC (M a : ℝ) (x : CoordinateSpace 4)
    (α μ ν : Fin 4) : ℝ :=
  partialKillingTensorFormC M a x α μ ν
  - Finset.univ.sum (fun σ : Fin 4 =>
      kerrChristoffel M a x σ α μ * killingTensorFormC M a x σ ν)
  - Finset.univ.sum (fun σ : Fin 4 =>
      kerrChristoffel M a x σ α ν * killingTensorFormC M a x μ σ)

/-- The symmetrized Killing tensor equation: ∇_(α K_μν) = 0. -/
theorem symmetrized_killing_equation_formC (M a : ℝ)
    (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ α μ ν : Fin 4,
      covDerivKillingFormC M a x α μ ν +
      covDerivKillingFormC M a x μ ν α +
      covDerivKillingFormC M a x ν α μ = 0 := by
  clear hSigma hDelta hSin
  -- ATTEMPT: this should follow by expanding `partialKillingTensorFormC` from the
  -- exact component formulas and then simplifying the Christoffel sums, but the
  -- current file still has the derivative placeholder `0` and needs a real exact
  -- derivative expansion before the algebra can close.
  sorry

end Kerr
end KerrFormalization
