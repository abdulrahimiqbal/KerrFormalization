import Mathlib

/-!
# Symmetrized Killing Tensor Equation for Kerr

## Corrected Killing tensor formula

The original submission used `K_{μν} = r² g_{μν} + Δ Σ δ^r_μ δ^r_ν`, which is
**not** the correct Killing tensor for the Kerr spacetime. Numerical verification
confirmed that formula does NOT satisfy ∇_{(α} K_{μν)} = 0.

The correct Killing tensor (associated with the Carter constant) in
Boyer-Lindquist coordinates is:

  `K_{μν} = -a² cos²θ · g_{μν} + Σ² · (dθ)_μ (dθ)_ν + sin²θ · ω³_μ ω³_ν`

where `ω³ = a dt - (r²+a²) dφ`. Equivalently, using the Kinnersley principal
null covectors ℓ and n (with ℓ · n = -1):

  `K_{μν} = Σ (ℓ_μ n_ν + ℓ_ν n_μ) + r² g_{μν}`

Both forms have been verified numerically at generic points (M=1, a=0.5,
r=3, θ=π/4) to satisfy ∇_{(α} K_{μν)} = 0 to machine precision.

## Proof status

The symmetrized Killing tensor equation is stated as a theorem below.
Each of the 64 index cases (α,μ,ν ∈ {0,1,2,3}) reduces to a rational
function identity in (r, sinθ, cosθ, M, a). The "trivial" cases where
all partial derivatives vanish (α ∈ {0,3}) have been verified to close
with `norm_num [Fin.sum_univ_four]; ring`. The harder cases (α ∈ {1,2})
involve extremely large rational expressions that currently exceed the
computational budget of automated tactics.

A structural proof via the Killing-Yano tensor would be more elegant:
the KY 2-form f satisfies ∇_{(α} f_{β)γ} = 0, and K = f·g⁻¹·f
automatically satisfies the Killing tensor equation by an algebraic
identity. However, formalizing this requires substantial infrastructure
for tensor calculus that is not currently available in Mathlib.
-/

noncomputable section

open Real

-- ============================================================================
-- Coordinate labels and helper functions
-- ============================================================================

abbrev coordT : Fin 4 := 0
abbrev coordR : Fin 4 := 1
abbrev coordTh : Fin 4 := 2
abbrev coordPh : Fin 4 := 3

def rIdx : Fin 4 := coordR
def thetaIdx : Fin 4 := coordTh

def kerrSigmaCoord (a r th : ℝ) : ℝ :=
  r ^ 2 + a ^ 2 * (Real.cos th) ^ 2

def kerrDeltaCoord (M a r : ℝ) : ℝ :=
  r ^ 2 - 2 * M * r + a ^ 2

/-- Σ = r² + a² cos²θ -/
def kerrSigma (a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x coordR) ^ 2 + a ^ 2 * (Real.cos (x coordTh)) ^ 2

/-- Δ = r² − 2Mr + a² -/
def kerrDelta (M a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x coordR) ^ 2 - 2 * M * (x coordR) + a ^ 2

-- ============================================================================
-- Kerr metric in Boyer-Lindquist coordinates
-- ============================================================================

/-- The Kerr metric tensor g_{μν} in Boyer-Lindquist coordinates. -/
def kerrMetric (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  let r := x coordR
  let th := x coordTh
  let sig := kerrSigma a x
  let del := kerrDelta M a x
  if μ = ν then
    match μ with
    | ⟨0, _⟩ => -(1 - 2 * M * r / sig)
    | ⟨1, _⟩ => sig / del
    | ⟨2, _⟩ => sig
    | ⟨3, _⟩ => (r ^ 2 + a ^ 2 + 2 * M * r * a ^ 2 *
                  (Real.sin th) ^ 2 / sig) * (Real.sin th) ^ 2
  else if (μ = coordT ∧ ν = coordPh) ∨ (μ = coordPh ∧ ν = coordT) then
    -(2 * M * r * a * (Real.sin th) ^ 2 / sig)
  else
    0

-- ============================================================================
-- The correct Killing tensor
-- ============================================================================

/-- The 1-form ω³ = a dt - (r²+a²) dφ. -/
def omega3 (a : ℝ) (x : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  match μ with
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => -((x coordR) ^ 2 + a ^ 2)

/-- The correct Killing tensor for Kerr spacetime:
    K_{μν} = -a² cos²θ · g_{μν} + Σ² · δ^θ_μ δ^θ_ν + sin²θ · ω³_μ ω³_ν -/
def killingTensor (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  let th := x coordTh
  let sig := kerrSigma a x
  let c2 := (Real.cos th) ^ 2
  let s2 := (Real.sin th) ^ 2
  (- a ^ 2 * c2 * kerrMetric M a x μ ν)
  + ((if μ = coordTh then (1 : ℝ) else 0) * (if ν = coordTh then (1 : ℝ) else 0) * sig ^ 2)
  + (s2 * omega3 a x μ * omega3 a x ν)

-- ============================================================================
-- Explicit partial derivatives of metric and Killing tensor
-- ============================================================================

def partialSigmaR (x : Fin 4 → ℝ) : ℝ := 2 * x coordR

def partialSigmaTheta (a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -2 * a ^ 2 * Real.cos (x coordTh) * Real.sin (x coordTh)

def partialDeltaR (M : ℝ) (x : Fin 4 → ℝ) : ℝ := 2 * x coordR - 2 * M

/-- Inverse Kerr metric g^{μν}. -/
def kerrInverseMetric (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  let r := x coordR
  let th := x coordTh
  let sig := kerrSigma a x
  let del := kerrDelta M a x
  let s2 := (Real.sin th) ^ 2
  if μ = ν then
    match μ with
    | ⟨0, _⟩ => -(((r ^ 2 + a ^ 2) ^ 2 - a ^ 2 * del * s2) / (del * sig))
    | ⟨1, _⟩ => del / sig
    | ⟨2, _⟩ => 1 / sig
    | ⟨3, _⟩ => (del - a ^ 2 * s2) / (del * sig * s2)
  else if (μ = coordT ∧ ν = coordPh) ∨ (μ = coordPh ∧ ν = coordT) then
    -(2 * M * r * a / (del * sig))
  else
    0

/-- Partial derivatives ∂_α g_{μν}. -/
def partialKerrMetric (M a : ℝ) (x : Fin 4 → ℝ) (α μ ν : Fin 4) : ℝ :=
  let r := x coordR
  let th := x coordTh
  let sig := kerrSigma a x
  let del := kerrDelta M a x
  let dsig_dr := partialSigmaR x
  let dsig_dth := partialSigmaTheta a x
  let ddel_dr := partialDeltaR M x
  let s := Real.sin th
  let c := Real.cos th
  let s2 := s ^ 2
  if α = coordT then 0
  else if α = coordPh then 0
  else if α = coordR then
    if μ = ν then
      match μ with
      | ⟨0, _⟩ => 2 * M * (sig - r * dsig_dr) / sig ^ 2
      | ⟨1, _⟩ => (dsig_dr * del - sig * ddel_dr) / del ^ 2
      | ⟨2, _⟩ => dsig_dr
      | ⟨3, _⟩ =>
          let dbase :=
            2 * r + ((2 * M * a ^ 2 * s2) * sig - (2 * M * r * a ^ 2 * s2) * dsig_dr) / sig ^ 2
          dbase * s2
    else if (μ = coordT ∧ ν = coordPh) ∨ (μ = coordPh ∧ ν = coordT) then
      -(((2 * M * a * s2) * sig - (2 * M * r * a * s2) * dsig_dr) / sig ^ 2)
    else 0
  else if α = coordTh then
    if μ = ν then
      match μ with
      | ⟨0, _⟩ => -(2 * M * r * dsig_dth / sig ^ 2)
      | ⟨1, _⟩ => dsig_dth / del
      | ⟨2, _⟩ => dsig_dth
      | ⟨3, _⟩ =>
          let base := r ^ 2 + a ^ 2 + 2 * M * r * a ^ 2 * s2 / sig
          let dbase := ((4 * M * r * a ^ 2 * s * c) * sig -
            (2 * M * r * a ^ 2 * s2) * dsig_dth) / sig ^ 2
          dbase * s2 + base * (2 * s * c)
    else if (μ = coordT ∧ ν = coordPh) ∨ (μ = coordPh ∧ ν = coordT) then
      -(((4 * M * r * a * s * c) * sig -
        (2 * M * r * a * s2) * dsig_dth) / sig ^ 2)
    else 0
  else 0

/-- Partial derivatives ∂_α K_{μν}, computed from the decomposition
    K = -a²cos²θ g + Σ²(dθ)² + sin²θ(ω³)². -/
def partialKillingTensor (M a : ℝ) (x : Fin 4 → ℝ) (α μ ν : Fin 4) : ℝ :=
  let r := x coordR
  let th := x coordTh
  let sig := kerrSigma a x
  let c := Real.cos th
  let s := Real.sin th
  let c2 := c ^ 2
  let s2 := s ^ 2
  let dthMu : ℝ := if μ = coordTh then 1 else 0
  let dthNu : ℝ := if ν = coordTh then 1 else 0
  let dphMu : ℝ := if μ = coordPh then 1 else 0
  let dphNu : ℝ := if ν = coordPh then 1 else 0
  if α = coordT then 0
  else if α = coordPh then 0
  else if α = coordR then
    (- a ^ 2 * c2 * partialKerrMetric M a x coordR μ ν)
    + (4 * r * sig * dthMu * dthNu)
    + (- 2 * r * s2 * (dphMu * omega3 a x ν + omega3 a x μ * dphNu))
  else if α = coordTh then
    (2 * a ^ 2 * c * s * kerrMetric M a x μ ν)
    + (- a ^ 2 * c2 * partialKerrMetric M a x coordTh μ ν)
    + (- 4 * a ^ 2 * c * s * sig * dthMu * dthNu)
    + (2 * s * c * omega3 a x μ * omega3 a x ν)
  else 0

-- ============================================================================
-- Christoffel symbols and covariant derivative
-- ============================================================================

/-- Christoffel symbols Γ^σ_{μν}. -/
noncomputable def kerrGamma (M a : ℝ) (x : Fin 4 → ℝ) (σ μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * Finset.univ.sum (fun ρ : Fin 4 =>
    kerrInverseMetric M a x σ ρ * (
      partialKerrMetric M a x μ ν ρ +
      partialKerrMetric M a x ν μ ρ -
      partialKerrMetric M a x ρ μ ν))

/-- Covariant derivative ∇_α K_{μν}. -/
noncomputable def covDerivKillingConcrete
    (M a : ℝ) (x : Fin 4 → ℝ) (α μ ν : Fin 4) : ℝ :=
  partialKillingTensor M a x α μ ν
  - Finset.univ.sum (fun l : Fin 4 =>
      kerrGamma M a x l α μ * killingTensor M a x l ν)
  - Finset.univ.sum (fun l : Fin 4 =>
      kerrGamma M a x l α ν * killingTensor M a x μ l)

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- The Kerr Killing tensor satisfies the symmetrized Killing tensor equation:
    ∇_α K_{μν} + ∇_μ K_{να} + ∇_ν K_{αμ} = 0 for all index triples. -/
theorem symmetrized_killing_equation (M a : ℝ)
    (x : Fin 4 → ℝ)
    (hSig : kerrSigmaCoord a (x rIdx) (x thetaIdx) ≠ 0)
    (hDel : kerrDeltaCoord M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ α μ ν : Fin 4,
      covDerivKillingConcrete M a x α μ ν +
      covDerivKillingConcrete M a x μ ν α +
      covDerivKillingConcrete M a x ν α μ = 0 := by
  sorry

end
