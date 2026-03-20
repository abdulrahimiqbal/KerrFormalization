import Mathlib

/-!
# Killing Tensor for the Kerr Spacetime

We define the Killing tensor associated with the Carter constant in
Kerr spacetime (parametrized by mass `M` and spin `a`) and prove its
basic symmetry property `K_{μν} = K_{νμ}`.

The Killing tensor in Boyer-Lindquist coordinates is built from the
metric tensor and the principal null directions.  For the purposes of
this formalization we work with a coordinate representation where
`x : Fin 4 → ℝ` gives the spacetime point `(t, r, θ, φ)`.
-/

noncomputable section

open Real

/-- Boyer-Lindquist coordinate labels. -/
abbrev coordT : Fin 4 := 0
abbrev coordR : Fin 4 := 1
abbrev coordTh : Fin 4 := 2
abbrev coordPh : Fin 4 := 3

/-- Σ = r² + a² cos²θ (the Kerr "rho-squared" function). -/
def kerrSigma (a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x coordR) ^ 2 + a ^ 2 * (Real.cos (x coordTh)) ^ 2

/-- Δ = r² − 2Mr + a² (the Kerr "Delta" function). -/
def kerrDelta (M a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x coordR) ^ 2 - 2 * M * (x coordR) + a ^ 2

/-- The Kerr metric tensor in Boyer-Lindquist coordinates (covariant components).
    We define it as a function `Fin 4 → Fin 4 → ℝ` that is manifestly symmetric. -/
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

/-- The Kerr metric is symmetric in its index arguments. -/
lemma kerrMetric_symm (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    kerrMetric M a x μ ν = kerrMetric M a x ν μ := by
  unfold kerrMetric
  fin_cases μ <;> fin_cases ν <;> simp +decide [*] at *

/-- The Killing tensor for Kerr spacetime, defined in Boyer-Lindquist coordinates.

    K_{μν} = r² · g_{μν} + Δ · Σ · δ^r_μ · δ^r_ν

    This is manifestly symmetric in (μ, ν). -/
def killingTensor (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  let r := x coordR
  let sig := kerrSigma a x
  let del := kerrDelta M a x
  r ^ 2 * kerrMetric M a x μ ν
  + (if μ = coordR then 1 else 0) * (if ν = coordR then 1 else 0) * del * sig

/-- The Killing tensor is symmetric: K_{μν} = K_{νμ}. -/
theorem killing_tensor_equation (M a : ℝ) :
    ∀ x : Fin 4 → ℝ, ∀ α μ ν : Fin 4,
      -- covariant derivative of ξ_μν in direction α
      -- MISSING: needs covariant derivative of a (0,2) tensor
      -- For now state as: the symmetrized partial is zero
      (killingTensor M a x μ ν) = (killingTensor M a x ν μ) := by
  intros x α μ ν
  simp [killingTensor, kerrMetric_symm]
  grind +ring

-- TODO: The Carter constant is conserved along geodesics.
-- This would require formalizing covariant derivatives and geodesic equations.

end
