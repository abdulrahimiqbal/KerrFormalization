import Mathlib

/-!
# Killing Tensor Equation for Kerr in Boyer-Lindquist Coordinates

This file isolates the remaining gap behind Carter constant conservation:
the covariant-derivative equation for the explicit Boyer-Lindquist
Killing tensor.
-/

noncomputable section

open Real

/-- Boyer-Lindquist coordinate labels. -/
abbrev coordT : Fin 4 := 0
abbrev coordR : Fin 4 := 1
abbrev coordTh : Fin 4 := 2
abbrev coordPh : Fin 4 := 3

/-- Convenience aliases matching the research note terminology. -/
def rIdx : Fin 4 := coordR
def thetaIdx : Fin 4 := coordTh

/-- Sigma = r^2 + a^2 cos^2 theta. -/
def kerrSigma (a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x coordR) ^ 2 + a ^ 2 * (Real.cos (x coordTh)) ^ 2

/-- Delta = r^2 - 2 M r + a^2. -/
def kerrDelta (M a : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x coordR) ^ 2 - 2 * M * (x coordR) + a ^ 2

/-- The Kerr metric tensor in Boyer-Lindquist coordinates (covariant components). -/
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

    K_{μν} = r² · g_{μν} + Δ · Σ · δ^r_μ · δ^r_ν -/
def killingTensor (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  let r := x coordR
  let sig := kerrSigma a x
  let del := kerrDelta M a x
  r ^ 2 * kerrMetric M a x μ ν
  + (if μ = coordR then 1 else 0) * (if ν = coordR then 1 else 0) * del * sig

/-- The Killing tensor is symmetric: K_{μν} = K_{νμ}. -/
theorem killing_tensor_symm (M a : ℝ) :
    ∀ x : Fin 4 → ℝ, ∀ μ ν : Fin 4,
      (killingTensor M a x μ ν) = (killingTensor M a x ν μ) := by
  intros x μ ν
  simp [killingTensor, kerrMetric_symm]
  grind +ring

/-- A parametrized curve with position, velocity, acceleration as data. -/
structure CurveWithVelocity where
  pos : ℝ → Fin 4 → ℝ
  vel : ℝ → Fin 4 → ℝ
  acc : ℝ → Fin 4 → ℝ

/-- Time index. -/
def tIdx : Fin 4 := ⟨0, by decide⟩

/-- Azimuthal index. -/
def phiIdx : Fin 4 := ⟨3, by decide⟩

/-- Geodesic equation with respect to a given connection Gamma. -/
def IsGeodesic (Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (γ : CurveWithVelocity) : Prop :=
  ∀ p : ℝ, ∀ σ : Fin 4,
    γ.acc p σ +
      Finset.univ.sum (fun μ : Fin 4 =>
        Finset.univ.sum (fun ν : Fin 4 =>
          Gamma (γ.pos p) σ μ ν *
          γ.vel p μ * γ.vel p ν)) = 0

/-- Bundle of physical assumptions currently available from the Aristotle runs. -/
structure KerrGeodesicData (M a : ℝ) where
  Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ
  γ : CurveWithVelocity
  is_geodesic : IsGeodesic Gamma γ
  vel_deriv : ∀ p μ, HasDerivAt (fun s => γ.pos s μ) (γ.vel p μ) p
  acc_deriv : ∀ p μ, HasDerivAt (fun s => γ.vel s μ) (γ.acc p μ) p
  metric_deriv : ∀ p μ ν,
    HasDerivAt (fun s => kerrMetric M a (γ.pos s) μ ν)
      (Finset.univ.sum (fun α : Fin 4 =>
        (Finset.univ.sum (fun σ : Fin 4 =>
          kerrMetric M a (γ.pos p) μ σ * Gamma (γ.pos p) σ α ν +
          kerrMetric M a (γ.pos p) ν σ * Gamma (γ.pos p) σ α μ)) *
        γ.vel p α))
      p
  stationary_christoffel : ∀ x μ ν,
    Finset.univ.sum (fun σ : Fin 4 =>
      kerrMetric M a x μ σ * Gamma x σ tIdx ν +
      kerrMetric M a x ν σ * Gamma x σ tIdx μ) = 0
  axisymmetric_christoffel : ∀ x μ ν,
    Finset.univ.sum (fun σ : Fin 4 =>
      kerrMetric M a x μ σ * Gamma x σ phiIdx ν +
      kerrMetric M a x ν σ * Gamma x σ phiIdx μ) = 0
  christoffel_symm : ∀ x σ μ ν,
    Gamma x σ μ ν = Gamma x σ ν μ
  killing_tensor_conservation_law : ∀ p,
    HasDerivAt (fun s => Finset.univ.sum (fun μ : Fin 4 =>
      Finset.univ.sum (fun ν : Fin 4 =>
        killingTensor M a (γ.pos s) μ ν * γ.vel s μ * γ.vel s ν)))
      0 p

/-- Projection alias so theorem statements can refer to `curve`. -/
def KerrGeodesicData.curve {M a : ℝ} (D : KerrGeodesicData M a) : CurveWithVelocity := D.γ

/-- Placeholder for the coordinate partial derivative of the explicit Killing tensor. -/
axiom killingTensorPartial
    (M a : ℝ) (α : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ

/-- Placeholder describing when Gamma is the Kerr Christoffel connection in these coordinates. -/
axiom IsKerrChristoffel
    (M a : ℝ) (Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop

/-- Covariant derivative of the Killing tensor in Boyer-Lindquist coordinates. -/
noncomputable def covDerivKilling
    (M a : ℝ) (Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (α μ ν : Fin 4) : ℝ :=
  killingTensorPartial M a α x μ ν
  - Finset.univ.sum (fun l : Fin 4 =>
      Gamma x l α μ * killingTensor M a x l ν)
  - Finset.univ.sum (fun l : Fin 4 =>
      Gamma x l α ν * killingTensor M a x μ l)

/-!
## Note on `killing_tensor_cov_deriv_zero`

The theorem below (`killing_tensor_cov_deriv_zero`) cannot be proved as currently stated,
for two independent reasons:

### 1. Opaque axioms prevent any computation

Both `killingTensorPartial` and `IsKerrChristoffel` are declared as `axiom`, making them
completely opaque to the elaborator. No information can be extracted from
`hGamma : IsKerrChristoffel M a Gamma` (it is an opaque `Prop` with no constructors),
and `killingTensorPartial` returns an opaque `ℝ` with no definitional content.
The definition of `covDerivKilling` therefore cannot be simplified or evaluated.

### 2. The unsymmetrized statement is mathematically incorrect

Even if the axioms were replaced with concrete definitions, the claim
  `∇_α K_{μν} = 0` for ALL `α μ ν`
is **false** for any non-trivial Killing tensor in a curved spacetime. A Killing tensor
satisfies the **symmetrized** equation `∇_{(α} K_{μν)} = 0`, i.e.:
  `∇_α K_{μν} + ∇_μ K_{να} + ∇_ν K_{αμ} = 0`
This is strictly weaker than requiring each `∇_α K_{μν} = 0` individually.

For the Carter constant conservation, only the symmetrized version is needed, since
  `d/ds [K_{μν} u^μ u^ν] = (∇_α K_{μν}) u^α u^μ u^ν`
and `u^α u^μ u^ν` is completely symmetric, so it only sees the symmetric part of `∇_α K_{μν}`.

### What would need to change

To make the Killing tensor equation provable and useful:
1. Replace `killingTensorPartial` with a concrete definition computing partial derivatives of
   `killingTensor` components.
2. Replace `IsKerrChristoffel` with a concrete definition of the Kerr Christoffel symbols.
3. State the **symmetrized** Killing tensor equation: `∇_{(α} K_{μν)} = 0`.
4. Add a `killing_tensor_deriv` field to `KerrGeodesicData` connecting `killingTensorPartial`
   to actual `HasDerivAt` statements for the Killing tensor along curves.
5. Prove `killing_tensor_conservation_from_equation` from the symmetrized KTE + geodesic
   equation, rather than from the `killing_tensor_conservation_law` field.
-/

/-- The explicit Kerr Killing tensor satisfies the Killing tensor equation.

**Status**: Unprovable as stated — see the note above. The axioms `IsKerrChristoffel` and
`killingTensorPartial` are opaque, and the unsymmetrized covariant derivative
`∇_α K_{μν}` does not vanish identically for a Killing tensor. -/
theorem killing_tensor_cov_deriv_zero (M a : ℝ)
    (Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hGamma : IsKerrChristoffel M a Gamma)
    (x : Fin 4 → ℝ) (hx : kerrSigma a x ≠ 0)
    (hDelta : kerrDelta M a x ≠ 0) :
    ∀ α μ ν : Fin 4,
      covDerivKilling M a Gamma x α μ ν = 0 := by
  sorry

/-- The Killing tensor equation implies vanishing derivative of the Carter integrand.

**Proof note**: In the current formalization, the conclusion is exactly
`γ.killing_tensor_conservation_law p` (since `γ.curve = γ.γ` by definition).
The hypothesis `hKilling` is not used. To break the circularity described in the
comments below, one would need to:
- Add a `killing_tensor_deriv` field connecting `killingTensorPartial` to `HasDerivAt`,
- Prove the conservation law from scratch using the chain rule, product rule,
  geodesic equation, and the (symmetrized) Killing tensor equation. -/
theorem killing_tensor_conservation_from_equation (M a : ℝ)
    (γ : KerrGeodesicData M a)
    (hKilling : ∀ x α μ ν,
      covDerivKilling M a (fun x σ μ ν => γ.Gamma x σ μ ν) x α μ ν = 0) :
    ∀ p, HasDerivAt (fun s =>
      Finset.univ.sum (fun μ : Fin 4 =>
        Finset.univ.sum (fun ν : Fin 4 =>
          killingTensor M a (γ.curve.pos s) μ ν * γ.curve.vel s μ * γ.curve.vel s ν)))
      0 p := by
  intro p
  exact γ.killing_tensor_conservation_law p

/-
CHAIN TO CLOSE THE CIRCULAR AXIOM:

killing_tensor_cov_deriv_zero   (this file, sorry — see note above)
      ↓
killing_tensor_conservation_from_equation  (this file, proved — but see note)
      ↓
killing_tensor_conservation_law  (currently circular in KerrCarter.lean)
      ↓
carter_constant_conserved       (proved in KerrCarter.lean)

STATUS:
• killing_tensor_conservation_from_equation is proved, but its proof uses
  γ.killing_tensor_conservation_law (the very axiom it was meant to replace),
  so the circularity is NOT broken by this proof alone.

• killing_tensor_cov_deriv_zero remains sorry due to opaque axioms and an
  incorrect (unsymmetrized) mathematical statement.

TO FULLY CLOSE THE GAP:
1. Replace axiom killingTensorPartial with a concrete partial-derivative definition.
2. Replace axiom IsKerrChristoffel with concrete Christoffel symbol definitions.
3. Correct the statement to the symmetrized Killing tensor equation ∇_{(α}K_{μν)} = 0.
4. Add a killing_tensor_deriv assumption connecting partial derivatives to HasDerivAt.
5. Re-prove killing_tensor_conservation_from_equation from first principles
   (chain rule + product rule + geodesic equation + symmetrized KTE).
-/

end
