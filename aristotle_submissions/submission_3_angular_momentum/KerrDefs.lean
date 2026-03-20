import Mathlib

/-!
# Kerr Geodesic Definitions

Definitions for the Kerr metric, geodesic data, and angular momentum.
-/

noncomputable section

open Real

/-- Boyer-Lindquist coordinate labels. -/
abbrev coordT : Fin 4 := 0
abbrev coordR : Fin 4 := 1
abbrev coordTh : Fin 4 := 2
abbrev coordPh : Fin 4 := 3

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

/-- A parametrized curve with position, velocity, acceleration as data. -/
structure CurveWithVelocity where
  pos : ℝ → Fin 4 → ℝ
  vel : ℝ → Fin 4 → ℝ
  acc : ℝ → Fin 4 → ℝ

/-- Time index. -/
def tIdx : Fin 4 := ⟨0, by decide⟩

/-- Azimuthal index. -/
def phiIdx : Fin 4 := ⟨3, by decide⟩

/-- Axial angular momentum along a curve. -/
noncomputable def angMomentum (M a : ℝ) (γ : CurveWithVelocity) (p : ℝ) : ℝ :=
  Finset.univ.sum (fun μ : Fin 4 =>
    kerrMetric M a (γ.pos p) phiIdx μ * γ.vel p μ)

/-- Geodesic equation with respect to a given connection Gamma. -/
def IsGeodesic (Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (γ : CurveWithVelocity) : Prop :=
  ∀ p : ℝ, ∀ σ : Fin 4,
    γ.acc p σ +
      Finset.univ.sum (fun μ : Fin 4 =>
        Finset.univ.sum (fun ν : Fin 4 =>
          Gamma (γ.pos p) σ μ ν *
          γ.vel p μ * γ.vel p ν)) = 0

/-- Bundle of physical assumptions needed for angular momentum conservation. -/
structure KerrGeodesicData (M a : ℝ) where
  /-- Christoffel symbols -/
  Gamma : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ
  /-- The worldline -/
  γ : CurveWithVelocity
  /-- Geodesic equation holds -/
  is_geodesic : IsGeodesic Gamma γ
  /-- Velocity is derivative of position -/
  vel_deriv : ∀ p μ, HasDerivAt (fun s => γ.pos s μ) (γ.vel p μ) p
  /-- Acceleration is derivative of velocity -/
  acc_deriv : ∀ p μ, HasDerivAt (fun s => γ.vel s μ) (γ.acc p μ) p
  /-- Metric compatibility + chain rule along worldline -/
  metric_deriv : ∀ p μ ν,
    HasDerivAt (fun s => kerrMetric M a (γ.pos s) μ ν)
      (Finset.univ.sum (fun α : Fin 4 =>
        (Finset.univ.sum (fun σ : Fin 4 =>
          kerrMetric M a (γ.pos p) μ σ * Gamma (γ.pos p) σ α ν +
          kerrMetric M a (γ.pos p) ν σ * Gamma (γ.pos p) σ α μ)) *
        γ.vel p α))
      p
  /-- Stationarity in Christoffel form -/
  stationary_christoffel : ∀ x μ ν,
    Finset.univ.sum (fun σ : Fin 4 =>
      kerrMetric M a x μ σ * Gamma x σ tIdx ν +
      kerrMetric M a x ν σ * Gamma x σ tIdx μ) = 0
  /-- Axisymmetry in Christoffel form: the metric does not depend on phi.
      This is the phi-analogue of `stationary_christoffel` and is needed for
      angular momentum conservation, just as stationarity is needed for
      energy conservation. -/
  axisymmetric_christoffel : ∀ x μ ν,
    Finset.univ.sum (fun σ : Fin 4 =>
      kerrMetric M a x μ σ * Gamma x σ phiIdx ν +
      kerrMetric M a x ν σ * Gamma x σ phiIdx μ) = 0
  /-- Christoffel symmetry in lower indices -/
  christoffel_symm : ∀ x σ μ ν,
    Gamma x σ μ ν = Gamma x σ ν μ

/-- Projection alias so the theorem statement can refer to `curve`. -/
def KerrGeodesicData.curve {M a : ℝ} (D : KerrGeodesicData M a) : CurveWithVelocity := D.γ

/-
PROBLEM
Kerr metric does not depend on the phi coordinate.

PROVIDED SOLUTION
The kerrMetric depends on x only through x coordR (r) and x coordTh (theta). It never depends on x phiIdx. So replacing x phiIdx with phi doesn't change the metric. Unfold kerrMetric, kerrSigma, kerrDelta. Note that phiIdx = ⟨3, _⟩, coordR = 1, coordTh = 2, and these are all different from phiIdx, so (fun k => if k = phiIdx then phi else x k) coordR = x coordR and similarly for coordTh. Use simp with the if-then-else simplification to show both sides are equal. Key: phiIdx ≠ coordR and phiIdx ≠ coordTh (by decide).
-/
lemma kerrMetric_axisymmetric (M a : ℝ) (x : Fin 4 → ℝ)
    (phi : ℝ) (i j : Fin 4) :
    kerrMetric M a (fun k => if k = phiIdx then phi else x k) i j =
    kerrMetric M a x i j := by
  all_goals unfold phiIdx; aesop;

end