import KerrFormalization.Kerr.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

namespace RequestProject

/-- Kerr metric function `Σ = r^2 + a^2 cos(θ)^2`. -/
noncomputable def sigma (a r θ : ℝ) : ℝ :=
  r^2 + a^2 * (Real.cos θ)^2

/-- Kerr metric function `Δ = r^2 - 2 M r + a^2`. -/
noncomputable def delta (M a r : ℝ) : ℝ :=
  r^2 - 2 * M * r + a^2

/-- Radially deformed lapse function `Δ_ε = Δ + ε`. -/
noncomputable def deltaEps (M a r ε : ℝ) : ℝ :=
  delta M a r + ε

/-- Boyer-Lindquist time coordinate index. -/
def tIdx : Fin 4 := 0

/-- Boyer-Lindquist radial coordinate index. -/
def rIdx : Fin 4 := 1

/-- Boyer-Lindquist polar coordinate index. -/
def thetaIdx : Fin 4 := 2

/-- Boyer-Lindquist azimuthal coordinate index. -/
def phiIdx : Fin 4 := 3

/-- The unique nonzero off-diagonal Boyer-Lindquist pair `(t, φ)` (in either order). -/
def isTPhiPair (μ ν : Fin 4) : Prop :=
  (μ = tIdx ∧ ν = phiIdx) ∨ (μ = phiIdx ∧ ν = tIdx)

/-- Exact Kerr metric components in Boyer-Lindquist coordinates. -/
noncomputable def kerrMetricExplicit (M a r θ : ℝ) (μ ν : Fin 4) : ℝ :=
  if isTPhiPair μ ν then
    -(2 * M * a * r * (Real.sin θ)^2 / sigma a r θ)
  else if μ = ν then
    if μ = tIdx then
      -(1 - (2 * M * r) / sigma a r θ)
    else if μ = rIdx then
      sigma a r θ / delta M a r
    else if μ = thetaIdx then
      sigma a r θ
    else if μ = phiIdx then
      (((r^2 + a^2)^2 - a^2 * delta M a r * (Real.sin θ)^2) * (Real.sin θ)^2) / sigma a r θ
    else 0
  else 0

/-- The one-form `dθ` written in coordinates. -/
def dThetaCovector (μ : Fin 4) : ℝ :=
  if μ = thetaIdx then 1 else 0

/-- The principal one-form `ω³ = a dt - (r^2 + a^2) dφ`. -/
noncomputable def omega3 (a r : ℝ) (μ : Fin 4) : ℝ :=
  if μ = tIdx then a else if μ = phiIdx then -(r^2 + a^2) else 0

/--
Form C of the Carter Killing tensor:

`K = -a^2 cos(θ)^2 g + Σ^2 dθ ⊗ dθ + sin(θ)^2 ω³ ⊗ ω³`.
-/
noncomputable def killingTensorFormCExplicit (M a r θ : ℝ) (μ ν : Fin 4) : ℝ :=
  -(a^2 * (Real.cos θ)^2) * kerrMetricExplicit M a r θ μ ν
    + (sigma a r θ)^2 * dThetaCovector μ * dThetaCovector ν
    + (Real.sin θ)^2 * omega3 a r μ * omega3 a r ν

/--
Explicit Christoffel symbols `Γ^σ_{μν}` for the exact Kerr metric, restricted to
the components needed by the `(θ, θ, θ)` contraction.
-/
noncomputable def kerrChristoffelExplicit (M a r θ : ℝ) (σ μ ν : Fin 4) : ℝ :=
  if μ = thetaIdx ∧ ν = thetaIdx then
    if σ = rIdx then
      -(r * delta M a r / sigma a r θ)
    else if σ = thetaIdx then
      -(a^2 * Real.cos θ * Real.sin θ / sigma a r θ)
    else 0
  else 0

/--
Explicit Christoffel symbols `Γ^σ_{μν}` for the `Δ ↦ Δ + ε` radial deformation,
again only on the slots needed by `(θ, θ, θ)`.
-/
noncomputable def kerrChristoffelDeformed (M a r θ ε : ℝ) (σ μ ν : Fin 4) : ℝ :=
  if μ = thetaIdx ∧ ν = thetaIdx then
    if σ = rIdx then
      -(r * deltaEps M a r ε / sigma a r θ)
    else if σ = thetaIdx then
      -(a^2 * Real.cos θ * Real.sin θ / sigma a r θ)
    else 0
  else 0

/-- The explicit `θ`-derivative of `K_{θθ} = r^2 Σ`. -/
noncomputable def dThetaKThetaTheta (a r θ : ℝ) : ℝ :=
  -2 * a^2 * r^2 * Real.cos θ * Real.sin θ

/--
The `(θ, θ, θ)` component of the symmetrized Killing equation, evaluated using
the deformed Christoffel symbols.
-/
noncomputable def killingResidual222 (M a r θ ε : ℝ) : ℝ :=
  dThetaKThetaTheta a r θ
    - 2 * Finset.univ.sum (fun σ : Fin 4 =>
        kerrChristoffelDeformed M a r θ ε σ thetaIdx thetaIdx
          * killingTensorFormCExplicit M a r θ σ thetaIdx)

@[simp] theorem sigma_def (a r θ : ℝ) :
    sigma a r θ = r^2 + a^2 * (Real.cos θ)^2 := rfl

@[simp] theorem delta_def (M a r : ℝ) :
    delta M a r = r^2 - 2 * M * r + a^2 := rfl

@[simp] theorem deltaEps_def (M a r ε : ℝ) :
    deltaEps M a r ε = r^2 - 2 * M * r + a^2 + ε := by
  rfl

@[simp] theorem dThetaCovector_theta :
    dThetaCovector thetaIdx = 1 := by
  simp [dThetaCovector, thetaIdx]

@[simp] theorem omega3_theta (a r : ℝ) :
    omega3 a r thetaIdx = 0 := by
  simp [omega3, thetaIdx, tIdx, phiIdx]

@[simp] theorem kerrMetricExplicit_theta_theta (M a r θ : ℝ) :
    kerrMetricExplicit M a r θ thetaIdx thetaIdx = sigma a r θ := by
  simp [kerrMetricExplicit, isTPhiPair, thetaIdx, tIdx, rIdx, phiIdx]

@[simp] theorem killingTensorFormCExplicit_theta_theta (M a r θ : ℝ) :
    killingTensorFormCExplicit M a r θ thetaIdx thetaIdx = r^2 * sigma a r θ := by
  rw [killingTensorFormCExplicit, kerrMetricExplicit_theta_theta]
  simp [dThetaCovector, omega3, sigma, thetaIdx, tIdx, phiIdx]
  ring_nf

@[simp] theorem killingTensorFormCExplicit_t_theta (M a r θ : ℝ) :
    killingTensorFormCExplicit M a r θ tIdx thetaIdx = 0 := by
  simp [killingTensorFormCExplicit, kerrMetricExplicit, isTPhiPair, dThetaCovector, omega3,
    tIdx, thetaIdx, phiIdx]

@[simp] theorem killingTensorFormCExplicit_r_theta (M a r θ : ℝ) :
    killingTensorFormCExplicit M a r θ rIdx thetaIdx = 0 := by
  simp [killingTensorFormCExplicit, kerrMetricExplicit, isTPhiPair, dThetaCovector, omega3,
    tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem killingTensorFormCExplicit_phi_theta (M a r θ : ℝ) :
    killingTensorFormCExplicit M a r θ phiIdx thetaIdx = 0 := by
  simp [killingTensorFormCExplicit, kerrMetricExplicit, isTPhiPair, dThetaCovector, omega3,
    tIdx, thetaIdx, phiIdx]

@[simp] theorem kerrChristoffelDeformed_t_theta_theta (M a r θ ε : ℝ) :
    kerrChristoffelDeformed M a r θ ε tIdx thetaIdx thetaIdx = 0 := by
  simp [kerrChristoffelDeformed, tIdx, thetaIdx, rIdx]

@[simp] theorem kerrChristoffelDeformed_r_theta_theta (M a r θ ε : ℝ) :
    kerrChristoffelDeformed M a r θ ε rIdx thetaIdx thetaIdx =
      -(r * deltaEps M a r ε / sigma a r θ) := by
  simp [kerrChristoffelDeformed, rIdx, thetaIdx]

@[simp] theorem kerrChristoffelDeformed_theta_theta_theta (M a r θ ε : ℝ) :
    kerrChristoffelDeformed M a r θ ε thetaIdx thetaIdx thetaIdx =
      -(a^2 * Real.cos θ * Real.sin θ / sigma a r θ) := by
  simp [kerrChristoffelDeformed, thetaIdx, rIdx]

@[simp] theorem kerrChristoffelDeformed_phi_theta_theta (M a r θ ε : ℝ) :
    kerrChristoffelDeformed M a r θ ε phiIdx thetaIdx thetaIdx = 0 := by
  simp [kerrChristoffelDeformed, phiIdx, thetaIdx, rIdx]

@[simp] theorem dThetaKThetaTheta_eq (a r θ : ℝ) :
    dThetaKThetaTheta a r θ =
      -2 * a^2 * r^2 * Real.cos θ * Real.sin θ := rfl

theorem theta_theta_theta_contraction (M a r θ ε : ℝ) :
    Finset.univ.sum (fun σ : Fin 4 =>
      kerrChristoffelDeformed M a r θ ε σ thetaIdx thetaIdx
        * killingTensorFormCExplicit M a r θ σ thetaIdx) =
      -(a^2 * Real.cos θ * Real.sin θ / sigma a r θ) * (r^2 * sigma a r θ) := by
  rw [Fin.sum_univ_four]
  simp [kerrChristoffelDeformed, killingTensorFormCExplicit, kerrMetricExplicit, isTPhiPair,
    dThetaCovector, omega3, sigma, deltaEps, tIdx, rIdx, thetaIdx, phiIdx]
  ring_nf
  tauto

theorem theta_theta_theta_contraction_simplified (M a r θ ε : ℝ)
    (hSigma : sigma a r θ ≠ 0) :
    Finset.univ.sum (fun σ : Fin 4 =>
      kerrChristoffelDeformed M a r θ ε σ thetaIdx thetaIdx
        * killingTensorFormCExplicit M a r θ σ thetaIdx) =
      -(a^2 * r^2 * Real.cos θ * Real.sin θ) := by
  rw [theta_theta_theta_contraction]
  calc
    -(a^2 * Real.cos θ * Real.sin θ / sigma a r θ) * (r^2 * sigma a r θ)
        = -(a^2 * Real.cos θ * Real.sin θ * r^2) * ((sigma a r θ)⁻¹ * sigma a r θ) := by
            simp [div_eq_mul_inv]
            ring
    _ = -(a^2 * Real.cos θ * Real.sin θ * r^2) := by
          rw [inv_mul_cancel₀ hSigma]
          ring
    _ = -(a^2 * r^2 * Real.cos θ * Real.sin θ) := by
          ring

theorem killing_equation_222_kerr (M a r θ : ℝ)
    (hSigma : sigma a r θ ≠ 0) (_hDelta : delta M a r ≠ 0) (_hSin : Real.sin θ ≠ 0) :
    killingResidual222 M a r θ 0 = 0 := by
  rw [killingResidual222, theta_theta_theta_contraction_simplified _ _ _ _ 0 hSigma,
    dThetaKThetaTheta]
  ring

theorem killing_equation_222_deformed_value (M a r θ ε : ℝ)
    (hSigma : sigma a r θ ≠ 0) (_hDelta : delta M a r ≠ 0)
    (_hDeltaEps : deltaEps M a r ε ≠ 0) (_hSin : Real.sin θ ≠ 0) :
    killingResidual222 M a r θ ε = 0 := by
  rw [killingResidual222, theta_theta_theta_contraction_simplified _ _ _ _ _ hSigma,
    dThetaKThetaTheta]
  ring

/--
The `(2,2,2)` component is not a deformation diagnostic: it vanishes for every
`ε`, so no theorem of the form `killingResidual222 ... ε = 0 → ε = 0` can hold
in general.
-/
theorem killing_equation_222_deformed_nondiagnostic (M a r θ ε : ℝ)
    (hSigma : sigma a r θ ≠ 0) (hDelta : delta M a r ≠ 0) (hDeltaEps : deltaEps M a r ε ≠ 0)
    (hSin : Real.sin θ ≠ 0) :
    killingResidual222 M a r θ ε = 0 := by
  exact killing_equation_222_deformed_value M a r θ ε hSigma hDelta hDeltaEps hSin

end RequestProject
