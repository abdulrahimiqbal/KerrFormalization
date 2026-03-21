import KerrFormalization.Kerr.KillingTensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-!
# Paper 2 Round 2 explicit Kerr/Δε component formulas

These definitions intentionally bypass the current coordinate-data Christoffel
pipeline in `KerrFormalization.Kerr.Christoffel`, whose metric derivative slots
are still placeholders for several Kerr components. Round 2 needs explicit
`r`/`θ` derivatives so that `Δ`-sensitive components such as `Γ^r_{rr}` are
actually live.

The exact Kerr formulas mirror the explicit component package Aristotle used in
the successful Round 1 `(0,0,0)` probe workspace, while the deformed formulas
replace `Δ` by `Δ_ε = r^2 - 2Mr + a^2 + εr` and `Δ'` by `2r - 2M + ε`.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- A Boyer-Lindquist sample point with prescribed `r, θ` and `t = φ = 0`. -/
def round2Point (r θ : ℝ) : CoordinateSpace 4 :=
  fun i =>
    if i = tIdx then 0
    else if i = rIdx then r
    else if i = thetaIdx then θ
    else 0

/-- Explicit inverse Kerr metric `g^{σρ}` at `(r, θ)`. -/
noncomputable def kerrInvMetricExplicit (M a r θ : ℝ) (σ ρ : Fin 4) : ℝ :=
  let S := sigma a r θ
  let D := delta M a r
  let s := Real.sin θ
  match σ.val, ρ.val with
  | 0, 0 => -((r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2) / (S * D)
  | 0, 3 => -2 * M * a * r / (S * D)
  | 3, 0 => -2 * M * a * r / (S * D)
  | 1, 1 => D / S
  | 2, 2 => 1 / S
  | 3, 3 => (S - 2 * M * r) / (S * D * s ^ 2)
  | _, _ => 0

/-- Explicit Kerr metric derivatives `∂_α g_{μν}` at `(r, θ)`. -/
noncomputable def kerrMetricDerivExplicit (M a r θ : ℝ) (α μ ν : Fin 4) : ℝ :=
  let S := sigma a r θ
  let D := delta M a r
  let s := Real.sin θ
  match α.val with
  | 0 => 0
  | 3 => 0
  | 1 =>
    match μ.val, ν.val with
    | 0, 0 => 2 * M * (S - 2 * r ^ 2) / S ^ 2
    | 0, 3 => -2 * M * a * s ^ 2 * (S - 2 * r ^ 2) / S ^ 2
    | 3, 0 => -2 * M * a * s ^ 2 * (S - 2 * r ^ 2) / S ^ 2
    | 1, 1 => 2 * (r * D - S * (r - M)) / D ^ 2
    | 2, 2 => 2 * r
    | 3, 3 =>
      let A := (r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2
      s ^ 2 *
        (S * (4 * r * (r ^ 2 + a ^ 2) - (2 * r - 2 * M) * a ^ 2 * s ^ 2) - 2 * r * A) /
        S ^ 2
    | _, _ => 0
  | 2 =>
    match μ.val, ν.val with
    | 0, 0 => 2 * M * r * a ^ 2 * Real.sin (2 * θ) / S ^ 2
    | 0, 3 => -2 * M * a * r * Real.sin (2 * θ) * (r ^ 2 + a ^ 2) / S ^ 2
    | 3, 0 => -2 * M * a * r * Real.sin (2 * θ) * (r ^ 2 + a ^ 2) / S ^ 2
    | 1, 1 => -a ^ 2 * Real.sin (2 * θ) / D
    | 2, 2 => -a ^ 2 * Real.sin (2 * θ)
    | 3, 3 =>
      let A := (r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2
      Real.sin (2 * θ) * ((A - D * a ^ 2 * s ^ 2) * S + a ^ 2 * A * s ^ 2) / S ^ 2
    | _, _ => 0
  | _ => 0

/-- Explicit Kerr Christoffel symbols built from the exact Kerr formulas above. -/
noncomputable def kerrChristoffelExplicit (M a r θ : ℝ) (σ μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ ρ : Fin 4,
      kerrInvMetricExplicit M a r θ σ ρ *
        (kerrMetricDerivExplicit M a r θ μ ν ρ
          + kerrMetricDerivExplicit M a r θ ν μ ρ
          - kerrMetricDerivExplicit M a r θ ρ μ ν)

/-- Explicit Form C Killing tensor components at `(r, θ)`. -/
noncomputable def killingTensorFormCExplicit (M a r θ : ℝ) (μ ν : Fin 4) : ℝ :=
  let S := sigma a r θ
  let D := delta M a r
  let s := Real.sin θ
  let c := Real.cos θ
  match μ.val, ν.val with
  | 0, 0 => D - r ^ 2 * (S - 2 * M * r) / S
  | 0, 3 => -a * s ^ 2 * (D * S + 2 * M * r ^ 3) / S
  | 3, 0 => -a * s ^ 2 * (D * S + 2 * M * r ^ 3) / S
  | 1, 1 => -a ^ 2 * c ^ 2 * S / D
  | 2, 2 => r ^ 2 * S
  | 3, 3 => a ^ 2 * D * s ^ 4 +
      r ^ 2 * ((r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2) * s ^ 2 / S
  | _, _ => 0

/-- Deformed Delta function: `Δ_ε = r² - 2Mr + a² + εr`. -/
noncomputable def DeltaEps (M a r ε : ℝ) : ℝ :=
  r ^ 2 - 2 * M * r + a ^ 2 + ε * r

/-- Auxiliary numerator `N = rΔ - (r - M)Σ` that controls the `(r,r,r)` probe. -/
noncomputable def kerrN (M a r θ : ℝ) : ℝ :=
  r * delta M a r - (r - M) * sigma a r θ

/-- Explicit inverse metric with `Δ` replaced by `Δ_ε`. -/
noncomputable def invMetricDeformed (M a r θ ε : ℝ) (σ ρ : Fin 4) : ℝ :=
  let S := sigma a r θ
  let D := DeltaEps M a r ε
  let s := Real.sin θ
  match σ.val, ρ.val with
  | 0, 0 => -((r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2) / (S * D)
  | 0, 3 => -2 * M * a * r / (S * D)
  | 3, 0 => -2 * M * a * r / (S * D)
  | 1, 1 => D / S
  | 2, 2 => 1 / S
  | 3, 3 => (S - 2 * M * r) / (S * D * s ^ 2)
  | _, _ => 0

/-- Explicit metric derivatives with `Δ` replaced by `Δ_ε` and `Δ' = 2r - 2M + ε`. -/
noncomputable def metricDerivDeformed (M a r θ ε : ℝ) (α μ ν : Fin 4) : ℝ :=
  let S := sigma a r θ
  let D := DeltaEps M a r ε
  let D' := 2 * r - 2 * M + ε
  let s := Real.sin θ
  match α.val with
  | 0 => 0
  | 3 => 0
  | 1 =>
    match μ.val, ν.val with
    | 0, 0 => 2 * M * (S - 2 * r ^ 2) / S ^ 2
    | 0, 3 => -2 * M * a * s ^ 2 * (S - 2 * r ^ 2) / S ^ 2
    | 3, 0 => -2 * M * a * s ^ 2 * (S - 2 * r ^ 2) / S ^ 2
    | 1, 1 => 2 * r / D - S * D' / D ^ 2
    | 2, 2 => 2 * r
    | 3, 3 =>
      let A := (r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2
      s ^ 2 * (S * (4 * r * (r ^ 2 + a ^ 2) - D' * a ^ 2 * s ^ 2) - 2 * r * A) / S ^ 2
    | _, _ => 0
  | 2 =>
    match μ.val, ν.val with
    | 0, 0 => 2 * M * r * a ^ 2 * Real.sin (2 * θ) / S ^ 2
    | 0, 3 => -2 * M * a * r * Real.sin (2 * θ) * (r ^ 2 + a ^ 2) / S ^ 2
    | 3, 0 => -2 * M * a * r * Real.sin (2 * θ) * (r ^ 2 + a ^ 2) / S ^ 2
    | 1, 1 => -a ^ 2 * Real.sin (2 * θ) / D
    | 2, 2 => -a ^ 2 * Real.sin (2 * θ)
    | 3, 3 =>
      let A := (r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2
      Real.sin (2 * θ) * ((A - D * a ^ 2 * s ^ 2) * S + a ^ 2 * A * s ^ 2) / S ^ 2
    | _, _ => 0
  | _ => 0

/-- Explicit deformed Christoffel symbols. -/
noncomputable def christoffelDeformed (M a r θ ε : ℝ) (σ μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ ρ : Fin 4,
      invMetricDeformed M a r θ ε σ ρ *
        (metricDerivDeformed M a r θ ε μ ν ρ
          + metricDerivDeformed M a r θ ε ν μ ρ
          - metricDerivDeformed M a r θ ε ρ μ ν)

/-- Explicit deformed Form C tensor with `Δ ↦ Δ_ε`. -/
noncomputable def killingTensorDeformed (M a r θ ε : ℝ) (μ ν : Fin 4) : ℝ :=
  let S := sigma a r θ
  let D := DeltaEps M a r ε
  let s := Real.sin θ
  let c := Real.cos θ
  match μ.val, ν.val with
  | 0, 0 => D - r ^ 2 * (S - 2 * M * r) / S
  | 0, 3 => -a * s ^ 2 * (D * S + 2 * M * r ^ 3) / S
  | 3, 0 => -a * s ^ 2 * (D * S + 2 * M * r ^ 3) / S
  | 1, 1 => -a ^ 2 * c ^ 2 * S / D
  | 2, 2 => r ^ 2 * S
  | 3, 3 => a ^ 2 * D * s ^ 4 +
      r ^ 2 * ((r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2) * s ^ 2 / S
  | _, _ => 0

end Paper2
end KerrFormalization
