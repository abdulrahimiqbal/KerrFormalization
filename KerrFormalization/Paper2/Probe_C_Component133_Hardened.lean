import Mathlib

open scoped BigOperators

/-!
# Probe C Hardened: Killing Equation Component `(1,3,3)`

This is a self-contained version of Probe C part (a). It deliberately embeds
the exact Kerr formulas needed for the `(r, φ, φ)` contraction so Aristotle
cannot replace imported dependencies with a simplified surrogate model.
-/

namespace KerrFormalization
namespace Paper2

namespace Kerr

noncomputable def sigma (a r th : ℝ) : ℝ :=
  r ^ 2 + a ^ 2 * (Real.cos th) ^ 2

noncomputable def delta (M a r : ℝ) : ℝ :=
  r ^ 2 - 2 * M * r + a ^ 2

end Kerr

namespace LocalCoordinates

def tIdx : Fin 4 := 0
def rIdx : Fin 4 := 1
def thetaIdx : Fin 4 := 2
def phiIdx : Fin 4 := 3

end LocalCoordinates

open Kerr
open LocalCoordinates

/-- Exact Kerr Christoffel symbols used in the Round 2 explicit probes. -/
noncomputable def kerrInvMetricExplicit (M a r th : ℝ) (σ ρ : Fin 4) : ℝ :=
  let S := sigma a r th
  let D := delta M a r
  let s := Real.sin th
  match σ.val, ρ.val with
  | 0, 0 => -((r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2) / (S * D)
  | 0, 3 => -2 * M * a * r / (S * D)
  | 3, 0 => -2 * M * a * r / (S * D)
  | 1, 1 => D / S
  | 2, 2 => 1 / S
  | 3, 3 => (S - 2 * M * r) / (S * D * s ^ 2)
  | _, _ => 0

/-- Exact Kerr metric derivatives used in the Round 2 explicit probes. -/
noncomputable def kerrMetricDerivExplicit (M a r th : ℝ) (α μ ν : Fin 4) : ℝ :=
  let S := sigma a r th
  let D := delta M a r
  let s := Real.sin th
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
    | 0, 0 => 2 * M * r * a ^ 2 * Real.sin (2 * th) / S ^ 2
    | 0, 3 => -2 * M * a * r * Real.sin (2 * th) * (r ^ 2 + a ^ 2) / S ^ 2
    | 3, 0 => -2 * M * a * r * Real.sin (2 * th) * (r ^ 2 + a ^ 2) / S ^ 2
    | 1, 1 => -a ^ 2 * Real.sin (2 * th) / D
    | 2, 2 => -a ^ 2 * Real.sin (2 * th)
    | 3, 3 =>
      let A := (r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2
      Real.sin (2 * th) * ((A - D * a ^ 2 * s ^ 2) * S + a ^ 2 * A * s ^ 2) / S ^ 2
    | _, _ => 0
  | _ => 0

/-- Exact Kerr Christoffel symbols from the explicit metric formulas. -/
noncomputable def kerrChristoffelExplicit (M a r th : ℝ) (σ μ ν : Fin 4) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ ρ : Fin 4,
      kerrInvMetricExplicit M a r th σ ρ *
        (kerrMetricDerivExplicit M a r th μ ν ρ
          + kerrMetricDerivExplicit M a r th ν μ ρ
          - kerrMetricDerivExplicit M a r th ρ μ ν)

/-- Exact Form C Killing tensor used in the Round 2 explicit probes. -/
noncomputable def killingTensorFormCExplicit (M a r th : ℝ) (μ ν : Fin 4) : ℝ :=
  let S := sigma a r th
  let D := delta M a r
  let s := Real.sin th
  let c := Real.cos th
  match μ.val, ν.val with
  | 0, 0 => D - r ^ 2 * (S - 2 * M * r) / S
  | 0, 3 => -a * s ^ 2 * (D * S + 2 * M * r ^ 3) / S
  | 3, 0 => -a * s ^ 2 * (D * S + 2 * M * r ^ 3) / S
  | 1, 1 => -a ^ 2 * c ^ 2 * S / D
  | 2, 2 => r ^ 2 * S
  | 3, 3 => a ^ 2 * D * s ^ 4 +
      r ^ 2 * ((r ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * s ^ 2) * s ^ 2 / S
  | _, _ => 0

/-- Hardened Probe C A: the exact Kerr `(r,φ,φ)` contraction. -/
theorem killing_equation_133_contraction_A_hardened
    (M a r th : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hth : 0 < th ∧ th < Real.pi)
    (hSig : sigma a r th ≠ 0)
    (hDel : delta M a r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    ∑ σ : Fin 4,
      kerrChristoffelExplicit M a r th σ rIdx phiIdx *
        killingTensorFormCExplicit M a r th σ phiIdx = 0 := by
  sorry

/-- Hardened Probe C full: the full Christoffel contribution in `(r,φ,φ)`. -/
theorem killing_equation_133_full_christoffel_hardened
    (M a r th : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hth : 0 < th ∧ th < Real.pi)
    (hSig : sigma a r th ≠ 0)
    (hDel : delta M a r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (∑ σ : Fin 4,
      kerrChristoffelExplicit M a r th σ rIdx phiIdx *
          killingTensorFormCExplicit M a r th σ phiIdx +
        kerrChristoffelExplicit M a r th σ rIdx phiIdx *
          killingTensorFormCExplicit M a r th phiIdx σ) +
    2 * (∑ σ : Fin 4,
      kerrChristoffelExplicit M a r th σ phiIdx rIdx *
          killingTensorFormCExplicit M a r th σ phiIdx +
        kerrChristoffelExplicit M a r th σ phiIdx phiIdx *
          killingTensorFormCExplicit M a r th rIdx σ) = 0 := by
  sorry

end Paper2
end KerrFormalization
