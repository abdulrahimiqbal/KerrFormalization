import KerrFormalization.Kerr.KillingYanoEquation
import KerrFormalization.Kerr.KillingTensor
import KerrFormalization.Kerr.InverseMetricExact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Kerr Killing-Yano tensor squared to a Killing tensor

The pointwise square is recorded here in the exact Kerr coordinate-data model.
With the current lower-index convention for the covariant 2-form, the version
that matches the existing Form C Killing tensor carries a leading minus sign.
The abstract theorem that a Killing-Yano 2-form squares to a Killing tensor is
left as a focused `sorry` for Aristotle.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open Trusted

/-- The pointwise square of the Kerr Killing-Yano 2-form. -/
noncomputable def killingTensorFromKillingYano (M a : ℝ) (x : CoordinateSpace 4)
    (μ ν : Fin 4) : ℝ :=
  - Finset.univ.sum (fun ρ : Fin 4 =>
    Finset.univ.sum (fun σ : Fin 4 =>
      killingYanoComponent M a μ ρ x *
        kerrInverseMetricData M a x ρ σ *
        killingYanoComponent M a σ ν x))

-- TODO: Aristotle should expand `killingTensorFromKillingYano`, rewrite it to the
-- existing Form C tensor, and then discharge the symmetrized Killing tensor equation.
theorem killingYano_square_is_killingTensor (M a : ℝ)
    (hSquare : ∀ x : CoordinateSpace 4, ∀ μ ν : Fin 4,
      killingTensorFromKillingYano M a x μ ν = killingTensorFormC M a x μ ν)
    (hKY : ∀ x : CoordinateSpace 4, ∀ α β γ : Fin 4,
      covDerivKillingYano M a x α β γ + covDerivKillingYano M a x β α γ = 0) :
    ∀ x : CoordinateSpace 4, ∀ α μ ν : Fin 4,
      covDerivKillingFormC M a x α μ ν +
      covDerivKillingFormC M a x μ ν α +
      covDerivKillingFormC M a x ν α μ = 0 := by
  clear hSquare hKY
  -- ATTEMPT: the intended abstract Leibniz proof is straightforward once the
  -- square identity below is available and `partialKillingTensorFormC` is
  -- replaced by the derivative of the square-built tensor. Right now this file
  -- still routes through the placeholder derivative in `KillingTensor.lean`,
  -- so the proof remains a target rather than a certified result.
  sorry

-- TODO: Aristotle should verify the componentwise algebra that identifies the
-- square-built tensor with the existing Form C Killing tensor.
theorem killingTensorSquare_eq_formC (M a : ℝ) (x : CoordinateSpace 4) :
    ∀ μ ν : Fin 4,
      killingTensorFromKillingYano M a x μ ν = killingTensorFormC M a x μ ν := by
  intro μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [killingTensorFromKillingYano, killingYanoComponent, killingTensorFormC,
      kerrInverseMetricData, offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx,
      Fin.sum_univ_four]

end Kerr
end KerrFormalization
