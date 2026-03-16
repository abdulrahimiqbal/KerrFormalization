import KerrFormalization.Kerr.ReductionToSchwarzschild
import KerrFormalization.Kerr.Ergoregion

/-!
# Kerr validation facade

A presentation-oriented facade collecting the key sanity checks for the current
Kerr formalization in Boyer-Lindquist coordinates.

This module does not add new mathematics: it only re-exposes established results
with names that are convenient for smoke checks and documentation.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Public validation alias for the Kerr vacuum theorem. -/
theorem kerrVacuumValidated (M a : ℝ) :
    IsVacuumMetricData (kerrMetricData M a) (kerrInverseMetricWithDeriv M a) :=
  kerrIsVacuum M a

/-- Public validation alias for the Kerr `\Delta` formula. -/
@[simp] theorem deltaFormula (M a r : ℝ) :
    delta M a r = r ^ 2 - 2 * M * r + a ^ 2 :=
  delta_unfold M a r

/-- Public validation alias for the Kerr `\Sigma` formula. -/
@[simp] theorem sigmaFormula (a r θ : ℝ) :
    sigma a r θ = r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2 :=
  sigma_unfold a r θ

/-- Outer horizon is a root of `\Delta` when the discriminant is nonnegative. -/
theorem outerHorizonIsDeltaRoot (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    delta M a (outerHorizon M a) = 0 :=
  delta_outerHorizon_eq_zero M a hdisc

/-- Inner horizon is a root of `\Delta` when the discriminant is nonnegative. -/
theorem innerHorizonIsDeltaRoot (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    delta M a (innerHorizon M a) = 0 :=
  delta_innerHorizon_eq_zero M a hdisc

/-- Public validation bundle for the standard zero-spin component reductions. -/
theorem zeroSpinReductionValidated (M : ℝ) (x : CoordinateSpace 4)
    (hr : x rIdx ≠ 0) :
    ZeroSpinComponentAgreement M x :=
  zeroSpinComponentAgreement M x hr

/-- Public validation alias for the Kerr ergoregion membership criterion. -/
theorem ergoregionCriterion (M a : ℝ) (x : CoordinateSpace 4) :
    x ∈ ergoregion M a ↔ gttField M a x > 0 :=
  mem_ergoregion_iff M a x

end Kerr
end KerrFormalization
