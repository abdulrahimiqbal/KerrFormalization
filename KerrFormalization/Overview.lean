import KerrFormalization.Kerr.Validation
import KerrFormalization.Schwarzschild

/-!
# Project overview surface

This module provides a compact, public-facing summary of what the current
formalization establishes.

It intentionally re-exports established, fully checked results without changing
scope.

STATUS (March 2026): Vacuum theorems are not re-exported here because the
underlying Ricci-vanishing component proofs are still incomplete.
-/

namespace KerrFormalization

open LocalCoordinates

/-- Public alias for Kerr `Δ` formula validation. -/
@[simp] theorem deltaFormula_v1 (M a r : ℝ) :
    Kerr.delta M a r = r ^ 2 - 2 * M * r + a ^ 2 :=
  Kerr.deltaFormula M a r

/-- Public alias for Kerr `Σ` formula validation. -/
@[simp] theorem sigmaFormula_v1 (a r θ : ℝ) :
    Kerr.sigma a r θ = r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2 :=
  Kerr.sigmaFormula a r θ

/-- Public alias for Kerr outer-horizon root identity under nonnegative discriminant. -/
theorem outerHorizonIsDeltaRoot_v1 (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    Kerr.delta M a (Kerr.outerHorizon M a) = 0 :=
  Kerr.outerHorizonIsDeltaRoot M a hdisc

/-- Public alias for Kerr ergoregion criterion. -/
theorem ergoregionCriterion_v1 (M a : ℝ) (x : CoordinateSpace 4) :
    x ∈ Kerr.ergoregion M a ↔ Kerr.gttField M a x > 0 :=
  Kerr.ergoregionCriterion M a x

end KerrFormalization
