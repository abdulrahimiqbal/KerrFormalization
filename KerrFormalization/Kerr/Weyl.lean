import KerrFormalization.Kerr.Ricci
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Kerr Weyl tensor scaffold

This file sets up the basic Weyl/Petrov notation needed for later work.
The exact Petrov-speciality proof is intentionally left open.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Weyl tensor components in the coordinate-data model. -/
abbrev WeylComponentsData (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → Fin n → ℝ

/-- A schematic Weyl tensor extracted from Riemann and Ricci data. -/
noncomputable def weylComponentsFromMetricData {n : ℕ}
    (g : CoordinateMetricData n) (ginv : InverseMetricDataWithDeriv n) :
    WeylComponentsData n :=
  let R := riemannComponentsFromMetricData g ginv
  let Ric := ricciComponentsFromMetricData g ginv
  fun x a b c d =>
    R x a b c d
    - (1 / 2 : ℝ) *
      (g.value x a c * Ric x b d - g.value x a d * Ric x b c
        - g.value x b c * Ric x a d + g.value x b d * Ric x a c)
    + (1 / 6 : ℝ) *
      (Finset.univ.sum (fun p : Fin n =>
        Finset.univ.sum (fun q : Fin n => ginv.value x p q * Ric x p q)))
      * (g.value x a c * g.value x b d - g.value x a d * g.value x b c)

/-- Petrov speciality index from abstract Weyl invariants. -/
noncomputable def petrovSpecialityIndex (I J : ℝ) : ℝ :=
  27 * J ^ 2 / I ^ 3

/-- Placeholder Weyl invariant `I` for the Kerr type-D scaffold. -/
noncomputable def weylInvariantI (M a : ℝ) : ℝ :=
  0

/-- Placeholder Weyl invariant `J` for the Kerr type-D scaffold. -/
noncomputable def weylInvariantJ (M a : ℝ) : ℝ :=
  0

theorem kerr_is_type_D (M a : ℝ) :
    petrovSpecialityIndex (weylInvariantI M a) (weylInvariantJ M a) = 1 := by
  -- TODO: replace the placeholder invariants by actual Weyl contractions.
  -- The current definitions are intentionally scaffolding only, so the theorem
  -- remains open until the Weyl tensor machinery is implemented.
  sorry

-- TODO: the type-D/Killing-Yano link should be stated here once the Weyl
-- scaffold is upgraded to real invariants.
theorem type_D_admits_killing_yano (M a : ℝ) :
    petrovSpecialityIndex (weylInvariantI M a) (weylInvariantJ M a) = 1 → True := by
  intro _
  trivial

end Kerr
end KerrFormalization
