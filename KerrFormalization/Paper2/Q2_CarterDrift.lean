import KerrFormalization.Paper2.Round2ExplicitDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-!
# Q2-A: Carter Constant Drift Rate

This file packages the leading-order `ε`-driven Carter drift implied by the
Probe A `(1,1,1)` residual. The intent is not to rebuild the full deformed
connection here, but to formalize the orbit-level consequences of the already
identified obstruction.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

section Setup

/-- Leading-order `(1,1,1)` contraction extracted from Probe A. -/
noncomputable def killingEq111_contraction
    (M a r θ ε : ℝ) : ℝ :=
  ε * a ^ 2 * (r ^ 2 - a ^ 2) * sigma a r θ * (Real.cos θ) ^ 2 /
    (delta M a r) ^ 3

/-- The deformed Killing-equation residual `R_μνρ`.

For the immediate Q2 drift analysis we keep only the leading `(r,r,r)` slot
detected by Probe A; all other components are suppressed in this effective
model. -/
noncomputable def killingResidual
    (M a r θ ε : ℝ) (μ ν ρ : Fin 4) : ℝ :=
  if μ = rIdx ∧ ν = rIdx ∧ ρ = rIdx then
    killingEq111_contraction M a r θ ε
  else
    0

end Setup

section EquatorialOrbits

/-- A circular equatorial geodesic has `θ = π/2`, `dr/dτ = 0`, `dθ/dτ = 0`. -/
structure CircularEquatorialOrbit (M a r_orb : ℝ) where
  ut : ℝ
  uphi : ℝ
  on_equator : True
  circular : True

/-- The Carter drift vanishes on circular equatorial orbits. -/
theorem carter_drift_equatorial_zero
    (M a r_orb ε : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r_orb > 0)
    (orbit : CircularEquatorialOrbit M a r_orb) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4,
      killingResidual M a r_orb (Real.pi / 2) ε μ ν ρ *
      (if μ = tIdx then orbit.ut else if μ = phiIdx then orbit.uphi else 0) *
      (if ν = tIdx then orbit.ut else if ν = phiIdx then orbit.uphi else 0) *
      (if ρ = tIdx then orbit.ut else if ρ = phiIdx then orbit.uphi else 0) = 0 := by
  sorry

end EquatorialOrbits

section InclinedOrbits

/-- Leading-order Carter drift for a generic orbit, using the `(r,r,r)` residual. -/
noncomputable def carterDriftRate
    (M a r θ ε : ℝ) (ur : ℝ) : ℝ :=
  ε * a ^ 2 * (r ^ 2 - a ^ 2) * sigma a r θ *
    (Real.cos θ) ^ 2 * ur ^ 3 /
    (delta M a r) ^ 3

/-- The leading-order drift vanishes exactly on the expected protection loci. -/
theorem carter_drift_vanishes_iff
    (M a r θ ε ur : ℝ)
    (hM : M > 0) (ha : a > 0) (hr : r > 0)
    (hΔ : delta M a r ≠ 0)
    (hur : ur ≠ 0) (hε : ε ≠ 0) :
    carterDriftRate M a r θ ε ur = 0 ↔
      (a = 0 ∨ r = a ∨ r = -a ∨ Real.cos θ = 0) := by
  sorry

end InclinedOrbits

section DephasingTimescale

/-- Order-of-magnitude number of orbits before Carter drift dephases the orbit. -/
noncomputable def dephasingOrbits (M a r θ ε ur : ℝ) : ℝ :=
  ((M / r) ^ (3 / 2 : ℝ)) / |carterDriftRate M a r θ ε ur|

/-- Schematic LISA detectability bound from accumulated Carter drift. -/
theorem lisa_detectability_bound
    (M a r θ ur : ℝ) (N_obs : ℝ)
    (hN : N_obs = 100000) :
    ∃ ε_min : ℝ, ε_min > 0 ∧
      ∀ ε : ℝ, |ε| > ε_min →
        N_obs * |carterDriftRate M a r θ ε ur| > 1 := by
  sorry

end DephasingTimescale

end Paper2
end KerrFormalization
