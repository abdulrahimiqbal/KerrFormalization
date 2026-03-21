import KerrFormalization.Paper2.Q2_CarterDrift

/-!
# Q2-B: Schwarzschild Protection Under the `Δ`-Deformation

The leading Probe A obstruction carries an overall factor of `a^2`, so the
effective Carter drift disappears in the Schwarzschild limit.
-/

namespace KerrFormalization
namespace Paper2

open Kerr

/-- The deformed `(1,1,1)` contraction vanishes identically at `a = 0`. -/
theorem schwarzschild_protected_111
    (M r θ ε : ℝ)
    (hM : M > 0) (hr : r > 0)
    (hθ : 0 < θ ∧ θ < Real.pi)
    (hΔε : r ^ 2 - 2 * M * r + ε * r ≠ 0) :
    killingEq111_contraction M 0 r θ ε = 0 := by
  sorry

/-- The leading-order Carter drift vanishes for all deformed Schwarzschild orbits. -/
theorem schwarzschild_drift_zero_all_orbits
    (M r θ ε ur : ℝ)
    (hM : M > 0) (hr : r > 0)
    (hΔ : r ^ 2 - 2 * M * r + ε * r ≠ 0) :
    carterDriftRate M 0 r θ ε ur = 0 := by
  sorry

end Paper2
end KerrFormalization
