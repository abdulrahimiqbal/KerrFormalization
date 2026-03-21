import KerrFormalization.Kerr.KillingTensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Test 04: Single Component of the Killing Tensor Equation

Paper 2 calibration. We isolate the `(0,0,0)` contraction that remains after
using stationarity to drop the explicit `∂ₜ K₀₀` term:

`∑ σ, Γ^σ_{00} K_{σ0} = 0`.

This is the smallest concrete component probe of the full symmetrized Killing
equation available in the current coordinate-data infrastructure.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- A Boyer-Lindquist sample point with prescribed `r, θ` and `t = φ = 0`. -/
def test04Point (r θ : ℝ) : CoordinateSpace 4 :=
  fun i =>
    if i = tIdx then 0
    else if i = rIdx then r
    else if i = thetaIdx then θ
    else 0

/-- The `(0,0,0)` Christoffel-Killing contraction vanishes. -/
theorem killing_equation_000
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : Kerr.sigma a r θ ≠ 0)
    (hΔ : Kerr.delta M a r ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∑ σ : Fin 4,
      kerrChristoffel M a (test04Point r θ) σ tIdx tIdx *
        killingTensorFormC M a (test04Point r θ) σ tIdx = 0 := by
  sorry

end Paper2
end KerrFormalization
