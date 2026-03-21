import KerrFormalization.Kerr.KillingTensor

/-!
# Test 01: Killing Tensor Symmetry

Paper 2 calibration test. The explicit Form C Killing tensor should satisfy
`K(μ,ν) = K(ν,μ)` for all coordinate indices `μ, ν : Fin 4`.
This is a pure algebraic check with the current component formulas.
-/

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- A Boyer-Lindquist sample point with prescribed `r, θ` and `t = φ = 0`. -/
def test01Point (r θ : ℝ) : CoordinateSpace 4 :=
  fun i =>
    if i = tIdx then 0
    else if i = rIdx then r
    else if i = thetaIdx then θ
    else 0

/-- The Form C Killing tensor is symmetric: `K(μ,ν) = K(ν,μ)`. -/
theorem killingTensorFormC_symmetric
    (M a r θ : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (μ ν : Fin 4) :
    killingTensorFormC M a (test01Point r θ) μ ν =
      killingTensorFormC M a (test01Point r θ) ν μ := by
  sorry

end Paper2
end KerrFormalization
