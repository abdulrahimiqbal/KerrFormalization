import KerrFormalization.Kerr.KillingTensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Test 05: Killing Tensor for an `ε`-Deformed Kerr Ansatz

Paper 2 first probe. We deform the Kerr `Δ` function by

`Δ_ε = r² - 2Mr + a² + εr`.

The current repo does not yet contain a fully deformed metric or deformed
Christoffel symbols, so this test keeps the existing Kerr Christoffel symbols
and asks whether the `000` contraction still vanishes for a Form C-style tensor
ansatz with `Δ` replaced by `Δ_ε` in the slots where `Δ` appears explicitly.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Paper2

open Kerr
open LocalCoordinates

/-- A Boyer-Lindquist sample point with prescribed `r, θ` and `t = φ = 0`. -/
def test05Point (r θ : ℝ) : CoordinateSpace 4 :=
  fun i =>
    if i = tIdx then 0
    else if i = rIdx then r
    else if i = thetaIdx then θ
    else 0

/-- Deformed Delta function: `Δ_ε = r² - 2Mr + a² + εr`. -/
noncomputable def DeltaDeformed (M a r ε : ℝ) : ℝ :=
  r ^ 2 - 2 * M * r + a ^ 2 + ε * r

/-- Deformed Sigma, unchanged from Kerr: `Σ = r² + a² cos² θ`. -/
noncomputable def SigmaDeformed (a r θ : ℝ) : ℝ :=
  r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2

/-- At `ε = 0`, the deformation reduces to the standard Kerr `Δ`. -/
theorem delta_deformed_at_zero (M a r : ℝ) :
    DeltaDeformed M a r 0 = r ^ 2 - 2 * M * r + a ^ 2 := by
  sorry

/-- A Form C-style deformed tensor obtained by replacing `Δ` by `Δ_ε`
in the explicit slots where `Δ` occurs. -/
noncomputable def killingTensorDeformed (M a r θ ε : ℝ) (μ ν : Fin 4) : ℝ :=
  let deltaVal := DeltaDeformed M a r ε
  let sigmaVal := SigmaDeformed a r θ
  let s := Real.sin θ
  let c := Real.cos θ
  if μ = tIdx ∧ ν = tIdx then
    a ^ 2 - 2 * M * r * a ^ 2 * c ^ 2 / sigmaVal
  else if μ = rIdx ∧ ν = rIdx then
    -(a ^ 2 * c ^ 2 * sigmaVal / deltaVal)
  else if μ = thetaIdx ∧ ν = thetaIdx then
    r ^ 2 * sigmaVal
  else if (μ = tIdx ∧ ν = phiIdx) ∨ (μ = phiIdx ∧ ν = tIdx) then
    -(a * deltaVal * s ^ 2) +
      r ^ 2 * CoordinateMetricData.value (kerrMetricData M a) (test05Point r θ) tIdx phiIdx
  else if μ = phiIdx ∧ ν = phiIdx then
    a ^ 2 * deltaVal * s ^ 4 +
      r ^ 2 * CoordinateMetricData.value (kerrMetricData M a) (test05Point r θ) phiIdx phiIdx
  else
    0

/-- Paper 2 probe: does the Kerr `000` contraction remain zero under the
`Δ ↦ Δ_ε` tensor deformation? -/
theorem killing_equation_deformed_000
    (M a r θ ε : ℝ)
    (hM : M > 0) (ha : a ≥ 0) (haM : a < M)
    (hr : r > 0) (hθ : 0 < θ ∧ θ < Real.pi)
    (hΣ : SigmaDeformed a r θ ≠ 0)
    (hΔε : DeltaDeformed M a r ε ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    ∑ σ : Fin 4,
      kerrChristoffel M a (test05Point r θ) σ tIdx tIdx *
        killingTensorDeformed M a r θ ε σ tIdx = 0 := by
  sorry

end Paper2
end KerrFormalization
