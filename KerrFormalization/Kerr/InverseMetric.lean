import KerrFormalization.Kerr.BoyerLindquist

/-!
# Kerr inverse metric data in Boyer-Lindquist coordinates
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Pointwise inverse Kerr metric components in Boyer-Lindquist coordinates. -/
noncomputable def kerrInverseMetricData (M a : ℝ) : InverseMetricData 4 :=
  by
    classical
    intro x i j
    let r := x rIdx
    let th := x thetaIdx
    let deltaVal := delta M a r
    let sigmaVal := sigma a r th
    let s2 := (Real.sin th)^2
    exact if hOff : offDiagTPhi i j then
      -(2 * M * a * r / (deltaVal * sigmaVal))
    else if hDiag : i = j then
      if i = tIdx then
        -((((r^2 + a^2)^2 - a^2 * deltaVal * s2) / (deltaVal * sigmaVal)))
      else if i = rIdx then
        deltaVal / sigmaVal
      else if i = thetaIdx then
        sigmaVal⁻¹
      else if i = phiIdx then
        (deltaVal - a^2 * s2) / (deltaVal * sigmaVal * s2)
      else 0
    else 0

/--
Inverse Kerr metric data with supplied first derivatives of inverse components.

Current derivative slots are placeholders and will be refined in a follow-up
curvature tranche.
-/
noncomputable def kerrInverseMetricWithDeriv (M a : ℝ) : InverseMetricDataWithDeriv 4 where
  value := kerrInverseMetricData M a
  deriv := fun _ _ _ _ => 0

end Kerr
end KerrFormalization
