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
  deriv := by
    classical
    exact fun k x i j =>
      let r := x rIdx
      let th := x thetaIdx
      let D := delta M a r
      let S := sigma a r th
      let s2 := (Real.sin th) ^ 2
      let twoMr := 2 * r - 2 * M
      let dSdr := 2 * r
      let dSdth := -a ^ 2 * Real.sin (2 * th)
      let A := (r ^ 2 + a ^ 2) ^ 2 - a ^ 2 * D * s2
      if hOff : offDiagTPhi i j then
        if k = rIdx then
          -2 * M * a *
            (D * S - r * (twoMr * S + D * dSdr)) / (D * S) ^ 2
        else if k = thetaIdx then
          2 * M * a * r * dSdth / (D * S ^ 2)
        else 0
      else if hDiag : i = j then
        if i = tIdx then
          if k = rIdx then
            -((4 * r * (r ^ 2 + a ^ 2) - a ^ 2 * twoMr * s2) * (D * S) -
              A * (twoMr * S + D * dSdr)) / (D * S) ^ 2
          else if k = thetaIdx then
            -((-a ^ 2 * D * Real.sin (2 * th)) * (D * S) - A * (D * dSdth)) / (D * S) ^ 2
          else 0
        else if i = rIdx then
          if k = rIdx then
            (twoMr * S - D * dSdr) / S ^ 2
          else if k = thetaIdx then
            -D * dSdth / S ^ 2
          else 0
        else if i = thetaIdx then
          if k = rIdx then
            -dSdr / S ^ 2
          else if k = thetaIdx then
            -dSdth / S ^ 2
          else 0
        else if i = phiIdx then
          let N := D - a ^ 2 * s2
          if k = rIdx then
            (twoMr * (D * S * s2) - N * ((twoMr * S + D * dSdr) * s2)) / (D * S * s2) ^ 2
          else if k = thetaIdx then
            ((-a ^ 2 * Real.sin (2 * th)) * (D * S * s2) -
              N * (D * (dSdth * s2 + S * Real.sin (2 * th)))) / (D * S * s2) ^ 2
          else 0
        else 0
      else 0

end Kerr
end KerrFormalization
