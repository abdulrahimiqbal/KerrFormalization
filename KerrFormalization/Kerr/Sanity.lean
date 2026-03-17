import KerrFormalization.Kerr.Horizons
import KerrFormalization.Kerr.ComponentLemmas
import KerrFormalization.Schwarzschild.Metric

/-!
# Kerr sanity and validation checks

Concrete checks that the Kerr coordinate-data layer matches standard
Boyer-Lindquist formulas and basic consistency reductions.

STATUS (March 2026): This file is restricted to metric/component sanity checks;
it does not certify Ricci-vanishing or vacuum completion.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Kerr and Schwarzschild use the same radial index convention. -/
@[simp] theorem rIdx_eq_schwarzschild_rIdx : (rIdx : Fin 4) = Schwarzschild.rIdx := rfl
/-- Kerr and Schwarzschild use the same polar index convention. -/
@[simp] theorem thetaIdx_eq_schwarzschild_thetaIdx : (thetaIdx : Fin 4) = Schwarzschild.thetaIdx := rfl

section AuxiliaryChecks

/-- Unfolding lemma for `Δ`. -/
@[simp] theorem delta_unfold (M a r : ℝ) :
    delta M a r = r ^ 2 - 2 * M * r + a ^ 2 := rfl

/-- Unfolding lemma for `Σ`. -/
@[simp] theorem sigma_unfold (a r θ : ℝ) :
    sigma a r θ = r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2 := rfl

end AuxiliaryChecks

section MetricComponentChecks

/-- `g_tt` in Boyer-Lindquist coordinates. -/
theorem metric_tt (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x tIdx tIdx =
      -(1 - (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx)) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, gttField]

/-- `g_rr` in Boyer-Lindquist coordinates. -/
theorem metric_rr (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x rIdx rIdx =
      sigma a (x rIdx) (x thetaIdx) / delta M a (x rIdx) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, grrField]

/-- `g_θθ` in Boyer-Lindquist coordinates. -/
theorem metric_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x thetaIdx thetaIdx =
      sigma a (x rIdx) (x thetaIdx) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, gThetaThetaField]

/-- Off-diagonal `g_tφ` in Boyer-Lindquist coordinates. -/
theorem metric_tPhi (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x tIdx phiIdx =
      -(2 * M * a * x rIdx * (Real.sin (x thetaIdx)) ^ 2 / sigma a (x rIdx) (x thetaIdx)) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx, gtPhiField]

/-- `g_φφ` in Boyer-Lindquist coordinates. -/
theorem metric_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x phiIdx phiIdx =
      (((x rIdx) ^ 2 + a ^ 2) ^ 2 - a ^ 2 * delta M a (x rIdx) * (Real.sin (x thetaIdx)) ^ 2)
        * (Real.sin (x thetaIdx)) ^ 2 / sigma a (x rIdx) (x thetaIdx) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, gPhiPhiField]

end MetricComponentChecks

section HorizonChecks

/-- Standard horizon ordering helper. -/
theorem horizons_ordered (M a : ℝ) :
    innerHorizon M a ≤ outerHorizon M a :=
  innerHorizon_le_outerHorizon M a

/-- Sum relation `r_+ + r_- = 2M`. -/
theorem horizon_sum_is_twice_mass (M a : ℝ) :
    outerHorizon M a + innerHorizon M a = 2 * M :=
  horizon_sum M a

/-- Product relation `r_+ r_- = a^2` under nonnegative discriminant. -/
theorem horizon_product_is_spin_square (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    outerHorizon M a * innerHorizon M a = a ^ 2 :=
  horizon_product M a hdisc

end HorizonChecks

section ReductionToSchwarzschild

/-- `g_tt` reduces to Schwarzschild at zero spin (`a = 0`) away from `r = 0`. -/
theorem gtt_reduces_to_schwarzschild (M : ℝ) (x : CoordinateSpace 4)
    (hr : x rIdx ≠ 0) :
    gttField M 0 x = Schwarzschild.gttField M x := by
  have hrEq : x Schwarzschild.rIdx = x rIdx := rfl
  have hrSch : x Schwarzschild.rIdx ≠ 0 := by simpa [hrEq] using hr
  simp [gttField, Schwarzschild.gttField, Schwarzschild.lapse, sigma, hrEq, pow_two]
  field_simp [hr, hrSch]

/-- `g_θθ` reduces to Schwarzschild at zero spin. -/
theorem gThetaTheta_reduces_to_schwarzschild (x : CoordinateSpace 4) :
    gThetaThetaField 0 x = Schwarzschild.gThetaThetaField x := by
  simp [gThetaThetaField, sigma, Schwarzschild.gThetaThetaField]

/-- `g_φφ` reduces to Schwarzschild at zero spin (`a = 0`) away from `r = 0`. -/
theorem gPhiPhi_reduces_to_schwarzschild (M : ℝ) (x : CoordinateSpace 4)
    (hr : x rIdx ≠ 0) :
    gPhiPhiField M 0 x = Schwarzschild.gPhiPhiField x := by
  have hrEq : x Schwarzschild.rIdx = x rIdx := rfl
  have hthetaEq : x Schwarzschild.thetaIdx = x thetaIdx := rfl
  have hrSch : x Schwarzschild.rIdx ≠ 0 := by simpa [hrEq] using hr
  simp [gPhiPhiField, sigma, delta, Schwarzschild.gPhiPhiField, hrEq, hthetaEq]
  field_simp [hr, hrSch]

/-- `g_tφ` vanishes identically in the zero-spin limit. -/
theorem gtPhi_zero_at_zero_spin (M : ℝ) (x : CoordinateSpace 4) :
    gtPhiField M 0 x = 0 := by
  simp [gtPhiField, sigma]

end ReductionToSchwarzschild

end Kerr
end KerrFormalization
