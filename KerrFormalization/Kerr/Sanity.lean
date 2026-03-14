import KerrFormalization.Kerr.Vacuum
import KerrFormalization.Kerr.Horizons
import KerrFormalization.Kerr.ComponentLemmas
import KerrFormalization.Schwarzschild.Metric

/-!
# Kerr sanity and validation checks

Concrete checks that the Kerr coordinate-data layer matches standard
Boyer-Lindquist formulas and basic consistency reductions.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

@[simp] theorem rIdx_eq_schwarzschild_rIdx : (rIdx : Fin 4) = Schwarzschild.rIdx := rfl
@[simp] theorem thetaIdx_eq_schwarzschild_thetaIdx : (thetaIdx : Fin 4) = Schwarzschild.thetaIdx := rfl

section AuxiliaryChecks

@[simp] theorem delta_unfold (M a r : ℝ) :
    delta M a r = r ^ 2 - 2 * M * r + a ^ 2 := rfl

@[simp] theorem sigma_unfold (a r θ : ℝ) :
    sigma a r θ = r ^ 2 + a ^ 2 * (Real.cos θ) ^ 2 := rfl

end AuxiliaryChecks

section MetricComponentChecks

theorem metric_tt (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x tIdx tIdx =
      -(1 - (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx)) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, gttField]

theorem metric_rr (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x rIdx rIdx =
      sigma a (x rIdx) (x thetaIdx) / delta M a (x rIdx) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, grrField]

theorem metric_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x thetaIdx thetaIdx =
      sigma a (x rIdx) (x thetaIdx) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, gThetaThetaField]

theorem metric_tPhi (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x tIdx phiIdx =
      -(2 * M * a * x rIdx * (Real.sin (x thetaIdx)) ^ 2 / sigma a (x rIdx) (x thetaIdx)) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, tIdx, rIdx, thetaIdx, phiIdx, gtPhiField]

theorem metric_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M a) x phiIdx phiIdx =
      (((x rIdx) ^ 2 + a ^ 2) ^ 2 - a ^ 2 * delta M a (x rIdx) * (Real.sin (x thetaIdx)) ^ 2)
        * (Real.sin (x thetaIdx)) ^ 2 / sigma a (x rIdx) (x thetaIdx) := by
  unfold CoordinateMetricData.value kerrMetricData
  simp [offDiagTPhi, kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx, gPhiPhiField]

end MetricComponentChecks

section HorizonChecks

@[simp] theorem outerHorizon_def (M a : ℝ) :
    outerHorizon M a = M + Real.sqrt (M ^ 2 - a ^ 2) := rfl

@[simp] theorem innerHorizon_def (M a : ℝ) :
    innerHorizon M a = M - Real.sqrt (M ^ 2 - a ^ 2) := rfl

theorem delta_outerHorizon_eq_zero (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    delta M a (outerHorizon M a) = 0 := by
  unfold delta outerHorizon
  have hs : (Real.sqrt (M ^ 2 - a ^ 2)) ^ 2 = M ^ 2 - a ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt hdisc
  nlinarith [hs]

theorem delta_innerHorizon_eq_zero (M a : ℝ) (hdisc : 0 ≤ M ^ 2 - a ^ 2) :
    delta M a (innerHorizon M a) = 0 := by
  unfold delta innerHorizon
  have hs : (Real.sqrt (M ^ 2 - a ^ 2)) ^ 2 = M ^ 2 - a ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt hdisc
  nlinarith [hs]

end HorizonChecks

section ReductionToSchwarzschild

theorem gtt_reduces_to_schwarzschild (M : ℝ) (x : CoordinateSpace 4)
    (hr : x rIdx ≠ 0) :
    gttField M 0 x = Schwarzschild.gttField M x := by
  have hrEq : x Schwarzschild.rIdx = x rIdx := rfl
  have hrSch : x Schwarzschild.rIdx ≠ 0 := by simpa [hrEq] using hr
  simp [gttField, Schwarzschild.gttField, Schwarzschild.lapse, sigma, hrEq, pow_two]
  field_simp [hr, hrSch]

theorem gThetaTheta_reduces_to_schwarzschild (x : CoordinateSpace 4) :
    gThetaThetaField 0 x = Schwarzschild.gThetaThetaField x := by
  simp [gThetaThetaField, sigma, Schwarzschild.gThetaThetaField]

theorem gPhiPhi_reduces_to_schwarzschild (M : ℝ) (x : CoordinateSpace 4)
    (hr : x rIdx ≠ 0) :
    gPhiPhiField M 0 x = Schwarzschild.gPhiPhiField x := by
  have hrEq : x Schwarzschild.rIdx = x rIdx := rfl
  have hthetaEq : x Schwarzschild.thetaIdx = x thetaIdx := rfl
  have hrSch : x Schwarzschild.rIdx ≠ 0 := by simpa [hrEq] using hr
  simp [gPhiPhiField, sigma, delta, Schwarzschild.gPhiPhiField, hrEq, hthetaEq]
  field_simp [hr, hrSch]

theorem gtPhi_zero_at_zero_spin (M : ℝ) (x : CoordinateSpace 4) :
    gtPhiField M 0 x = 0 := by
  simp [gtPhiField, sigma]

#check kerrIsVacuum

end ReductionToSchwarzschild

end Kerr
end KerrFormalization
