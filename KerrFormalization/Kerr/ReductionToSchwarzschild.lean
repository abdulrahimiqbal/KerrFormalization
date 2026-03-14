import KerrFormalization.Kerr.Sanity

/-!
# Structured zero-spin reduction from Kerr to Schwarzschild

This file packages `a = 0` Kerr-to-Schwarzschild relations into a reusable
reduction layer.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Packaged componentwise agreement facts for `a = 0`. -/
structure ZeroSpinComponentAgreement (M : ℝ) (x : CoordinateSpace 4) : Prop where
  tt : gttField M 0 x = Schwarzschild.gttField M x
  rr : grrField M 0 x = Schwarzschild.grrField M x
  thetaTheta : gThetaThetaField 0 x = Schwarzschild.gThetaThetaField x
  phiPhi : gPhiPhiField M 0 x = Schwarzschild.gPhiPhiField x
  tPhi : gtPhiField M 0 x = 0

/-- At nonzero radius, Kerr `a = 0` agrees with Schwarzschild on key components. -/
theorem zeroSpinComponentAgreement (M : ℝ) (x : CoordinateSpace 4)
    (hr : x rIdx ≠ 0) :
    ZeroSpinComponentAgreement M x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gtt_reduces_to_schwarzschild M x hr
  · have hrEq : x Schwarzschild.rIdx = x rIdx := rfl
    have hrSch : x Schwarzschild.rIdx ≠ 0 := by simpa [hrEq] using hr
    simp [grrField, sigma, delta, Schwarzschild.grrField, Schwarzschild.lapse, hrEq]
    field_simp [hr, hrSch]
  · exact gThetaTheta_reduces_to_schwarzschild x
  · exact gPhiPhi_reduces_to_schwarzschild M x hr
  · exact gtPhi_zero_at_zero_spin M x

/-- `g_{tφ}` vanishes everywhere in the zero-spin limit. -/
theorem zeroSpin_tPhi_metric_value (M : ℝ) (x : CoordinateSpace 4) :
    CoordinateMetricData.value (kerrMetricData M 0) x tIdx phiIdx = 0 := by
  simpa [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, tIdx, phiIdx] using
    gtPhi_zero_at_zero_spin M x

/-- Componentwise metric-data reduction theorem on the common nonzero-radius domain. -/
theorem zeroSpin_metricValue_agrees_on_principal_components
    (M : ℝ) (x : CoordinateSpace 4) (hr : x rIdx ≠ 0) :
    CoordinateMetricData.value (kerrMetricData M 0) x tIdx tIdx =
      Schwarzschild.gttField M x ∧
    CoordinateMetricData.value (kerrMetricData M 0) x rIdx rIdx =
      Schwarzschild.grrField M x ∧
    CoordinateMetricData.value (kerrMetricData M 0) x thetaIdx thetaIdx =
      Schwarzschild.gThetaThetaField x ∧
    CoordinateMetricData.value (kerrMetricData M 0) x phiIdx phiIdx =
      Schwarzschild.gPhiPhiField x := by
  have hAgree : ZeroSpinComponentAgreement M x := zeroSpinComponentAgreement M x hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      CoordinateMetricData.value (kerrMetricData M 0) x tIdx tIdx = gttField M 0 x := by
        simp [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, kerrDiagField,
          tIdx, rIdx, thetaIdx, phiIdx]
      _ = Schwarzschild.gttField M x := hAgree.tt
  · calc
      CoordinateMetricData.value (kerrMetricData M 0) x rIdx rIdx = grrField M 0 x := by
        simp [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, kerrDiagField,
          tIdx, rIdx, thetaIdx, phiIdx]
      _ = Schwarzschild.grrField M x := hAgree.rr
  · calc
      CoordinateMetricData.value (kerrMetricData M 0) x thetaIdx thetaIdx = gThetaThetaField 0 x := by
        simp [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, kerrDiagField,
          tIdx, rIdx, thetaIdx, phiIdx]
      _ = Schwarzschild.gThetaThetaField x := hAgree.thetaTheta
  · calc
      CoordinateMetricData.value (kerrMetricData M 0) x phiIdx phiIdx = gPhiPhiField M 0 x := by
        simp [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, kerrDiagField,
          tIdx, rIdx, thetaIdx, phiIdx]
      _ = Schwarzschild.gPhiPhiField x := hAgree.phiPhi

end Kerr
end KerrFormalization
