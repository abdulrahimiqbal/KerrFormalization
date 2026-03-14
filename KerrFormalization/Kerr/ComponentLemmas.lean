import KerrFormalization.Kerr.InverseMetric

/-!
# Explicit Kerr component lemmas

This file focuses on concrete formulas for the Kerr component scalar fields and
index helpers used by the Boyer-Lindquist metric/inverse definitions.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

@[simp] theorem delta_def (M a r : ℝ) :
    delta M a r = r^2 - 2 * M * r + a^2 := rfl

@[simp] theorem sigma_def (a r θ : ℝ) :
    sigma a r θ = r^2 + a^2 * (Real.cos θ)^2 := rfl

@[simp] theorem gttField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    gttField M a x = -(1 - (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx)) := rfl

@[simp] theorem grrField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    grrField M a x = sigma a (x rIdx) (x thetaIdx) / delta M a (x rIdx) := rfl

@[simp] theorem gThetaThetaField_apply (a : ℝ) (x : CoordinateSpace 4) :
    gThetaThetaField a x = sigma a (x rIdx) (x thetaIdx) := rfl

@[simp] theorem gtPhiField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    gtPhiField M a x =
      -(2 * M * a * x rIdx * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx)) := rfl

@[simp] theorem gPhiPhiField_apply (M a : ℝ) (x : CoordinateSpace 4) :
    gPhiPhiField M a x =
      (((x rIdx)^2 + a^2)^2 - a^2 * delta M a (x rIdx) * (Real.sin (x thetaIdx))^2)
        * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx) := rfl

@[simp] theorem gThetaThetaField_deriv_r (a : ℝ) (x : CoordinateSpace 4) :
    (gThetaThetaField a).deriv rIdx x = 2 * x rIdx := by
  simp [gThetaThetaField, rIdx, thetaIdx]

@[simp] theorem gThetaThetaField_deriv_theta (a : ℝ) (x : CoordinateSpace 4) :
    (gThetaThetaField a).deriv thetaIdx x =
      -2 * a^2 * Real.cos (x thetaIdx) * Real.sin (x thetaIdx) := by
  simp [gThetaThetaField, rIdx, thetaIdx]

@[simp] theorem offDiagTPhi_tPhi : offDiagTPhi tIdx phiIdx := by
  simp [offDiagTPhi, tIdx, phiIdx]

@[simp] theorem offDiagTPhi_phiT : offDiagTPhi phiIdx tIdx := by
  simp [offDiagTPhi, tIdx, phiIdx]

@[simp] theorem offDiagTPhi_tt_false : ¬ offDiagTPhi tIdx tIdx := by
  simp [offDiagTPhi, tIdx, phiIdx]

@[simp] theorem offDiagTPhi_rr_false : ¬ offDiagTPhi rIdx rIdx := by
  simp [offDiagTPhi, tIdx, rIdx, phiIdx]

@[simp] theorem kerrDiagField_t (M a : ℝ) :
    kerrDiagField M a tIdx = gttField M a := by
  simp [kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrDiagField_r (M a : ℝ) :
    kerrDiagField M a rIdx = grrField M a := by
  simp [kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrDiagField_theta (M a : ℝ) :
    kerrDiagField M a thetaIdx = gThetaThetaField a := by
  simp [kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx]

@[simp] theorem kerrDiagField_phi (M a : ℝ) :
    kerrDiagField M a phiIdx = gPhiPhiField M a := by
  simp [kerrDiagField, tIdx, rIdx, thetaIdx, phiIdx]

end Kerr
end KerrFormalization
