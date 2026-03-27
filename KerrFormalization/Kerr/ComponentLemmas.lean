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
