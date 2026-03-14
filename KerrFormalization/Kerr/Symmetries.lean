import KerrFormalization.Kerr.ComponentLemmas

/-!
# Kerr symmetry layer in the coordinate-data model

This file records stationarity/axisymmetry-style facts as coordinate
independence properties of Kerr metric components in Boyer-Lindquist
coordinates.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Replace only the Boyer-Lindquist time coordinate. -/
def withTime (x : CoordinateSpace 4) (t : ℝ) : CoordinateSpace 4 :=
  fun i => if i = tIdx then t else x i

/-- Replace only the Boyer-Lindquist azimuthal coordinate. -/
def withPhi (x : CoordinateSpace 4) (φ : ℝ) : CoordinateSpace 4 :=
  fun i => if i = phiIdx then φ else x i

@[simp] theorem withTime_t (x : CoordinateSpace 4) (t : ℝ) :
    withTime x t tIdx = t := by
  simp [withTime, tIdx]

@[simp] theorem withTime_r (x : CoordinateSpace 4) (t : ℝ) :
    withTime x t rIdx = x rIdx := by
  simp [withTime, tIdx, rIdx]

@[simp] theorem withTime_theta (x : CoordinateSpace 4) (t : ℝ) :
    withTime x t thetaIdx = x thetaIdx := by
  simp [withTime, tIdx, thetaIdx]

@[simp] theorem withTime_phi (x : CoordinateSpace 4) (t : ℝ) :
    withTime x t phiIdx = x phiIdx := by
  simp [withTime, tIdx, phiIdx]

@[simp] theorem withPhi_phi (x : CoordinateSpace 4) (φ : ℝ) :
    withPhi x φ phiIdx = φ := by
  simp [withPhi, phiIdx]

@[simp] theorem withPhi_t (x : CoordinateSpace 4) (φ : ℝ) :
    withPhi x φ tIdx = x tIdx := by
  simp [withPhi, tIdx, phiIdx]

@[simp] theorem withPhi_r (x : CoordinateSpace 4) (φ : ℝ) :
    withPhi x φ rIdx = x rIdx := by
  simp [withPhi, rIdx, phiIdx]

@[simp] theorem withPhi_theta (x : CoordinateSpace 4) (φ : ℝ) :
    withPhi x φ thetaIdx = x thetaIdx := by
  simp [withPhi, thetaIdx, phiIdx]

/-- Kerr metric components are unchanged under time-coordinate shifts. -/
theorem metric_value_withTime (M a : ℝ) (x : CoordinateSpace 4) (t : ℝ)
    (i j : Fin 4) :
    CoordinateMetricData.value (kerrMetricData M a) (withTime x t) i j =
      CoordinateMetricData.value (kerrMetricData M a) x i j := by
  fin_cases i <;> fin_cases j <;>
    simp [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, kerrDiagField,
      withTime, gttField, grrField, gThetaThetaField, gtPhiField, gPhiPhiField,
      sigma, delta, tIdx, rIdx, thetaIdx, phiIdx]

/-- Kerr metric components are unchanged under azimuthal-coordinate shifts. -/
theorem metric_value_withPhi (M a : ℝ) (x : CoordinateSpace 4) (φ : ℝ)
    (i j : Fin 4) :
    CoordinateMetricData.value (kerrMetricData M a) (withPhi x φ) i j =
      CoordinateMetricData.value (kerrMetricData M a) x i j := by
  fin_cases i <;> fin_cases j <;>
    simp [CoordinateMetricData.value, kerrMetricData, offDiagTPhi, kerrDiagField,
      withPhi, gttField, grrField, gThetaThetaField, gtPhiField, gPhiPhiField,
      sigma, delta, tIdx, rIdx, thetaIdx, phiIdx]

/-- Coordinate-data stationarity: every Kerr component has zero supplied `∂/∂t`. -/
def StationarySymmetry (M a : ℝ) : Prop :=
  ∀ x i j, CoordinateMetricData.partialValue (kerrMetricData M a) tIdx x i j = 0

/-- Coordinate-data axisymmetry: every Kerr component has zero supplied `∂/∂φ`. -/
def AxialSymmetry (M a : ℝ) : Prop :=
  ∀ x i j, CoordinateMetricData.partialValue (kerrMetricData M a) phiIdx x i j = 0

/-- Kerr is stationary in the current coordinate-data framework. -/
theorem kerr_stationary (M a : ℝ) : StationarySymmetry M a := by
  intro x i j
  fin_cases i <;> fin_cases j <;>
    simp [CoordinateMetricData.partialValue, kerrMetricData, offDiagTPhi, kerrDiagField,
      gttField, grrField, gThetaThetaField, gtPhiField, gPhiPhiField,
      tIdx, rIdx, thetaIdx, phiIdx]

/-- Kerr is axisymmetric in the current coordinate-data framework. -/
theorem kerr_axisymmetric (M a : ℝ) : AxialSymmetry M a := by
  intro x i j
  fin_cases i <;> fin_cases j <;>
    simp [CoordinateMetricData.partialValue, kerrMetricData, offDiagTPhi, kerrDiagField,
      gttField, grrField, gThetaThetaField, gtPhiField, gPhiPhiField,
      tIdx, rIdx, thetaIdx, phiIdx]

end Kerr
end KerrFormalization
