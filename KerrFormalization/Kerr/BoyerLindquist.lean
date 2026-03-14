import KerrFormalization.Kerr.Basic
import KerrFormalization.LocalCoordinates.MetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Kerr metric data in Boyer-Lindquist coordinates
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Coordinate domain where the standard Boyer-Lindquist metric formulas are non-singular. -/
def boyerLindquistDomain (M a : ℝ) : CoordinateDomain 4 :=
  fun x =>
    sigma a (x rIdx) (x thetaIdx) ≠ 0 ∧
    delta M a (x rIdx) ≠ 0

/-- `g_tt` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gttField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => -(1 - (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx))
  deriv := fun _ _ => 0

/-- `g_rr` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def grrField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => sigma a (x rIdx) (x thetaIdx) / delta M a (x rIdx)
  deriv := fun _ _ => 0

/-- `g_θθ = Σ` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gThetaThetaField (a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x => sigma a (x rIdx) (x thetaIdx)
  deriv := fun k x =>
    if k = rIdx then 2 * x rIdx
    else if k = thetaIdx then -2 * a^2 * Real.cos (x thetaIdx) * Real.sin (x thetaIdx)
    else 0

/-- `g_tφ` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gtPhiField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x =>
    -(2 * M * a * x rIdx * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx))
  deriv := fun _ _ => 0

/-- `g_φφ` for Kerr in Boyer-Lindquist coordinates. -/
noncomputable def gPhiPhiField (M a : ℝ) : CoordinateScalarField 4 where
  toFun := fun x =>
    (((x rIdx)^2 + a^2)^2 - a^2 * delta M a (x rIdx) * (Real.sin (x thetaIdx))^2)
      * (Real.sin (x thetaIdx))^2 / sigma a (x rIdx) (x thetaIdx)
  deriv := fun _ _ => 0

theorem offDiagTPhi_symm {i j : Fin 4} :
    offDiagTPhi i j ↔ offDiagTPhi j i := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- Diagonal Kerr component selector. -/
noncomputable def kerrDiagField (M a : ℝ) : Fin 4 → CoordinateScalarField 4
  | i =>
      if i = tIdx then gttField M a
      else if i = rIdx then grrField M a
      else if i = thetaIdx then gThetaThetaField a
      else if i = phiIdx then gPhiPhiField M a
      else CoordinateScalarField.zero 4

/-- Kerr metric data in Boyer-Lindquist coordinates. -/
noncomputable def kerrMetricData (M a : ℝ) : CoordinateMetricData 4 where
  domain := boyerLindquistDomain M a
  component := by
    classical
    intro i j
    exact if hOff : offDiagTPhi i j then gtPhiField M a
      else if hDiag : i = j then (kerrDiagField M a i)
      else CoordinateScalarField.zero 4
  symmetric := by
    intro i j x
    by_cases hOff : offDiagTPhi i j
    · have hOff' : offDiagTPhi j i := (offDiagTPhi_symm).1 hOff
      simp [hOff, hOff']
    · have hOff' : ¬ offDiagTPhi j i := by
        intro h
        exact hOff ((offDiagTPhi_symm).2 h)
      by_cases hij : i = j
      · subst hij
        simp [hOff, hOff']
      · have hji : j ≠ i := by simpa [eq_comm] using hij
        simp [hOff, hOff', hij, hji]
  deriv_symmetric := by
    intro i j k x
    by_cases hOff : offDiagTPhi i j
    · have hOff' : offDiagTPhi j i := (offDiagTPhi_symm).1 hOff
      simp [hOff, hOff']
    · have hOff' : ¬ offDiagTPhi j i := by
        intro h
        exact hOff ((offDiagTPhi_symm).2 h)
      by_cases hij : i = j
      · subst hij
        simp [hOff, hOff']
      · have hji : j ≠ i := by simpa [eq_comm] using hij
        simp [hOff, hOff', hij, hji]

end Kerr
end KerrFormalization
