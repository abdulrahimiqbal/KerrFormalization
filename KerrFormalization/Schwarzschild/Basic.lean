import KerrFormalization.LocalCoordinates.Fields
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Basic Schwarzschild coordinate data

This file fixes the coordinate conventions and auxiliary scalar functions used in
Schwarzschild coordinates.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Schwarzschild time coordinate index. -/
def tIdx : Fin 4 := ⟨0, by decide⟩
/-- Schwarzschild radial coordinate index. -/
def rIdx : Fin 4 := ⟨1, by decide⟩
/-- Schwarzschild polar angle index. -/
def thetaIdx : Fin 4 := ⟨2, by decide⟩
/-- Schwarzschild azimuthal angle index. -/
def phiIdx : Fin 4 := ⟨3, by decide⟩

/-- The Schwarzschild lapse factor `1 - 2M/r`. -/
noncomputable def lapse (M r : ℝ) : ℝ := 1 - (2 * M) / r

/-- The Schwarzschild exterior domain `r > 2M`. -/
def exteriorDomain (M : ℝ) : CoordinateDomain 4 :=
  fun x => 2 * M < x rIdx

/-- The radial coordinate field. -/
def rField : CoordinateScalarField 4 := CoordinateScalarField.coord rIdx

/-- The polar angle field. -/
def thetaField : CoordinateScalarField 4 := CoordinateScalarField.coord thetaIdx

#check lapse
#check exteriorDomain
#check rField
#check thetaField

end Schwarzschild
end KerrFormalization
