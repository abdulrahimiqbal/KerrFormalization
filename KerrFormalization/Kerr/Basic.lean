import KerrFormalization.LocalCoordinates.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Basic Kerr coordinate data

Core parameters, indices, and scalar helper functions for Kerr spacetime in
Boyer-Lindquist coordinates.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Boyer-Lindquist time coordinate index. -/
def tIdx : Fin 4 := ⟨0, by decide⟩
/-- Boyer-Lindquist radial coordinate index. -/
def rIdx : Fin 4 := ⟨1, by decide⟩
/-- Boyer-Lindquist polar coordinate index. -/
def thetaIdx : Fin 4 := ⟨2, by decide⟩
/-- Boyer-Lindquist azimuthal coordinate index. -/
def phiIdx : Fin 4 := ⟨3, by decide⟩

/-- Kerr `Δ = r^2 - 2 M r + a^2`. -/
noncomputable def delta (M a r : ℝ) : ℝ := r^2 - 2 * M * r + a^2

/-- Kerr `Σ = r^2 + a^2 cos(θ)^2`. -/
noncomputable def sigma (a r θ : ℝ) : ℝ := r^2 + a^2 * (Real.cos θ)^2

/-- The unique nonzero off-diagonal Kerr index pair `(t, φ)` (in either order). -/
def offDiagTPhi (i j : Fin 4) : Prop :=
  (i = tIdx ∧ j = phiIdx) ∨ (i = phiIdx ∧ j = tIdx)

end Kerr
end KerrFormalization
