import KerrFormalization.Kerr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kerr horizon helper definitions
-/

namespace KerrFormalization
namespace Kerr

/-- Outer Kerr horizon radius `r_+ = M + sqrt(M^2 - a^2)`. -/
noncomputable def outerHorizon (M a : ℝ) : ℝ :=
  M + Real.sqrt (M^2 - a^2)

/-- Inner Kerr horizon radius `r_- = M - sqrt(M^2 - a^2)`. -/
noncomputable def innerHorizon (M a : ℝ) : ℝ :=
  M - Real.sqrt (M^2 - a^2)

end Kerr
end KerrFormalization
