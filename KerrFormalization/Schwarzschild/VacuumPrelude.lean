import KerrFormalization.Schwarzschild.ComponentLemmas

/-!
# Schwarzschild vacuum-prelude layer

This file gathers the first serious Schwarzschild lemmas that will be reused in
later Ricci and vacuum computations.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Bundle of Schwarzschild metric and inverse metric data used in vacuum computations. -/
noncomputable def schwarzschildMetricPair (M : ℝ) :
    CoordinateMetricData 4 × InverseMetricDataWithDeriv 4 :=
  (schwarzschildMetricData M, schwarzschildInverseMetricWithDeriv M)

/-- The Christoffel layer used by later vacuum calculations. -/
noncomputable def schwarzschildVacuumChristoffel (M : ℝ) : ChristoffelSymbolsData 4 :=
  schwarzschildChristoffel M

/-- Re-export a representative nonzero Christoffel component. -/
theorem vacuumPrelude_christoffel_r_tt (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildVacuumChristoffel M x rIdx tIdx tIdx =
      (M / (x rIdx)^2) * lapse M (x rIdx) :=
  christoffel_r_tt M x

/-- Re-export a representative zero Christoffel component. -/
theorem vacuumPrelude_christoffel_t_tt_zero (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildVacuumChristoffel M x tIdx tIdx tIdx = 0 :=
  christoffel_t_tt_zero M x

end Schwarzschild
end KerrFormalization
