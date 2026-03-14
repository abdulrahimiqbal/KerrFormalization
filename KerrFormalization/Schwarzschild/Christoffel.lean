import KerrFormalization.Schwarzschild.InverseMetric
import KerrFormalization.LocalCoordinates.ChristoffelData

/-!
# Schwarzschild Christoffel symbols from coordinate data

This file exposes the Christoffel-symbol layer built from Schwarzschild metric
component data and the explicit inverse metric components.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Schwarzschild Christoffel symbols in Schwarzschild coordinates. -/
noncomputable def schwarzschildChristoffel (M : ℝ) : ChristoffelSymbolsData 4 :=
  christoffelFromMetricData (schwarzschildMetricData M) (schwarzschildInverseMetric M)

end Schwarzschild
end KerrFormalization
