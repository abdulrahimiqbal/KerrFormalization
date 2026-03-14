import KerrFormalization.Kerr.InverseMetric
import KerrFormalization.LocalCoordinates.ChristoffelData

/-!
# Kerr Christoffel symbols from coordinate data

This file exposes the Christoffel-symbol layer built from Kerr metric component
fields and explicit inverse metric components.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Kerr Christoffel symbols in Boyer-Lindquist coordinates. -/
noncomputable def kerrChristoffel (M a : ℝ) : ChristoffelSymbolsData 4 :=
  christoffelFromMetricData (kerrMetricData M a) (kerrInverseMetricData M a)

@[simp] theorem kerrChristoffel_def (M a : ℝ) :
    kerrChristoffel M a =
      christoffelFromMetricData (kerrMetricData M a) (kerrInverseMetricData M a) := rfl

end Kerr
end KerrFormalization
