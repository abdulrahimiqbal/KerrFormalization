import KerrFormalization.PseudoRiemannian
import KerrFormalization.LocalCoordinates
import KerrFormalization.Warmup
import KerrFormalization.Schwarzschild
import KerrFormalization.Kerr
import KerrFormalization.Overview

/-!
# Smoke checks

Minimal `#check` coverage for the public v1 surface.
These checks are presentation-oriented and avoid brittle computation tests.
-/

namespace KerrFormalization

open LocalCoordinates

#check PseudoRiemannian.BilinearMetric
#check LocalCoordinates.CoordinateMetricData
#check Warmup.minkowskiMetricData

end KerrFormalization
