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
#check LocalCoordinates.IsVacuumMetricData
#check Warmup.minkowskiMetricData

#check Schwarzschild.schwarzschildMetricData
#check Schwarzschild.schwarzschildInverseMetric
#check Schwarzschild.schwarzschildIsVacuum

#check Kerr.delta
#check Kerr.sigma
#check Kerr.kerrMetricData
#check Kerr.kerrInverseMetricData
#check Kerr.outerHorizon
#check Kerr.ergoregion
#check Kerr.kerr_stationary
#check Kerr.kerr_axisymmetric
#check Kerr.kerrIsVacuum
#check Kerr.zeroSpinComponentAgreement

#check Kerr.kerrVacuumValidated
#check Kerr.outerHorizonIsDeltaRoot
#check Kerr.zeroSpinReductionValidated

#check kerrIsVacuum_v1
#check schwarzschildIsVacuum_v1

end KerrFormalization
