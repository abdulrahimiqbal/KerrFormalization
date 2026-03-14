import KerrFormalization.PseudoRiemannian
import KerrFormalization.LocalCoordinates
import KerrFormalization.Warmup
import KerrFormalization.Schwarzschild
import KerrFormalization.Kerr

/-!
# Smoke tests

This file provides lightweight checks that the pseudo-Riemannian, local-coordinate,
and first serious spacetime modules can be imported together and that the expected
names are available.
-/

namespace KerrFormalization

open PseudoRiemannian
open LocalCoordinates

#check PseudoRiemannian.BilinearMetric
#check PseudoRiemannian.BilinearMetric.lower
#check PseudoRiemannian.BilinearMetric.IsNondegenerate
#check PseudoRiemannian.BilinearMetric.lowerLinearEquiv
#check PseudoRiemannian.BilinearMetric.raiseLinearEquiv
#check PseudoRiemannian.BilinearMetric.flat
#check PseudoRiemannian.BilinearMetric.sharp
#check PseudoRiemannian.realLineMetric
#check PseudoRiemannian.twoDimMinkowskiMetric

#check LocalCoordinates.CoordinateSpace
#check LocalCoordinates.CoordinateScalarField
#check LocalCoordinates.CoordinateMetricData
#check LocalCoordinates.InverseMetricData
#check LocalCoordinates.christoffelFromMetricData
#check LocalCoordinates.IsVacuumMetric

#check Warmup.minkowskiMetricData
#check Warmup.minkowskiInverseMetric
#check Schwarzschild.lapse
#check Schwarzschild.schwarzschildMetricData
#check Schwarzschild.schwarzschildInverseMetric
#check Schwarzschild.schwarzschildIsVacuum

#check Kerr.delta
#check Kerr.sigma
#check Kerr.kerrMetricData
#check Kerr.kerrInverseMetricData
#check Kerr.outerHorizon

end KerrFormalization
