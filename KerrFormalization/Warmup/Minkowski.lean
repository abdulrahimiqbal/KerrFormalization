import KerrFormalization.LocalCoordinates.ChristoffelData

/-!
# Minkowski space in coordinates

This file provides a first serious metric example in the upgraded coordinate-data
layer: the standard Minkowski metric in four coordinates.
-/

namespace KerrFormalization
namespace Warmup

open LocalCoordinates

/-- Time coordinate index. -/
def tIdx : Fin 4 := ⟨0, by decide⟩
/-- First spatial coordinate index. -/
def xIdx : Fin 4 := ⟨1, by decide⟩
/-- Second spatial coordinate index. -/
def yIdx : Fin 4 := ⟨2, by decide⟩
/-- Third spatial coordinate index. -/
def zIdx : Fin 4 := ⟨3, by decide⟩

/-- Diagonal entries of the Minkowski metric in `(-,+,+,+)` convention. -/
def minkowskiDiag : Fin 4 → CoordinateScalarField 4
  | ⟨0, _⟩ => CoordinateScalarField.const (-1)
  | ⟨1, _⟩ => CoordinateScalarField.const 1
  | ⟨2, _⟩ => CoordinateScalarField.const 1
  | ⟨3, _⟩ => CoordinateScalarField.const 1

/-- Minkowski metric data on all of `ℝ^4`. -/
def minkowskiMetricData : CoordinateMetricData 4 :=
  CoordinateMetricData.diagonal Set.univ minkowskiDiag

/-- Inverse Minkowski metric, equal to the metric itself in these coordinates. -/
def minkowskiInverseMetric : InverseMetricData 4 :=
  fun x i j => CoordinateMetricData.value minkowskiMetricData x i j

example (x : CoordinateSpace 4) :
    CoordinateMetricData.value minkowskiMetricData x tIdx tIdx = -1 := by
  simp [minkowskiMetricData, CoordinateMetricData.value, CoordinateMetricData.diagonal,
    minkowskiDiag, tIdx]

example (x : CoordinateSpace 4) :
    CoordinateMetricData.value minkowskiMetricData x xIdx xIdx = 1 := by
  simp [minkowskiMetricData, CoordinateMetricData.value, CoordinateMetricData.diagonal,
    minkowskiDiag, xIdx]

#check minkowskiMetricData
#check minkowskiInverseMetric
#check christoffelFromMetricData

end Warmup
end KerrFormalization
