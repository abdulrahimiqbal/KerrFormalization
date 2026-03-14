import KerrFormalization.LocalCoordinates.MetricData

/-!
# Reusable lemmas for diagonal coordinate metrics

This file collects basic evaluation lemmas for `CoordinateMetricData.diagonal`.
These are used by explicit spacetime examples such as Schwarzschild.
-/

namespace KerrFormalization
namespace LocalCoordinates

namespace CoordinateMetricData

@[simp] theorem value_diagonal_diag {n : ℕ} (domain : CoordinateDomain n)
    (diag : Fin n → CoordinateScalarField n) (x : CoordinateSpace n) (i : Fin n) :
    value (diagonal domain diag) x i i = diag i x := by
  simp [value, diagonal]

@[simp] theorem value_diagonal_offDiag {n : ℕ} (domain : CoordinateDomain n)
    (diag : Fin n → CoordinateScalarField n) (x : CoordinateSpace n) (i j : Fin n)
    (hij : i ≠ j) :
    value (diagonal domain diag) x i j = 0 := by
  simp [value, diagonal, hij]

@[simp] theorem partialValue_diagonal_diag {n : ℕ} (domain : CoordinateDomain n)
    (diag : Fin n → CoordinateScalarField n) (k : Fin n) (x : CoordinateSpace n) (i : Fin n) :
    partialValue (diagonal domain diag) k x i i = (diag i).deriv k x := by
  simp [partialValue, diagonal]

@[simp] theorem partialValue_diagonal_offDiag {n : ℕ} (domain : CoordinateDomain n)
    (diag : Fin n → CoordinateScalarField n) (k : Fin n) (x : CoordinateSpace n)
    (i j : Fin n) (hij : i ≠ j) :
    partialValue (diagonal domain diag) k x i j = 0 := by
  simp [partialValue, diagonal, hij]

end CoordinateMetricData

end LocalCoordinates
end KerrFormalization
