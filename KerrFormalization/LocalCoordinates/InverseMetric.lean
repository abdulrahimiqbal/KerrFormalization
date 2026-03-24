import KerrFormalization.LocalCoordinates.MetricMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace KerrFormalization
namespace LocalCoordinates

def IsInverseMetric {n : ℕ} (domain : CoordinateDomain n) (g : CoordinateMetric n)
    (ginv : InverseMetric n) : Prop :=
  ∀ x, domain x →
    (∀ i j, Finset.univ.sum (fun k : Fin n => g x i k * ginv x k j) = if i = j then 1 else 0) ∧
    (∀ i j, Finset.univ.sum (fun k : Fin n => ginv x i k * g x k j) = if i = j then 1 else 0)

end LocalCoordinates
end KerrFormalization
