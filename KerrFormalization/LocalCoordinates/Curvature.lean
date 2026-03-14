import KerrFormalization.LocalCoordinates.Christoffel

namespace KerrFormalization
namespace LocalCoordinates

abbrev RiemannComponents (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → Fin n → ℝ

def riemannComponents {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) :
    RiemannComponents n :=
  fun _ _ _ _ _ => 0

def metricRicciComponents {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) :
    CoordinateSpace n → Fin n → Fin n → ℝ :=
  fun _ _ _ => 0

end LocalCoordinates
end KerrFormalization
