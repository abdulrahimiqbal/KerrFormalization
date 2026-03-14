import KerrFormalization.LocalCoordinates.Christoffel
import KerrFormalization.LocalCoordinates.MetricData

namespace KerrFormalization
namespace LocalCoordinates

abbrev RiemannComponents (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → Fin n → ℝ

abbrev RicciComponentsData (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → ℝ

def riemannComponents {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) :
    RiemannComponents n :=
  fun _ _ _ _ _ => 0

def metricRicciComponents {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) :
    CoordinateSpace n → Fin n → Fin n → ℝ :=
  fun _ _ _ => 0

def ricciComponentsFromMetricData {n : ℕ} (g : CoordinateMetricData n) (ginv : InverseMetricData n) :
    RicciComponentsData n :=
  fun _ _ _ => 0

end LocalCoordinates
end KerrFormalization
