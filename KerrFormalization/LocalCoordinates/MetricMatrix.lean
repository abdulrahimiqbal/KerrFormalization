import KerrFormalization.LocalCoordinates.Basic

namespace KerrFormalization
namespace LocalCoordinates

abbrev MetricMatrix (n : ℕ) := Fin n → Fin n → ℝ

def metricAt {n : ℕ} (g : CoordinateMetric n) (x : CoordinateSpace n) : MetricMatrix n :=
  fun i j => g x i j

end LocalCoordinates
end KerrFormalization
