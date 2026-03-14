import KerrFormalization.LocalCoordinates.Curvature

namespace KerrFormalization
namespace LocalCoordinates

def IsVacuumMetric {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) : Prop :=
  ∀ x μ ν, metricRicciComponents g ginv x μ ν = 0

def IsVacuumMetricData {n : ℕ} (g : CoordinateMetricData n) (ginv : InverseMetricData n) : Prop :=
  ∀ x μ ν, ricciComponentsFromMetricData g ginv x μ ν = 0

end LocalCoordinates
end KerrFormalization
