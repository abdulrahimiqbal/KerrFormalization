import KerrFormalization.LocalCoordinates.Curvature

namespace KerrFormalization
namespace LocalCoordinates

def IsVacuumMetric {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) : Prop :=
  ∀ x μ ν, metricRicciComponents g ginv x μ ν = 0

end LocalCoordinates
end KerrFormalization
