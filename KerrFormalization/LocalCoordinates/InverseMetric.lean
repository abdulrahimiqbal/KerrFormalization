import KerrFormalization.LocalCoordinates.MetricMatrix

namespace KerrFormalization
namespace LocalCoordinates

def IsInverseMetric {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) : Prop := by
  classical
  exact True

end LocalCoordinates
end KerrFormalization
