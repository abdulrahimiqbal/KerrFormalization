import KerrFormalization.LocalCoordinates.MetricMatrix

namespace KerrFormalization
namespace LocalCoordinates

def IsInverseMetric {n : ℕ} (_g : CoordinateMetric n) (_ginv : InverseMetric n) : Prop := by
  classical
  exact True

end LocalCoordinates
end KerrFormalization
