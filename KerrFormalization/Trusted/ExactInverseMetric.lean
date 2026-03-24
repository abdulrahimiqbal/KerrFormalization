import KerrFormalization.Trusted.ExactMetricData
import KerrFormalization.LocalCoordinates.MetricData

namespace KerrFormalization
namespace Trusted

open LocalCoordinates

/-- An exact inverse-metric component table. -/
abbrev ExactInverseComponent (n : ℕ) := ExactMetricComponent n

/-- Convert exact inverse components into the legacy inverse-metric container. -/
noncomputable def toInverseMetricDataWithDeriv {n : ℕ} (component : ExactInverseComponent n) :
    InverseMetricDataWithDeriv n where
  value := fun x i j => component i j x
  deriv := fun k x i j => (component i j).deriv k x

end Trusted
end KerrFormalization
