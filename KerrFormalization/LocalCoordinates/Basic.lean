import Mathlib.Data.Real.Basic

namespace KerrFormalization
namespace LocalCoordinates

abbrev CoordinateSpace (n : ℕ) := Fin n → ℝ

abbrev CoordinateDomain (n : ℕ) := Set (CoordinateSpace n)

abbrev CoordinateMetric (n : ℕ) := CoordinateSpace n → Fin n → Fin n → ℝ

abbrev InverseMetric (n : ℕ) := CoordinateSpace n → Fin n → Fin n → ℝ

end LocalCoordinates
end KerrFormalization
