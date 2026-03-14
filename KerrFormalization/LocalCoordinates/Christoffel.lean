import KerrFormalization.LocalCoordinates.InverseMetric

namespace KerrFormalization
namespace LocalCoordinates

abbrev ChristoffelSymbols (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → ℝ

def christoffelSymbols {n : ℕ} (g : CoordinateMetric n) (ginv : InverseMetric n) :
    ChristoffelSymbols n :=
  fun _ _ _ _ => 0

end LocalCoordinates
end KerrFormalization
