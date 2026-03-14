import KerrFormalization.LocalCoordinates.MetricData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Christoffel symbols from supplied first derivative data

This file defines coordinate Christoffel symbols using metric component fields
that carry their first derivatives as data.
-/

open scoped BigOperators

namespace KerrFormalization
namespace LocalCoordinates

/-- Coordinate Christoffel symbols `Γ^σ_{μν}`. -/
abbrev ChristoffelSymbolsData (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → ℝ

/--
Coordinate Christoffel symbols associated to metric-component data and inverse
metric values.
-/
noncomputable def christoffelFromMetricData {n : ℕ} (g : CoordinateMetricData n)
    (ginv : InverseMetricData n) : ChristoffelSymbolsData n :=
  fun x σ μ ν =>
    (1 / 2 : ℝ) *
      Finset.univ.sum (fun ρ : Fin n =>
        ginv x σ ρ *
          (g.partialValue μ x ν ρ
            + g.partialValue ν x μ ρ
            - g.partialValue ρ x μ ν))

#check ChristoffelSymbolsData
#check christoffelFromMetricData

end LocalCoordinates
end KerrFormalization
