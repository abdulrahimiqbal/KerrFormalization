import KerrFormalization.LocalCoordinates.ChristoffelData
import KerrFormalization.LocalCoordinates.MetricData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Derivatives of Christoffel symbols from supplied metric data

This file defines `∂_λ Γ^σ_{μν}` using:
* first and second derivatives of metric components, and
* supplied first derivatives of inverse-metric components.
-/

open scoped BigOperators

namespace KerrFormalization
namespace LocalCoordinates

/-- Coordinate derivatives of Christoffel symbols `∂_λ Γ^σ_{μν}`. -/
abbrev ChristoffelDerivativesData (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → Fin n → ℝ

/--
Derivatives of coordinate Christoffel symbols associated to metric-component
data and inverse-metric data-with-derivatives.
-/
noncomputable def christoffelDerivFromMetricData {n : ℕ} (g : CoordinateMetricData n)
    (ginv : InverseMetricDataWithDeriv n) : ChristoffelDerivativesData n :=
  fun x l σ μ ν =>
    (1 / 2 : ℝ) *
      Finset.univ.sum (fun ρ : Fin n =>
        ginv.deriv l x σ ρ *
          (g.partialValue μ x ν ρ
            + g.partialValue ν x μ ρ
            - g.partialValue ρ x μ ν)
        + ginv.value x σ ρ *
          (g.partial2Value l μ x ν ρ
            + g.partial2Value l ν x μ ρ
            - g.partial2Value l ρ x μ ν))

end LocalCoordinates
end KerrFormalization
