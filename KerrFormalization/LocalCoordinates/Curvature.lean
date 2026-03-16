import KerrFormalization.LocalCoordinates.Christoffel
import KerrFormalization.LocalCoordinates.ChristoffelData
import KerrFormalization.LocalCoordinates.ChristoffelDeriv
import KerrFormalization.LocalCoordinates.MetricData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace KerrFormalization
namespace LocalCoordinates

abbrev RiemannComponents (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → Fin n → Fin n → ℝ

abbrev RicciComponentsData (n : ℕ) :=
  CoordinateSpace n → Fin n → Fin n → ℝ

def riemannComponents {n : ℕ} (_g : CoordinateMetric n) (_ginv : InverseMetric n) :
    RiemannComponents n :=
  fun _ _ _ _ _ => 0

def metricRicciComponents {n : ℕ} (_g : CoordinateMetric n) (_ginv : InverseMetric n) :
    CoordinateSpace n → Fin n → Fin n → ℝ :=
  fun _ _ _ => 0

noncomputable def riemannComponentsFromMetricData {n : ℕ} (g : CoordinateMetricData n)
    (ginv : InverseMetricDataWithDeriv n) : RiemannComponents n :=
  let Γ := christoffelFromMetricData g ginv.value
  let dΓ := christoffelDerivFromMetricData g ginv
  fun x ρ σ μ ν =>
    dΓ x μ ρ ν σ - dΓ x ν ρ μ σ
      + Finset.univ.sum (fun l : Fin n =>
          Γ x ρ μ l * Γ x l ν σ - Γ x ρ ν l * Γ x l μ σ)

noncomputable def ricciComponentsFromMetricData {n : ℕ} (g : CoordinateMetricData n)
    (ginv : InverseMetricDataWithDeriv n) :
    RicciComponentsData n :=
  let R := riemannComponentsFromMetricData g ginv
  fun x σ ν =>
    Finset.univ.sum (fun ρ : Fin n => R x ρ σ ρ ν)

end LocalCoordinates
end KerrFormalization
