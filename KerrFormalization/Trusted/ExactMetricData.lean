import KerrFormalization.Trusted.ExactField
import KerrFormalization.LocalCoordinates.MetricData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace KerrFormalization
namespace Trusted

open LocalCoordinates
open scoped BigOperators

/-- An exact metric component table. -/
abbrev ExactMetricComponent (n : ℕ) := Fin n → Fin n → ExactField n

/-- Convert exact metric components into the legacy coordinate metric data container. -/
noncomputable def toCoordinateMetricData {n : ℕ} (domain : CoordinateDomain n)
    (component : ExactMetricComponent n)
    (symmetric : ∀ i j, component i j = component j i) :
    CoordinateMetricData n where
  domain := domain
  component := fun i j => ExactField.toCoordinateScalarField (component i j)
  symmetric := by
    intro i j x
    simpa using congrArg (fun f => f x) (symmetric i j)
  deriv_symmetric := by
    intro i j k x
    simpa using congrArg (fun f => f.deriv k x) (symmetric i j)
  deriv2_symmetric := by
    intro i j k l x
    simpa using congrArg (fun f => f.deriv2 k l x) (symmetric i j)

/-- Exact left inverse relation on a coordinate domain. -/
def componentwiseLeftInverse {n : ℕ} (domain : CoordinateDomain n)
    (g inv : ExactMetricComponent n) : Prop :=
  ∀ x, domain x →
    ∀ i j, Finset.univ.sum (fun k : Fin n => g i k x * inv k j x) = if i = j then 1 else 0

/-- Exact right inverse relation on a coordinate domain. -/
def componentwiseRightInverse {n : ℕ} (domain : CoordinateDomain n)
    (g inv : ExactMetricComponent n) : Prop :=
  ∀ x, domain x →
    ∀ i j, Finset.univ.sum (fun k : Fin n => inv i k x * g k j x) = if i = j then 1 else 0

/-- Exact inverse relation on a coordinate domain. -/
def componentwiseInverse {n : ℕ} (domain : CoordinateDomain n)
    (g inv : ExactMetricComponent n) : Prop :=
  componentwiseLeftInverse domain g inv ∧ componentwiseRightInverse domain g inv

end Trusted
end KerrFormalization
