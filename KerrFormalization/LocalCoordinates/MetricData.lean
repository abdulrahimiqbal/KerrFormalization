import KerrFormalization.LocalCoordinates.Fields

/-!
# Coordinate metrics with supplied first derivatives

This file packages coordinate metrics as families of scalar fields indexed by
component positions. The component fields carry their own first coordinate
derivatives, which is enough to define meaningful Christoffel-symbol formulas in the
next file.
-/

namespace KerrFormalization
namespace LocalCoordinates

/--
A coordinate metric whose components are scalar fields with supplied first
derivatives.
-/
structure CoordinateMetricData (n : ℕ) where
  /-- Domain of definition. -/
  domain : CoordinateDomain n
  /-- Component fields `g_{ij}`. -/
  component : Fin n → Fin n → CoordinateScalarField n
  /-- Pointwise symmetry of metric components. -/
  symmetric : ∀ i j x, component i j x = component j i x
  /-- Pointwise symmetry of supplied first derivatives. -/
  deriv_symmetric : ∀ i j k x, (component i j).deriv k x = (component j i).deriv k x

/-- Pointwise inverse-metric components in coordinates. -/
abbrev InverseMetricData (n : ℕ) := CoordinateSpace n → Fin n → Fin n → ℝ

namespace CoordinateMetricData

/-- Evaluate the metric components at a point. -/
def value {n : ℕ} (g : CoordinateMetricData n) (x : CoordinateSpace n) (i j : Fin n) : ℝ :=
  g.component i j x

/-- Evaluate a supplied first derivative of a metric component. -/
def partialValue {n : ℕ} (g : CoordinateMetricData n) (k : Fin n) (x : CoordinateSpace n)
    (i j : Fin n) : ℝ :=
  (g.component i j).deriv k x

/-- A diagonal coordinate metric built from diagonal scalar fields. -/
def diagonal {n : ℕ} (domain : CoordinateDomain n) (diag : Fin n → CoordinateScalarField n) :
    CoordinateMetricData n where
  domain := domain
  component := fun i j => if i = j then diag i else CoordinateScalarField.zero n
  symmetric := by
    intro i j x
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      change (if i = j then diag i else CoordinateScalarField.zero n) x =
        (if j = i then diag j else CoordinateScalarField.zero n) x
      simp [hij, hji]
  deriv_symmetric := by
    intro i j k x
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      change ((if i = j then diag i else CoordinateScalarField.zero n).deriv k x) =
        ((if j = i then diag j else CoordinateScalarField.zero n).deriv k x)
      simp [hij, hji]

#check CoordinateMetricData
#check InverseMetricData
#check CoordinateMetricData.diagonal

end CoordinateMetricData

end LocalCoordinates
end KerrFormalization
