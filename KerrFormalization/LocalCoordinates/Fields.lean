import KerrFormalization.LocalCoordinates.Basic
import Mathlib.Data.Real.Basic

/-!
# Coordinate scalar fields with supplied partial derivatives

This file is the legacy compatibility container for scalar-valued fields with
supplied partial derivatives.

Phase I trusted code should prefer the exact-expression kernel under
`KerrFormalization.Trusted` instead of constructing fields directly with
free-form derivative payloads.

This avoids depending on a fragile analysis API while still letting later files
write mathematically meaningful Christoffel-symbol formulas.
-/

namespace KerrFormalization
namespace LocalCoordinates

/--
A scalar field on coordinate space together with supplied first partial
coordinate derivatives.
-/
structure CoordinateScalarField (n : ℕ) where
  /-- The scalar-valued function. -/
  toFun : CoordinateSpace n → ℝ
  /-- The supplied first partial derivatives. -/
  deriv : Fin n → CoordinateSpace n → ℝ
  /-- The supplied second partial derivatives. -/
  deriv2 : Fin n → Fin n → CoordinateSpace n → ℝ

namespace CoordinateScalarField

instance {n : ℕ} : CoeFun (CoordinateScalarField n) (fun _ => CoordinateSpace n → ℝ) where
  coe f := f.toFun

/-- The zero scalar field. -/
def zero (n : ℕ) : CoordinateScalarField n where
  toFun := fun _ => 0
  deriv := fun _ _ => 0
  deriv2 := fun _ _ _ => 0

/-- A constant scalar field. -/
def const {n : ℕ} (c : ℝ) : CoordinateScalarField n where
  toFun := fun _ => c
  deriv := fun _ _ => 0
  deriv2 := fun _ _ _ => 0

/-- The coordinate projection field `x ↦ x i`. -/
def coord {n : ℕ} (i : Fin n) : CoordinateScalarField n where
  toFun := fun x => x i
  deriv := fun j _ => if j = i then 1 else 0
  deriv2 := fun _ _ _ => 0

@[simp] theorem zero_apply {n : ℕ} (x : CoordinateSpace n) : zero n x = 0 := rfl
@[simp] theorem zero_deriv {n : ℕ} (i : Fin n) (x : CoordinateSpace n) :
    (zero n).deriv i x = 0 := rfl
@[simp] theorem zero_deriv2 {n : ℕ} (i j : Fin n) (x : CoordinateSpace n) :
    (zero n).deriv2 i j x = 0 := rfl

@[simp] theorem const_apply {n : ℕ} (c : ℝ) (x : CoordinateSpace n) :
    const c x = c := rfl
@[simp] theorem const_deriv {n : ℕ} (c : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    (const c).deriv i x = 0 := rfl
@[simp] theorem const_deriv2 {n : ℕ} (c : ℝ) (i j : Fin n) (x : CoordinateSpace n) :
    (const c).deriv2 i j x = 0 := rfl

@[simp] theorem coord_apply {n : ℕ} (i : Fin n) (x : CoordinateSpace n) :
    coord i x = x i := rfl
@[simp] theorem coord_deriv {n : ℕ} (i j : Fin n) (x : CoordinateSpace n) :
    (coord i).deriv j x = if j = i then 1 else 0 := rfl
@[simp] theorem coord_deriv2 {n : ℕ} (i j k : Fin n) (x : CoordinateSpace n) :
    (coord i).deriv2 j k x = 0 := rfl

#check CoordinateScalarField
#check CoordinateScalarField.const
#check CoordinateScalarField.coord

end CoordinateScalarField

end LocalCoordinates
end KerrFormalization
