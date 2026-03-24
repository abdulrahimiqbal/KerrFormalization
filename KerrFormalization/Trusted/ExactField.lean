import KerrFormalization.Trusted.ScalarExprDeriv
import KerrFormalization.LocalCoordinates.Fields

namespace KerrFormalization
namespace Trusted

open LocalCoordinates

/-- An exact scalar field whose derivatives are generated from an expression AST. -/
structure ExactField (n : ℕ) where
  expr : ScalarExpr n

namespace ExactField

noncomputable instance {n : ℕ} : CoeFun (ExactField n) (fun _ => CoordinateSpace n → ℝ) where
  coe f := ScalarExpr.eval f.expr

/-- Evaluate the exact field. -/
noncomputable def toFun {n : ℕ} (f : ExactField n) : CoordinateSpace n → ℝ :=
  ScalarExpr.eval f.expr

/-- Generated first derivative. -/
noncomputable def deriv {n : ℕ} (f : ExactField n) : Fin n → CoordinateSpace n → ℝ :=
  ScalarExpr.deriv f.expr

/-- Generated second derivative. -/
noncomputable def deriv2 {n : ℕ} (f : ExactField n) : Fin n → Fin n → CoordinateSpace n → ℝ :=
  ScalarExpr.deriv2 f.expr

/-- Convert an exact field into the legacy coordinate-scalar-field container. -/
noncomputable def toCoordinateScalarField {n : ℕ} (f : ExactField n) : CoordinateScalarField n where
  toFun := toFun f
  deriv := deriv f
  deriv2 := deriv2 f

/-- Build an exact field from an expression AST. -/
def fromExpr {n : ℕ} (e : ScalarExpr n) : ExactField n := ⟨e⟩

/-- The constant exact field. -/
def const {n : ℕ} (c : ℝ) : ExactField n := fromExpr (.const c)

/-- The coordinate exact field. -/
def coord {n : ℕ} (i : Fin n) : ExactField n := fromExpr (.coord i)

end ExactField

end Trusted
end KerrFormalization
