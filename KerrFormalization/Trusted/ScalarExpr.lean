import KerrFormalization.LocalCoordinates.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace KerrFormalization
namespace Trusted

open LocalCoordinates

/-- A small expression AST for exact scalar formulas in coordinate space. -/
inductive ScalarExpr (n : ℕ) where
  | const : ℝ → ScalarExpr n
  | coord : Fin n → ScalarExpr n
  | add : ScalarExpr n → ScalarExpr n → ScalarExpr n
  | sub : ScalarExpr n → ScalarExpr n → ScalarExpr n
  | mul : ScalarExpr n → ScalarExpr n → ScalarExpr n
  | div : ScalarExpr n → ScalarExpr n → ScalarExpr n
  | pow : ScalarExpr n → Nat → ScalarExpr n
  | sin : ScalarExpr n → ScalarExpr n
  | cos : ScalarExpr n → ScalarExpr n

namespace ScalarExpr

/-- Evaluate an exact scalar expression. -/
noncomputable def eval {n : ℕ} : ScalarExpr n → CoordinateSpace n → ℝ
  | const c, _ => c
  | coord i, x => x i
  | add a b, x => eval a x + eval b x
  | sub a b, x => eval a x - eval b x
  | mul a b, x => eval a x * eval b x
  | div a b, x => eval a x / eval b x
  | pow e 0, _ => 1
  | pow e (Nat.succ n), x => eval (pow e n) x * eval e x
  | sin e, x => Real.sin (eval e x)
  | cos e, x => Real.cos (eval e x)

end ScalarExpr

end Trusted
end KerrFormalization
