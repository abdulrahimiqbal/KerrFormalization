import KerrFormalization.Trusted.ScalarExpr

namespace KerrFormalization
namespace Trusted

open LocalCoordinates

namespace ScalarExpr

/-- First coordinate derivative of an exact scalar expression. -/
noncomputable def deriv {n : ℕ} : ScalarExpr n → Fin n → CoordinateSpace n → ℝ
  | const _, _ => fun _ => 0
  | coord i, k => fun x => if k = i then 1 else 0
  | add a b, k => fun x => deriv a k x + deriv b k x
  | sub a b, k => fun x => deriv a k x - deriv b k x
  | mul a b, k => fun x => deriv a k x * eval b x + eval a x * deriv b k x
  | div a b, k => fun x =>
      (deriv a k x * eval b x - eval a x * deriv b k x) / (eval b x)^2
  | pow _ 0, _ => fun _ => 0
  | pow e (Nat.succ n), k => fun x =>
      deriv (pow e n) k x * eval e x + eval (pow e n) x * deriv e k x
  | sin e, k => fun x => Real.cos (eval e x) * deriv e k x
  | cos e, k => fun x => -Real.sin (eval e x) * deriv e k x

/-- Second coordinate derivative of an exact scalar expression. -/
noncomputable def deriv2 {n : ℕ} : ScalarExpr n → Fin n → Fin n → CoordinateSpace n → ℝ
  | const _, _, _ => fun _ => 0
  | coord _, _, _ => fun _ => 0
  | add a b, k, l => fun x => deriv2 a k l x + deriv2 b k l x
  | sub a b, k, l => fun x => deriv2 a k l x - deriv2 b k l x
  | mul a b, k, l => fun x =>
      deriv2 a k l x * eval b x + deriv a k x * deriv b l x +
        deriv a l x * deriv b k x + eval a x * deriv2 b k l x
  | div a b, k, l => fun x =>
      let u := eval a x
      let v := eval b x
      let uk := deriv a k x
      let ul := deriv a l x
      let vk := deriv b k x
      let vl := deriv b l x
      let ukl := deriv2 a k l x
      let vkl := deriv2 b k l x
      (ukl * v^2 - uk * v * vl - ul * v * vk + u * (2 * vk * vl - v * vkl)) / v^3
  | pow _ 0, _, _ => fun _ => 0
  | pow e (Nat.succ n), k, l => fun x =>
      deriv2 (pow e n) k l x * eval e x +
        deriv (pow e n) k x * deriv e l x +
        deriv (pow e n) l x * deriv e k x +
        eval (pow e n) x * deriv2 e k l x
  | sin e, k, l => fun x =>
      -Real.sin (eval e x) * deriv e k x * deriv e l x +
        Real.cos (eval e x) * deriv2 e k l x
  | cos e, k, l => fun x =>
      -Real.cos (eval e x) * deriv e k x * deriv e l x -
        Real.sin (eval e x) * deriv2 e k l x

end ScalarExpr

end Trusted
end KerrFormalization
