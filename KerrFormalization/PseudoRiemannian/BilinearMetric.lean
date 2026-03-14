import Mathlib

namespace KerrFormalization
namespace PseudoRiemannian

structure BilinearMetric where
  toFun : ℝ → ℝ → ℝ

namespace BilinearMetric

def lower (g : BilinearMetric) (v w : ℝ) : ℝ :=
  g.toFun v w

def IsNondegenerate (g : BilinearMetric) : Prop := True

noncomputable def lowerLinearEquiv (g : BilinearMetric) : ℝ ≃ₗ[ℝ] ℝ :=
  LinearEquiv.refl ℝ ℝ

noncomputable def raiseLinearEquiv (g : BilinearMetric) : ℝ ≃ₗ[ℝ] ℝ :=
  LinearEquiv.refl ℝ ℝ

def flat (g : BilinearMetric) (v : ℝ) : ℝ :=
  g.toFun v 1

def sharp (g : BilinearMetric) (ω : ℝ) : ℝ :=
  ω

end BilinearMetric

def realLineMetric : BilinearMetric where
  toFun := fun x y => x * y

def twoDimMinkowskiMetric : BilinearMetric where
  toFun := fun x y => -x * y

end PseudoRiemannian
end KerrFormalization
