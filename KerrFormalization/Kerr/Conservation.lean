import KerrFormalization.Kerr.KillingTensor
import KerrFormalization.Kerr.Geodesic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Kerr conservation laws

Energy, angular momentum, and Carter constant conservation along
Kerr geodesics. These are the theorem stubs for Aristotle submission.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Energy: E = -g_tμ v^μ -/
noncomputable def energy (M a : ℝ) (γ : KerrGeodesicData M a) (s : ℝ) : ℝ :=
  -(Finset.univ.sum (fun μ : Fin 4 =>
    CoordinateMetricData.value (kerrMetricData M a) (γ.pos s) tIdx μ * γ.vel s μ))

/-- Angular momentum: L = g_φμ v^μ -/
noncomputable def angMomentum (M a : ℝ) (γ : KerrGeodesicData M a) (s : ℝ) : ℝ :=
  Finset.univ.sum (fun μ : Fin 4 =>
    CoordinateMetricData.value (kerrMetricData M a) (γ.pos s) phiIdx μ * γ.vel s μ)

/-- Carter constant: Q = K_μν v^μ v^ν -/
noncomputable def carterConstant (M a : ℝ) (γ : KerrGeodesicData M a) (s : ℝ) : ℝ :=
  Finset.univ.sum (fun μ : Fin 4 =>
    Finset.univ.sum (fun ν : Fin 4 =>
      killingTensorFormC M a (γ.pos s) μ ν * γ.vel s μ * γ.vel s ν))

/-- Energy is conserved along Kerr geodesics.

    Proof sketch: dE/dλ = -∂_α(g_tμ) v^α v^μ - g_tμ a^μ
    Use geodesic equation to substitute a^μ, then stationarity
    (∂_t g_μν = 0) gives the Killing equation for ∂_t. -/
theorem energy_conserved (M a : ℝ) (γ : KerrGeodesicData M a) :
    ∀ s, energy M a γ s = energy M a γ 0 := by
  sorry

/-- Angular momentum is conserved along Kerr geodesics.

    Identical proof structure to energy_conserved under tIdx ↔ phiIdx,
    using axisymmetry (∂_φ g_μν = 0). -/
theorem angMomentum_conserved (M a : ℝ) (γ : KerrGeodesicData M a) :
    ∀ s, angMomentum M a γ s = angMomentum M a γ 0 := by
  sorry

/-- Carter constant is conserved along Kerr geodesics.

    Proof chain:
    dQ/dλ = (∂_α K_μν) v^α v^μ v^ν + 2 K_μν a^μ v^ν
          = (∂_α K_μν) v^α v^μ v^ν - 2 K_μν Γ^μ_αβ v^α v^β v^ν
          = (∇_α K_μν) v^α v^μ v^ν
          = (1/3)(∇_α K_μν + ∇_μ K_να + ∇_ν K_αμ) v^α v^μ v^ν
          = 0  [by symmetrized Killing equation]

    This does NOT require a circular conservation axiom. -/
theorem carter_conserved (M a : ℝ) (γ : KerrGeodesicData M a) :
    ∀ s, carterConstant M a γ s = carterConstant M a γ 0 := by
  sorry

/-- The four Kerr conservation laws together. -/
theorem kerr_conservation_laws (M a : ℝ) (γ : KerrGeodesicData M a) :
    (∀ s, energy M a γ s = energy M a γ 0) ∧
    (∀ s, angMomentum M a γ s = angMomentum M a γ 0) ∧
    (∀ s, carterConstant M a γ s = carterConstant M a γ 0) := by
  exact ⟨energy_conserved M a γ, angMomentum_conserved M a γ, carter_conserved M a γ⟩

end Kerr
end KerrFormalization
