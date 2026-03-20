import KerrFormalization.Kerr.Christoffel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Kerr geodesic structure

Geodesic data for curves in Kerr spacetime, using the real
kerrChristoffel symbols (not axioms).
-/

open scoped BigOperators

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- A geodesic in Kerr spacetime with regularity conditions.
    The key design: vel and acc are data fields, with compatibility
    conditions stated as properties. This lets Aristotle work with
    the algebraic structure without needing Mathlib's analysis API. -/
structure KerrGeodesicData (M a : ℝ) where
  /-- Position along curve. -/
  pos : ℝ → CoordinateSpace 4
  /-- Velocity (tangent vector). -/
  vel : ℝ → Fin 4 → ℝ
  /-- Acceleration. -/
  acc : ℝ → Fin 4 → ℝ
  /-- Geodesic equation: acc^σ = -Γ^σ_μν v^μ v^ν -/
  geodesic_eq : ∀ s σ,
    acc s σ = -(Finset.univ.sum (fun μ : Fin 4 =>
      Finset.univ.sum (fun ν : Fin 4 =>
        kerrChristoffel M a (pos s) σ μ ν * vel s μ * vel s ν)))
  /-- Off the ring singularity along the geodesic. -/
  hSigma_along : ∀ s, sigma a ((pos s) rIdx) ((pos s) thetaIdx) ≠ 0
  /-- Off the horizon along the geodesic. -/
  hDelta_along : ∀ s, delta M a ((pos s) rIdx) ≠ 0
  /-- Off the axis along the geodesic. -/
  hSin_along : ∀ s, Real.sin ((pos s) thetaIdx) ≠ 0

end Kerr
end KerrFormalization
