import KerrFormalization.Kerr.KillingYanoToKillingTensor
import KerrFormalization.Kerr.Conservation

/-!
# Carter conservation from the Kerr Killing-Yano 2-form

This file makes the non-circular chain explicit:

`Killing-Yano equation -> square gives a Killing tensor -> Carter constant`
conservation along Kerr geodesics.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open scoped BigOperators

-- TODO: Aristotle should use the square identity and the symmetrized Killing tensor
-- equation to derive Carter conservation without assuming it as an axiom.
theorem carter_conserved_from_killingTensorEquation (M a : ℝ)
    (γ : KerrGeodesicData M a)
    (hKT : ∀ x : CoordinateSpace 4, ∀ α μ ν : Fin 4,
      covDerivKillingFormC M a x α μ ν +
      covDerivKillingFormC M a x μ ν α +
      covDerivKillingFormC M a x ν α μ = 0) :
    ∀ s, carterConstant M a γ s = carterConstant M a γ 0 := by
  clear hKT
  -- ATTEMPT: this should be derivable from the standard contraction identity
  -- `dQ/ds = (1/3)(∇_α K_μν + ∇_μ K_να + ∇_ν K_αμ) u^α u^μ u^ν` together with
  -- the geodesic equation in `Kerr/Geodesic.lean`. The current file only has the
  -- target statement, so the contraction proof still needs to be written.
  sorry

-- TODO: Aristotle should feed the Killing-Yano equation into the square-to-Killing
-- tensor theorem and then into Carter conservation.
theorem carter_conserved_from_killingYano (M a : ℝ) (γ : KerrGeodesicData M a)
    (hSquare : ∀ x : CoordinateSpace 4, ∀ μ ν : Fin 4,
      killingTensorFromKillingYano M a x μ ν = killingTensorFormC M a x μ ν)
    (hKY : ∀ x : CoordinateSpace 4, ∀ α β δ : Fin 4,
      covDerivKillingYano M a x α β δ + covDerivKillingYano M a x β α δ = 0) :
    ∀ s, carterConstant M a γ s = carterConstant M a γ 0 := by
  have hKT := killingYano_square_is_killingTensor M a hSquare hKY
  exact carter_conserved_from_killingTensorEquation M a γ hKT

end Kerr
end KerrFormalization
