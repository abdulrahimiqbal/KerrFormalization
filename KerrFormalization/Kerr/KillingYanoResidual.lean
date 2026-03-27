import KerrFormalization.Kerr.KillingYanoEquation
import KerrFormalization.Paper2.Round2ExplicitDefs
import KerrFormalization.Paper2.Q2_CarterDrift
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Killing-Yano residuals for deformed Kerr probes

This file provides a scaffold for comparing the undeformed Kerr Killing-Yano
2-form against the deformed Round 2 Christoffel data.

The intended use is:
- evaluate the standard KY tensor on the round-2 sample point,
- contract it against the deformed Christoffel symbols,
- and extract the symmetrized residual that drives the Carter drift.

The proving work is still upstream in the KY-equation and exact-deformation
pipelines, so the theorem statements remain `sorry` targets for now.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open Trusted
open Paper2

/-- The deformed KY residual, evaluated at the round-2 sample point. -/
noncomputable def kyResidual (M a r θ ε : ℝ) (α β γ : Fin 4) : ℝ :=
  ExactField.deriv (killingYanoComponent M a β γ) α (Paper2.round2Point r θ)
  - Finset.univ.sum (fun δ : Fin 4 =>
      Paper2.christoffelDeformed M a r θ ε δ α β *
        killingYanoComponent M a δ γ (Paper2.round2Point r θ))
  - Finset.univ.sum (fun δ : Fin 4 =>
      Paper2.christoffelDeformed M a r θ ε δ α γ *
        killingYanoComponent M a β δ (Paper2.round2Point r θ))

/-- Symmetrized KY residual in the first two indices. -/
noncomputable def kyResidualSymm (M a r θ ε : ℝ) (α β γ : Fin 4) : ℝ :=
  kyResidual M a r θ ε α β γ + kyResidual M a r θ ε β α γ

/-- The residual vanishes in the undeformed limit. -/
theorem kyResidual_eps_zero (M a r θ : ℝ) :
    ∀ α β γ : Fin 4, kyResidual M a r θ 0 α β γ = 0 := by
  -- TODO: replace the deformed Christoffel symbols by the undeformed Kerr
  -- connection at `ε = 0`, then invoke the main KY equation theorem once the
  -- component proof exists.
  sorry

/-- The residual is generically nonzero away from the undeformed limit. -/
theorem kyResidual_generically_nonzero (M a r θ ε : ℝ)
    (hε : ε ≠ 0) :
    ∃ α β γ : Fin 4, kyResidual M a r θ ε α β γ ≠ 0 := by
  -- TODO: the likely witness is the radial `(r,r,r)` / mixed radial-azimuthal
  -- sector identified in the Round 2 probe files.
  sorry

/-- Carter drift extracted from the symmetrized KY residual and a velocity field. -/
noncomputable def carterDriftFromKYResidual
    (M a r θ ε : ℝ) (u : Fin 4 → ℝ) : ℝ :=
  Finset.univ.sum (fun α : Fin 4 =>
    Finset.univ.sum (fun β : Fin 4 =>
      Finset.univ.sum (fun γ : Fin 4 =>
        kyResidualSymm M a r θ ε α β γ * u α * u β * u γ)))

/-- The drift vanishes in the undeformed limit. -/
theorem carterDriftFromKYResidual_eps_zero
    (M a r θ : ℝ) (u : Fin 4 → ℝ) :
    carterDriftFromKYResidual M a r θ 0 u = 0 := by
  -- TODO: reduce to `kyResidual_eps_zero` by expanding the finite sums.
  sorry

/-- The KY-residual drift agrees with the existing Probe Q2 drift model. -/
theorem carterDriftFromKYResidual_eq_Q2
    (M a r θ ε ur : ℝ) :
    carterDriftFromKYResidual M a r θ ε
        (fun i : Fin 4 => if i = rIdx then ur else 0) =
      Paper2.carterDriftRate M a r θ ε ur := by
  -- TODO: unfold the residual, kill the non-radial velocity slots, and match
  -- the resulting expression to `Paper2.carterDriftRate`.
  sorry

end Kerr
end KerrFormalization
