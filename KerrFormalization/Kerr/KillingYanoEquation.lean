import KerrFormalization.Kerr.KillingYano
import KerrFormalization.Kerr.Christoffel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Kerr Killing-Yano equation

This file states the Killing-Yano equation for the Kerr 2-form in Boyer-Lindquist
coordinates using the existing Christoffel-symbol infrastructure.
-/

open scoped BigOperators

namespace KerrFormalization
namespace Kerr

open LocalCoordinates
open Trusted

/-- Covariant derivative of the Kerr Killing-Yano 2-form. -/
noncomputable def covDerivKillingYano (M a : ℝ) (x : CoordinateSpace 4)
    (α β γ : Fin 4) : ℝ :=
  (killingYanoComponent M a β γ).deriv α x
  - Finset.univ.sum (fun δ : Fin 4 =>
      kerrChristoffel M a x δ α β * killingYanoComponent M a δ γ x)
  - Finset.univ.sum (fun δ : Fin 4 =>
      kerrChristoffel M a x δ α γ * killingYanoComponent M a β δ x)

-- TODO: Aristotle should discharge the full tensor equation from the explicit KY components.
theorem killingYano_equation (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ α β γ : Fin 4,
      covDerivKillingYano M a x α β γ + covDerivKillingYano M a x β α γ = 0 := by
  -- TODO: finish the explicit `Fin 4` case split after the component lemmas
  -- are proven in a separate file or moved above this theorem.
  sorry

-- TODO: Aristotle can attack the following αβ blocks individually.

lemma killingYano_eq_tt (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x tIdx tIdx γ + covDerivKillingYano M a x tIdx tIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_tr (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x tIdx rIdx γ + covDerivKillingYano M a x rIdx tIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_ttheta (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x tIdx thetaIdx γ +
        covDerivKillingYano M a x thetaIdx tIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_tphi (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x tIdx phiIdx γ + covDerivKillingYano M a x phiIdx tIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_rr (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x rIdx rIdx γ + covDerivKillingYano M a x rIdx rIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_rtheta (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x rIdx thetaIdx γ +
        covDerivKillingYano M a x thetaIdx rIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_rphi (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x rIdx phiIdx γ + covDerivKillingYano M a x phiIdx rIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_thetatheta (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x thetaIdx thetaIdx γ +
        covDerivKillingYano M a x thetaIdx thetaIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_thetaphi (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x thetaIdx phiIdx γ +
        covDerivKillingYano M a x phiIdx thetaIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

lemma killingYano_eq_phiphi (M a : ℝ) (x : CoordinateSpace 4)
    (hSigma : sigma a (x rIdx) (x thetaIdx) ≠ 0)
    (hDelta : delta M a (x rIdx) ≠ 0)
    (hSin : Real.sin (x thetaIdx) ≠ 0) :
    ∀ γ : Fin 4,
      covDerivKillingYano M a x phiIdx phiIdx γ + covDerivKillingYano M a x phiIdx phiIdx γ = 0 := by
  -- TODO: explicit `γ`-case split using the generated Christoffel formulas.
  sorry

end Kerr
end KerrFormalization
