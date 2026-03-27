import KerrFormalization.Kerr.Christoffel
import KerrFormalization.LocalCoordinates.Curvature

/-!
# Kerr Ricci components

This file packages Ricci components for Kerr in the current coordinate-data
curvature API.

STATUS: incomplete formal Ricci vanishing proof.
All component-vanishing lemmas below are placeholders and are not suitable for
public vacuum claims.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Ricci components associated to Kerr metric/inverse data. -/
noncomputable def kerrRicciComponents (M a : ℝ) : RicciComponentsData 4 :=
  ricciComponentsFromMetricData (kerrMetricData M a) (kerrInverseMetricWithDeriv M a)

lemma ricci_00 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx tIdx = 0 := by
  -- ATTEMPT: unfold `ricciComponentsFromMetricData`, `riemannComponentsFromMetricData`,
  -- and `christoffelDerivFromMetricData`, then simplify the 4x4 Christoffel sums.
  -- The exact metric derivatives are available, but this is still too large for a
  -- direct `simp` pass without additional explicit Christoffel lemmas.
  sorry

lemma ricci_01 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx rIdx = 0 := by
  -- ATTEMPT: the off-diagonal slice should collapse from symmetry/sparsity once
  -- the exact Christoffel formulas are unfolded. A reusable explicit connection
  -- lemma would likely remove most of the noise here.
  sorry

lemma ricci_02 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx thetaIdx = 0 := by
  -- ATTEMPT: same as `ricci_01`; the obstacle is the opaque Christoffel sum,
  -- not the final algebraic identity.
  sorry

lemma ricci_03 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx phiIdx = 0 := by
  -- ATTEMPT: same as `ricci_01`; this should be a pure cancellation lemma once
  -- the explicit connection coefficients are exposed.
  sorry

lemma ricci_10 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx tIdx = 0 := by
  -- ATTEMPT: off-diagonal symmetry should reduce this to `ricci_01`.
  sorry

lemma ricci_11 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx rIdx = 0 := by
  -- ATTEMPT: this is the first genuinely hard diagonal component; it likely
  -- needs an explicit Christoffel normal form before `ring_nf` can finish.
  sorry

lemma ricci_12 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx thetaIdx = 0 := by
  -- ATTEMPT: should vanish by symmetry once the connection is expanded.
  sorry

lemma ricci_13 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx phiIdx = 0 := by
  -- ATTEMPT: should vanish by the same off-diagonal cancellation pattern as
  -- the `(0,3)` component.
  sorry

lemma ricci_20 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx tIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_02`.
  sorry

lemma ricci_21 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx rIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_12`.
  sorry

lemma ricci_22 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx thetaIdx = 0 := by
  -- ATTEMPT: diagonal component; likely needs explicit algebra after unfolding
  -- `christoffelDerivFromMetricData` and `ricciComponentsFromMetricData`.
  sorry

lemma ricci_23 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx phiIdx = 0 := by
  -- ATTEMPT: should vanish by the same off-diagonal pattern as `ricci_03`.
  sorry

lemma ricci_30 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx tIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_03`.
  sorry

lemma ricci_31 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx rIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_13`.
  sorry

lemma ricci_32 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx thetaIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_23`.
  sorry

lemma ricci_33 (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx phiIdx = 0 := by
  -- ATTEMPT: this diagonal component is the second hard case and probably
  -- needs explicit closed forms for the nonzero Christoffels.
  sorry

@[simp] theorem ricci_component_zero (M a : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    kerrRicciComponents M a x i j = 0 := by
  fin_cases i <;> fin_cases j
  · simpa using ricci_00 M a x
  · simpa using ricci_01 M a x
  · simpa using ricci_02 M a x
  · simpa using ricci_03 M a x
  · simpa using ricci_10 M a x
  · simpa using ricci_11 M a x
  · simpa using ricci_12 M a x
  · simpa using ricci_13 M a x
  · simpa using ricci_20 M a x
  · simpa using ricci_21 M a x
  · simpa using ricci_22 M a x
  · simpa using ricci_23 M a x
  · simpa using ricci_30 M a x
  · simpa using ricci_31 M a x
  · simpa using ricci_32 M a x
  · simpa using ricci_33 M a x

@[simp] theorem ricci_tt (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x tIdx tIdx = 0 := by
  simpa using ricci_00 M a x

@[simp] theorem ricci_rr (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x rIdx rIdx = 0 := by
  simpa using ricci_11 M a x

@[simp] theorem ricci_thetaTheta (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x thetaIdx thetaIdx = 0 := by
  simpa using ricci_22 M a x

@[simp] theorem ricci_phiPhi (M a : ℝ) (x : CoordinateSpace 4) :
    kerrRicciComponents M a x phiIdx phiIdx = 0 := by
  simpa using ricci_33 M a x

end Kerr
end KerrFormalization
