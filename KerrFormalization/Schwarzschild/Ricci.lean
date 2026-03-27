import KerrFormalization.Schwarzschild.VacuumPrelude
import KerrFormalization.LocalCoordinates.Curvature

/-!
# Schwarzschild Ricci components

This file packages Ricci components for Schwarzschild in the current
coordinate-data curvature API.

STATUS: incomplete formal Ricci vanishing proof.
All component-vanishing lemmas below are placeholders and are not suitable for
public vacuum claims.
-/

namespace KerrFormalization
namespace Schwarzschild

open LocalCoordinates

/-- Ricci components associated to Schwarzschild metric/inverse data. -/
noncomputable def schwarzschildRicciComponents (M : ℝ) : RicciComponentsData 4 :=
  ricciComponentsFromMetricData (schwarzschildMetricData M) (schwarzschildInverseMetricWithDeriv M)

lemma ricci_00 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx tIdx = 0 := by
  -- ATTEMPT: the Schwarzschild case should be substantially easier than Kerr;
  -- the likely route is to unfold the exact metric data and let the diagonal
  -- structure kill most Christoffel terms before finishing with `ring_nf`.
  sorry

lemma ricci_01 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx rIdx = 0 := by
  -- ATTEMPT: off-diagonal symmetry/sparsity should make this the first easy
  -- component once the connection is unfolded.
  sorry

lemma ricci_02 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx thetaIdx = 0 := by
  -- ATTEMPT: same off-diagonal cancellation pattern as `ricci_01`.
  sorry

lemma ricci_03 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx phiIdx = 0 := by
  -- ATTEMPT: same off-diagonal cancellation pattern as `ricci_01`.
  sorry

lemma ricci_11 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx rIdx = 0 := by
  -- ATTEMPT: this diagonal component likely needs the explicit derivative
  -- formulas from `Schwarzschild/VacuumPrelude.lean` before the algebra closes.
  sorry

lemma ricci_10 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx tIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_01`.
  sorry

lemma ricci_12 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx thetaIdx = 0 := by
  -- ATTEMPT: off-diagonal cancellation after unfolding the exact connection.
  sorry

lemma ricci_13 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx phiIdx = 0 := by
  -- ATTEMPT: off-diagonal cancellation after unfolding the exact connection.
  sorry

lemma ricci_22 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx thetaIdx = 0 := by
  -- ATTEMPT: diagonal angular component; should be manageable once the exact
  -- Christoffel derivatives are expanded.
  sorry

lemma ricci_20 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx tIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_02`.
  sorry

lemma ricci_21 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx rIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_12`.
  sorry

lemma ricci_23 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx phiIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_03`.
  sorry

lemma ricci_33 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx phiIdx = 0 := by
  -- ATTEMPT: diagonal angular component; this is another likely place where a
  -- direct explicit-Christoffel normal form would pay off.
  sorry

lemma ricci_30 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx tIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_03`.
  sorry

lemma ricci_31 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx rIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_13`.
  sorry

lemma ricci_32 (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx thetaIdx = 0 := by
  -- ATTEMPT: symmetry should reduce this to `ricci_23`.
  sorry

@[simp] theorem ricci_component_zero (M : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) :
    schwarzschildRicciComponents M x i j = 0 := by
  fin_cases i <;> fin_cases j
  · simpa using ricci_00 M x
  · simpa using ricci_01 M x
  · simpa using ricci_02 M x
  · simpa using ricci_03 M x
  · simpa using ricci_10 M x
  · simpa using ricci_11 M x
  · simpa using ricci_12 M x
  · simpa using ricci_13 M x
  · simpa using ricci_20 M x
  · simpa using ricci_21 M x
  · simpa using ricci_22 M x
  · simpa using ricci_23 M x
  · simpa using ricci_30 M x
  · simpa using ricci_31 M x
  · simpa using ricci_32 M x
  · simpa using ricci_33 M x

@[simp] theorem ricci_tt (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x tIdx tIdx = 0 := by
  simpa using ricci_00 M x

@[simp] theorem ricci_rr (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x rIdx rIdx = 0 := by
  simpa using ricci_11 M x

@[simp] theorem ricci_thetaTheta (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x thetaIdx thetaIdx = 0 := by
  simpa using ricci_22 M x

@[simp] theorem ricci_phiPhi (M : ℝ) (x : CoordinateSpace 4) :
    schwarzschildRicciComponents M x phiIdx phiIdx = 0 := by
  simpa using ricci_33 M x

@[simp] theorem ricci_offDiag (M : ℝ) (x : CoordinateSpace 4) (i j : Fin 4) (hij : i ≠ j) :
    schwarzschildRicciComponents M x i j = 0 := by
  simpa using ricci_component_zero M x i j

end Schwarzschild
end KerrFormalization
