import Mathlib
import RequestProject.KerrDefs

/-!
# Angular Momentum Conservation for Kerr Geodesics

This file proves that the axial angular momentum L = g_{phi,mu} u^mu
is conserved along geodesics in the Kerr spacetime.

## Main result

`angMomentum_conserved`: The angular momentum is constant along any geodesic,
assuming the standard Kerr geodesic data including axisymmetry of the metric
in Christoffel form (`axisymmetric_christoffel`).

## Finding

Angular momentum conservation requires an `axisymmetric_christoffel` assumption
in the `KerrGeodesicData` structure, exactly analogous to `stationary_christoffel`
but for `phiIdx` instead of `tIdx`. The proof structure is identical to energy
conservation, confirming that energy and angular momentum conservation are
formally isomorphic theorems obtained by swapping the Killing vector field
direction (t ↔ phi).
-/

noncomputable section

open Real

/-! ### Helper lemmas -/

/-- Contracting an antisymmetric bilinear form with a symmetric tensor v⊗v gives zero. -/
lemma antisym_contract_zero (B : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (hB : ∀ i j, B i j + B j i = 0) :
    Finset.univ.sum (fun i : Fin 4 =>
      Finset.univ.sum (fun j : Fin 4 => B i j * v i * v j)) = 0 := by
  norm_num [Fin.sum_univ_four] at *
  grind +ring

/-! ### Main proof -/

/-- The angular momentum has derivative zero at every parameter value.

The proof proceeds by:
1. Differentiating the sum Σ_μ g(φ,μ) v^μ using the product rule
2. Substituting the geodesic equation and metric compatibility
3. Showing that the metric-derivative terms cancel with the geodesic-acceleration terms
4. The remaining terms form an antisymmetric contraction which vanishes
-/
lemma angMomentum_hasDerivAt_zero (M a : ℝ) (D : KerrGeodesicData M a) (p : ℝ) :
    HasDerivAt (fun s => angMomentum M a D.curve s) 0 p := by
  have h_deriv : ∀ μ,
      HasDerivAt (fun s => kerrMetric M a (D.curve.pos s) phiIdx μ)
        (Finset.univ.sum (fun α => Finset.univ.sum (fun σ =>
          kerrMetric M a (D.curve.pos p) phiIdx σ * D.Gamma (D.curve.pos p) σ α μ +
          kerrMetric M a (D.curve.pos p) μ σ * D.Gamma (D.curve.pos p) σ α phiIdx) *
          D.curve.vel p α)) p ∧
      HasDerivAt (fun s => D.curve.vel s μ) (D.curve.acc p μ) p :=
    fun μ => ⟨D.metric_deriv p phiIdx μ, D.acc_deriv p μ⟩
  convert HasDerivAt.sum fun μ _ => HasDerivAt.mul (h_deriv μ |>.1) (h_deriv μ |>.2)
    using 1; aesop
  have h_geodesic : ∀ σ, D.curve.acc p σ +
      Finset.univ.sum (fun μ => Finset.univ.sum (fun ν =>
        D.Gamma (D.curve.pos p) σ μ ν * D.curve.vel p μ * D.curve.vel p ν)) = 0 :=
    D.is_geodesic p
  simp_all +decide [Finset.sum_add_distrib, add_eq_zero_iff_eq_neg]
  simp +decide [Finset.sum_add_distrib, add_mul, mul_add,
    Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, h_geodesic]
  simp +decide [← mul_assoc, ← Finset.sum_mul, ← Finset.sum_comm]
  convert antisym_contract_zero _ _ _ |> Eq.symm using 1
  rotate_left
  use fun i j => ∑ k, kerrMetric M a (D.curve.pos p) i k * D.Gamma (D.curve.pos p) k j phiIdx
  use fun i => D.curve.vel p i
  · intro i j
    have := D.axisymmetric_christoffel (D.curve.pos p) i j
    simp_all +decide [Finset.sum_add_distrib, add_eq_zero_iff_eq_neg]
    convert this using 1
    · exact Finset.sum_congr rfl fun _ _ => by rw [D.christoffel_symm]
    · exact congr_arg Neg.neg (Finset.sum_congr rfl fun _ _ => by rw [D.christoffel_symm])
  · simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm]
    simp +decide only [mul_assoc]

/-- Angular momentum L = g_{φ,μ} u^μ is conserved along geodesics. -/
theorem angMomentum_conserved (M a : ℝ) (D : KerrGeodesicData M a) :
    ∀ s : ℝ, angMomentum M a D.curve s = angMomentum M a D.curve 0 := by
  intro s
  apply is_const_of_deriv_eq_zero
  · exact fun s => (angMomentum_hasDerivAt_zero M a D s).differentiableAt
  · exact fun x => (angMomentum_hasDerivAt_zero M a D x).deriv

/-! ### Metric symmetry -/

/-- The Kerr metric is symmetric in its index arguments. -/
lemma kerrMetric_symm (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    kerrMetric M a x μ ν = kerrMetric M a x ν μ := by
  unfold kerrMetric
  fin_cases μ <;> fin_cases ν <;> simp +decide [*] at *

end
