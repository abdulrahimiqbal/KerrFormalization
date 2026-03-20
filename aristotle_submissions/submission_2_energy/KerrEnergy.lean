import RequestProject.KerrDefs

/-!
# Energy Conservation for Kerr Geodesics

Proof that the energy E = -g_{tμ} u^μ is conserved along geodesics
of the Kerr spacetime.
-/

noncomputable section

open Finset

/-
PROBLEM
Key lemma: The derivative of energy along a geodesic is zero.
    This is the infinitesimal version of energy conservation (Noether's theorem
    for the time-translation Killing vector).

PROVIDED SOLUTION
energy(s) = -Σ_μ g_{tμ}(γ(s)) · vel(s)_μ

By HasDerivAt.neg and HasDerivAt.sum, it suffices to show:
HasDerivAt (fun s => Σ_μ g_{tμ}(γ(s)) · vel(s)_μ) 0 p

By HasDerivAt.sum, this reduces to showing for each μ:
HasDerivAt (fun s => g_{tμ}(γ(s)) · vel(s)_μ) (d_μ) p
where Σ_μ d_μ = 0.

By HasDerivAt.mul (product rule), for each μ:
d_μ = (dg_{tμ}/ds) · vel(p)_μ + g_{tμ}(γ(p)) · acc(p)_μ

where dg_{tμ}/ds comes from D.metric_deriv and acc from D.acc_deriv.

So the total derivative is:
Σ_μ [(Σ_α (Σ_σ (g_{tσ} Γ^σ_{αμ} + g_{μσ} Γ^σ_{αt}) vel_α)) · vel_μ + g_{tμ} · acc_μ]

Split into three sums:
A = Σ_{μ,α,σ} g_{tσ} Γ^σ_{αμ} vel_α vel_μ
B = Σ_{μ,α,σ} g_{μσ} Γ^σ_{αt} vel_α vel_μ
C = Σ_μ g_{tμ} acc_μ

From geodesic equation: acc_μ = -Σ_{α,β} Γ^μ_{αβ} vel_α vel_β
So C = -Σ_{μ,α,β} g_{tμ} Γ^μ_{αβ} vel_α vel_β

A + C: Relabel σ→μ' in A gives Σ_{μ,α,μ'} g_{tμ'} Γ^{μ'}_{αμ} vel_α vel_μ.
Rename μ'→μ, μ→β: Σ_{μ,α,β} g_{tμ} Γ^μ_{αβ} vel_α vel_β = -C. So A + C = 0.

B: Use Γ^σ_{αt} = Γ^σ_{tα} by D.christoffel_symm.
Then B = Σ_{μ,α,σ} g_{μσ} Γ^σ_{tα} vel_α vel_μ
= Σ_{α,μ} (Σ_σ g_{μσ} Γ^σ_{tα}) vel_α vel_μ

By D.stationary_christoffel with indices (μ, α):
Σ_σ (g_{μσ} Γ^σ_{tα} + g_{ασ} Γ^σ_{tμ}) = 0
So Σ_σ g_{μσ} Γ^σ_{tα} = -Σ_σ g_{ασ} Γ^σ_{tμ}

This means B_{μα} := Σ_σ g_{μσ} Γ^σ_{tα} is antisymmetric: B_{μα} = -B_{αμ}.
Since vel_α vel_μ is symmetric and B_{μα} is antisymmetric:
Σ_{α,μ} B_{μα} vel_α vel_μ = 0.

So total = A + B + C = 0.
-/
lemma energy_hasDerivAt_zero (M a : ℝ) (D : KerrGeodesicData M a) (p : ℝ) :
    HasDerivAt (fun s => energy M a D.γ s) 0 p := by
  -- By definition of energy, we have:
  have h_energy_def : ∀ p : ℝ, HasDerivAt (fun s => -Finset.sum Finset.univ (fun μ => kerrMetric M a (D.γ.pos s) tIdx μ * D.γ.vel s μ)) 0 p := by
    -- By definition of energy, we can write its derivative using the product rule and the geodesic equation.
    have h_deriv : ∀ p, HasDerivAt (fun s => Finset.sum Finset.univ (fun μ => kerrMetric M a (D.γ.pos s) tIdx μ * D.γ.vel s μ)) (Finset.sum Finset.univ (fun μ => (Finset.sum Finset.univ (fun α => (Finset.sum Finset.univ (fun σ => kerrMetric M a (D.γ.pos p) tIdx σ * D.Gamma (D.γ.pos p) σ α μ + kerrMetric M a (D.γ.pos p) μ σ * D.Gamma (D.γ.pos p) σ α tIdx)) * D.γ.vel p α)) * D.γ.vel p μ + kerrMetric M a (D.γ.pos p) tIdx μ * D.γ.acc p μ)) p := by
      intro p
      have h_sum_deriv : ∀ μ, HasDerivAt (fun s => kerrMetric M a (D.γ.pos s) tIdx μ * D.γ.vel s μ) ((Finset.sum Finset.univ (fun α => (Finset.sum Finset.univ (fun σ => kerrMetric M a (D.γ.pos p) tIdx σ * D.Gamma (D.γ.pos p) σ α μ + kerrMetric M a (D.γ.pos p) μ σ * D.Gamma (D.γ.pos p) σ α tIdx)) * D.γ.vel p α)) * D.γ.vel p μ + kerrMetric M a (D.γ.pos p) tIdx μ * D.γ.acc p μ) p := by
        intro μ;
        convert HasDerivAt.mul ( D.metric_deriv p tIdx μ ) ( D.acc_deriv p μ ) using 1;
      exact?;
    intro p; specialize h_deriv p; convert h_deriv.neg using 1; simp +decide [ Finset.sum_add_distrib, mul_add, add_mul, D.stationary_christoffel ] ;
    -- By the geodesic equation, we know that $acc_μ = -\sum_{α,β} Γ^μ_{αβ} vel_α vel_β$.
    have h_geodesic : ∀ μ, D.γ.acc p μ = -∑ α, ∑ β, D.Gamma (D.γ.pos p) μ α β * D.γ.vel p α * D.γ.vel p β := by
      exact fun μ => eq_neg_of_add_eq_zero_left <| D.is_geodesic p μ;
    simp +decide [ h_geodesic, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm ];
    simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, D.christoffel_symm ];
    have h_zero_sum : ∀ x i, (∑ i_1, kerrMetric M a (D.γ.pos p) i i_1 * D.Gamma (D.γ.pos p) i_1 x tIdx) = - (∑ i_1, kerrMetric M a (D.γ.pos p) x i_1 * D.Gamma (D.γ.pos p) i_1 i tIdx) := by
      intro x i; have := D.stationary_christoffel ( D.γ.pos p ) i x; simp_all +decide [ Finset.sum_add_distrib, mul_comm ] ;
      simp_all +decide [ add_eq_zero_iff_eq_neg, D.christoffel_symm ];
    have h_zero_sum : ∑ x, ∑ i, (∑ i_1, kerrMetric M a (D.γ.pos p) i i_1 * D.Gamma (D.γ.pos p) i_1 x tIdx) * D.γ.vel p i * D.γ.vel p x = ∑ x, ∑ i, - (∑ i_1, kerrMetric M a (D.γ.pos p) x i_1 * D.Gamma (D.γ.pos p) i_1 i tIdx) * D.γ.vel p i * D.γ.vel p x := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ h_zero_sum ] ;
    simp +decide [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ] at h_zero_sum ⊢;
    linarith [ show ∑ x : Fin 4, ∑ x_1 : Fin 4, D.γ.vel p x * ( D.γ.vel p x_1 * ∑ i_1 : Fin 4, kerrMetric M a ( D.γ.pos p ) x i_1 * D.Gamma ( D.γ.pos p ) i_1 x_1 tIdx ) = ∑ x : Fin 4, ∑ x_1 : Fin 4, ∑ x_2 : Fin 4, kerrMetric M a ( D.γ.pos p ) x_1 x_2 * ( D.Gamma ( D.γ.pos p ) x_2 x tIdx * ( D.γ.vel p x * D.γ.vel p x_1 ) ) by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ];
  convert h_energy_def p using 1

/-
PROBLEM
Energy is conserved along Kerr geodesics.

PROVIDED SOLUTION
Use `energy_hasDerivAt_zero` to get `HasDerivAt (fun s => energy M a D.γ s) 0 p` for all p. This gives:
1. Differentiability: `(energy_hasDerivAt_zero M a D p).differentiableAt` for each p, hence `Differentiable ℝ (fun s => energy M a D.γ s)`.
2. Derivative is zero: `(energy_hasDerivAt_zero M a D p).deriv` gives `deriv (fun s => energy M a D.γ s) p = 0`.
Then apply `is_const_of_deriv_eq_zero` to conclude `energy M a D.γ p = energy M a D.γ 0` for all p.
-/
theorem energy_conserved (M a : ℝ) (D : KerrGeodesicData M a) :
    ∀ p : ℝ, energy M a D.γ p = energy M a D.γ 0 := by
  intro p;
  apply is_const_of_deriv_eq_zero (fun p => ?_) (fun p => ?_) p 0;
  · exact ( energy_hasDerivAt_zero M a D p |> HasDerivAt.differentiableAt );
  · exact HasDerivAt.deriv ( energy_hasDerivAt_zero M a D p )

end