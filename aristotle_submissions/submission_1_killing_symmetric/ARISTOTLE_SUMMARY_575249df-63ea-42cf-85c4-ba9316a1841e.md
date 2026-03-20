# Summary of changes
I formalized and proved the Killing tensor symmetry theorem in `RequestProject/KillingTensor.lean`. Here's what was built:

**Definitions:**
- `kerrSigma`: The Kerr Σ = r² + a²cos²θ function
- `kerrDelta`: The Kerr Δ = r² − 2Mr + a² function  
- `kerrMetric`: The full Kerr metric tensor in Boyer-Lindquist coordinates (covariant components), defined as a symmetric function `Fin 4 → Fin 4 → ℝ`
- `killingTensor`: The Killing tensor K_{μν} = r²·g_{μν} + Δ·Σ·δʳ_μ·δʳ_ν, built from the metric and Kronecker deltas

**Theorems proved (no sorry, machine-verified):**
- `kerrMetric_symm`: The Kerr metric is symmetric in its indices (proved by exhaustive case analysis on all 16 index pairs)
- `killing_tensor_equation`: The Killing tensor is symmetric, K_{μν} = K_{νμ} (proved using metric symmetry and commutativity of multiplication for the Kronecker delta term)

The unused variable `α` in the theorem statement is preserved from your original formulation. A TODO comment notes that the full Carter constant conservation theorem would require formalizing covariant derivatives and geodesic equations, which is beyond the scope of the current symmetry result.