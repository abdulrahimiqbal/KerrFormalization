# Summary of changes
## Summary

I analyzed and worked on the two `sorry` theorems in `RequestProject/KerrKillingTensor.lean`:

### 1. `killing_tensor_conservation_from_equation` — **Proved** ✅

The conclusion of this theorem is definitionally equal to `γ.killing_tensor_conservation_law p` (since `γ.curve = γ.γ` by definition of `KerrGeodesicData.curve`), so the proof is:
```lean
intro p
exact γ.killing_tensor_conservation_law p
```

**Important caveat** (documented in the file): The hypothesis `hKilling` is unused. This proof uses the `killing_tensor_conservation_law` field from `KerrGeodesicData`, which is the very axiom the chain was meant to replace. So while the Lean proof is valid, **it does not break the circularity** described in the comments.

### 2. `killing_tensor_cov_deriv_zero` — **Cannot be proved as stated** ❌

This theorem is unprovable for two independent reasons, both documented in detail in the file:

1. **Opaque axioms**: Both `killingTensorPartial` and `IsKerrChristoffel` are declared as `axiom` with no definitional content. No information can be extracted from `hGamma : IsKerrChristoffel M a Gamma`, and `covDerivKilling` cannot be simplified because `killingTensorPartial` is opaque.

2. **Mathematically incorrect statement**: The theorem claims the **unsymmetrized** covariant derivative `∇_α K_{μν} = 0` for all α, μ, ν. This is false for any non-trivial Killing tensor in curved spacetime. The correct Killing tensor equation is the **symmetrized** version: `∇_{(α} K_{μν)} = 0`, i.e., `∇_α K_{μν} + ∇_μ K_{να} + ∇_ν K_{αμ} = 0`. (Carter constant conservation only requires this weaker symmetrized condition, since the contraction with `u^α u^μ u^ν` is automatically symmetric.)

### Additional changes
- Fixed a `λ` variable name that is a Lean keyword (replaced with `l`)
- Renamed `killing_tensor_equation` to `killing_tensor_symm` to better reflect its content (it proves symmetry K_{μν} = K_{νμ}, not the Killing tensor equation)
- Fixed an unused variable `α` in the original `killing_tensor_equation`
- Added detailed documentation explaining the gap and what would need to change to fully close the circular axiom

### What would be needed to fully close the gap

The file includes a detailed roadmap (in comments) for completing the formalization:
1. Replace `axiom killingTensorPartial` with a concrete partial-derivative definition
2. Replace `axiom IsKerrChristoffel` with concrete Kerr Christoffel symbol definitions  
3. Correct the statement to the symmetrized Killing tensor equation
4. Add a `killing_tensor_deriv` field connecting partial derivatives to `HasDerivAt`
5. Re-prove `killing_tensor_conservation_from_equation` from first principles (chain rule + product rule + geodesic equation + symmetrized KTE)