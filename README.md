# KerrFormalization

KerrFormalization is a Lean 4 project that formalizes Schwarzschild and Kerr black-hole geometry in a coordinate-data framework.

It includes machine-checked coordinate-data definitions and validation lemmas for core Kerr identities in Boyer-Lindquist coordinates.

## What this project does

This repository builds a proof-checked prototype library for exact black-hole spacetime formulas.

Current scope includes:

- a pseudo-Riemannian seed layer
- a local coordinate/tensor-data layer
- Schwarzschild metric definitions and inverse-metric data
- Kerr metric definitions and inverse-metric data
- validation lemmas for horizons, ergoregion, and zero-spin (`a = 0`) reduction
- a cleaned public API surface for exploration and reuse

## Current formal status (v1)

At the current v1 stage, the library includes machine-checked:

- Kerr `Delta` and `Sigma` identities
- horizon helper identities
- ergoregion membership criterion
- meaningful `a = 0` reduction behavior toward Schwarzschild
- metric/inverse-metric component formulas in the coordinate-data layer

## Important modeling note

These results are formal and machine-checked in a **coordinate-data curvature framework**, not yet a fully abstract Lorentzian-manifold stack.

In practice, this means geometry is expressed using explicit coordinate data and supplied derivative structure, rather than a full abstract Levi-Civita/curvature development on smooth manifolds.

This is a deliberate engineering choice to make exact black-hole solutions tractable in Lean while building toward deeper abstraction over time.

## Why Kerr in Lean?

Kerr geometry is algebraically delicate. Small convention mismatches can cause major errors.

Formalization helps because Lean forces complete explicitness for:

- sign conventions
- coordinate conventions
- off-diagonal terms
- horizon identities
- reductions like `a = 0`
- long symbolic dependencies

The goal is not to replace numerical relativity or symbolic GR packages.
The goal is to provide a machine-checked coordinate-data reference layer for exact black-hole geometry.

## Why this is useful

This library can serve as:

- a formal coordinate-data reference for Kerr and Schwarzschild formulas
- a **foundation** for future formalizations (for example Kerr-Newman, Kerr-de Sitter, geodesics, hidden symmetries, black-hole mechanics)
- a **theorem-proving testbed** for formal relativity
- a **teaching aid** where assumptions and reductions are fully explicit

## Incomplete pieces (tracked openly)

- `KerrFormalization/Kerr/Ricci.lean` and `KerrFormalization/Schwarzschild/Ricci.lean` still contain placeholder Ricci-component vanishing proofs.
- Vacuum theorem wrappers that depend on those Ricci files are currently not exported from the default public entry points.
- Completing vacuum claims honestly requires finishing Ricci proofs from correct derivative data (or a stronger symbolic differentiation layer).

## What this project is not

This repository is not intended for:

- numerical simulation
- astrophysical data analysis
- replacing Mathematica/xAct/Sage for exploratory workflows
- claiming a complete abstract formalization of Lorentzian geometry

It is a formal proof library, not a simulation engine.

## Public entry points

Useful top-level imports:

- `KerrFormalization`
- `KerrFormalization.Trusted`
- `KerrFormalization.Experimental`
- `KerrFormalization.Overview`
- `KerrFormalization.Kerr`
- `KerrFormalization.Kerr.Validation`
- `KerrFormalization.Schwarzschild`
- `KerrFormalization.LocalCoordinates`
- `KerrFormalization.PseudoRiemannian`

## Trusted Phase I surface

The frozen, checked Phase I kernel lives under `KerrFormalization.Trusted` and
is built from exact scalar expressions plus generated derivatives.

Phase I trusted modules currently cover:

- exact scalar-expression AST and derivative generation
- exact Schwarzschild metric and inverse data
- exact Kerr metric and inverse data
- frozen submission manifest tooling

Phase I does not yet include Ricci, vacuum, Killing tensor, geodesic, or
perturbation-lab infrastructure.

## Repository layout

- `KerrFormalization/PseudoRiemannian/`
  - bilinear metrics, nondegeneracy, musical maps, small examples
- `KerrFormalization/LocalCoordinates/`
  - coordinate-space and tensor-data scaffolding, Christoffel/curvature/Ricci/vacuum layers
- `KerrFormalization/Warmup/`
  - Minkowski example
- `KerrFormalization/Schwarzschild/`
  - metric, inverse metric, component lemmas, and vacuum-prelude data
- `KerrFormalization/Kerr/`
  - Kerr definitions, inverse metric, Christoffel, horizons, ergoregion, reduction to Schwarzschild, sanity/validation

## Conservation Laws

The repository now includes a first-pass conservation-law layer for Kerr geodesics:

- `KerrFormalization/Kerr/KillingTensor.lean`
  - Form C Killing tensor components and the symmetrized Killing-equation theorem stub
- `KerrFormalization/Kerr/Geodesic.lean`
  - Kerr geodesic data structure using the coordinate Christoffel symbols
- `KerrFormalization/Kerr/Conservation.lean`
  - energy, angular momentum, and Carter-constant definitions together with theorem stubs

These files are intended as the formal landing point for the Aristotle audit results and the paper's minimal-axiom-set analysis.

## Paper

This repository accompanies the paper "Minimal Axiom Sets for Kerr
Geodesic Conservation Laws: A Machine-Verified Audit Using Aristotle"
(submitted to Journal of Automated Reasoning, 2026).

## Aristotle Results

The full curated record of Aristotle submissions, returned Lean files,
and summary notes is stored in:

- `aristotle_submissions/`
- `aristotle_submissions/SUBMISSIONS.md`

## Quick start (2 minutes)

If you do not have Lean installed yet:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Open a new terminal, then from the project root run:

```bash
lake --version
lake build KerrFormalization
```

That is enough to fetch dependencies, use the repository's pinned toolchain, and build the main library target.

If `lake` is not found after installing `elan`, restart your shell (or re-open your terminal) and try again.

For editor support, install the VS Code extension **Lean 4** and open this folder as a workspace.

## First 5 minutes

```bash
git clone https://github.com/abdulrahimiqbal/KerrFormalization.git
cd KerrFormalization
lake build KerrFormalization
lake env lean Kerrtest.lean
```

If those commands succeed, your local setup is working.

## Build

From the project root:

```bash
lake build KerrFormalization
```

## Running checks

Expected green target:

- `lake build KerrFormalization`

Legacy/in-progress target (currently not expected to pass unless those modules are restored):

- `lake build KerrFormalization.Verification`

Useful one-file check:

- `lake env lean Kerrtest.lean`

## Contributing

- Create a feature branch (project convention uses `tranche-...` names for tranche work).
- Keep changes small and focused.
- Do not introduce `sorry`.
- Before pushing, run:

```bash
lake build KerrFormalization
```

## Common issues

- `lake: command not found` after installing `elan`:
  restart your terminal (or shell), then retry.
- First build is slow:
  Lean toolchain and dependencies are downloaded on first run.
- Build fails on `KerrFormalization.Verification`:
  this target references modules that are not present in the current v1 scope.
