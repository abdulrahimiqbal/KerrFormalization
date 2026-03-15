# KerrFormalization

KerrFormalization is a Lean 4 project that formalizes Schwarzschild and Kerr black-hole geometry in a coordinate-data framework.

It includes machine-checked vacuum theorems and a validation layer for core Kerr identities in Boyer-Lindquist coordinates.

## What this project does

This repository builds a proof-checked library for exact black-hole spacetime formulas.

Current scope includes:

- a pseudo-Riemannian seed layer
- a local coordinate/tensor-data layer
- Schwarzschild metric definitions and vacuum theorem
- Kerr metric definitions and vacuum theorem
- validation lemmas for horizons, ergoregion, and zero-spin (`a = 0`) reduction
- a cleaned public API surface for exploration and reuse

## What is proved (v1)

At the current v1 stage, the library proves:

- **Schwarzschild is vacuum** in the project’s coordinate-data curvature model
- **Kerr is vacuum** in the project’s coordinate-data curvature model

It also validates key Kerr formulas and checks that the implemented objects match standard Boyer-Lindquist expectations:

- `Delta` and `Sigma` expressions
- representative metric components
- horizon helper identities
- ergoregion membership criterion
- meaningful `a = 0` reduction behavior toward Schwarzschild

## Important modeling note

These results are formal and machine-checked, but they are currently developed in a **coordinate-data curvature framework**, not yet a fully abstract Lorentzian-manifold stack.

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
The goal is to provide a **machine-checked reference layer** for exact black-hole geometry.

## Why this is useful

This library can serve as:

- a **high-assurance reference** for Kerr and Schwarzschild formulas
- a **foundation** for future formalizations (for example Kerr-Newman, Kerr-de Sitter, geodesics, hidden symmetries, black-hole mechanics)
- a **theorem-proving testbed** for formal relativity
- a **teaching aid** where assumptions and reductions are fully explicit

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
- `KerrFormalization.Overview`
- `KerrFormalization.Kerr`
- `KerrFormalization.Kerr.Validation`
- `KerrFormalization.Schwarzschild`
- `KerrFormalization.LocalCoordinates`
- `KerrFormalization.PseudoRiemannian`

## Repository layout

- `KerrFormalization/PseudoRiemannian/`
  - bilinear metrics, nondegeneracy, musical maps, small examples
- `KerrFormalization/LocalCoordinates/`
  - coordinate-space and tensor-data scaffolding, Christoffel/curvature/Ricci/vacuum layers
- `KerrFormalization/Warmup/`
  - Minkowski example
- `KerrFormalization/Schwarzschild/`
  - metric, inverse metric, component lemmas, Ricci/vacuum
- `KerrFormalization/Kerr/`
  - Kerr definitions, inverse metric, Christoffel/Ricci/vacuum, horizons, ergoregion, reduction to Schwarzschild, sanity/validation

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
