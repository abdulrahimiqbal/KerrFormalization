# KerrFormalization Proof Status

This page is a fast map of what the repository currently checks, what is still scaffolded, and what a technical reader should inspect first.

The goal is not to make the project sound complete. The goal is to make the proof boundary easy to audit.

## Short Version

`KerrFormalization` is a Lean 4 project for formalizing Schwarzschild and Kerr black-hole geometry in a coordinate-data framework.

The current public surface contains:

- checked coordinate-data infrastructure
- checked Schwarzschild and Kerr basic definitions
- checked metric/inverse-metric support modules
- checked horizon and local-coordinate modules observed during a clean build attempt
- explicit `sorry` scaffolding for unfinished Ricci/vacuum, Killing-Yano, Killing tensor, conservation-law, and paper-probe work

That means the repo should currently be read as:

> A real formalization and verification workbench with a checked core and explicit open proof targets, not a complete proof of all Kerr geodesic conservation laws.

## Fast Local Check

From a clean clone:

```bash
git clone https://github.com/abdulrahimiqbal/KerrFormalization
cd KerrFormalization
lake exe cache get
lake build KerrFormalization
```

Useful one-file smoke check:

```bash
lake env lean Kerrtest.lean
```

To inspect remaining proof holes:

```bash
rg -n "sorry|admit" KerrFormalization
```

## Proof Status Table

| Area | Representative files | Current status | Notes |
|---|---|---|---|
| Local coordinate framework | `KerrFormalization/LocalCoordinates/*` | Checked core with ongoing extensions | Build reached and checked modules such as `Basic`, `MetricMatrix`, `Fields`, `InverseMetric`, `MetricData`, `Christoffel`, `Curvature`, and `Vacuum` during local verification. |
| Pseudo-Riemannian seed layer | `KerrFormalization/PseudoRiemannian/*` | Checked core with ongoing extensions | `PseudoRiemannian.BilinearMetric` built during local verification. |
| Schwarzschild basics | `KerrFormalization/Schwarzschild/Basic.lean` | Checked | Basic definitions such as lapse and exterior domain are inspectable entry points. |
| Kerr basics | `KerrFormalization/Kerr/Basic.lean` | Checked | Basic Kerr definitions are part of the checked public surface. |
| Kerr horizons | `KerrFormalization/Kerr/Horizons.lean` | Checked | Built during local verification; good first-click example for concrete Kerr identities. |
| Trusted exact scalar/data layer | `KerrFormalization/Trusted/*` | Checked core with minor warnings | `Trusted.ExactField` and `Trusted.ExactMetricData` built during local verification. Some files currently emit unused-variable warnings. |
| Ricci/vacuum claims | `KerrFormalization/Kerr/Ricci.lean`, `KerrFormalization/Schwarzschild/Ricci.lean`, related vacuum wrappers | Incomplete / contains `sorry` | These should not be presented as completed vacuum proofs. README already notes these are tracked openly. |
| Killing-Yano chain | `KerrFormalization/Kerr/KillingYano*.lean`, `KerrFormalization/Kerr/CarterFromKillingYano.lean` | Scaffold / contains `sorry` | This is an explicit research/proof target, not a finished hidden-symmetry proof chain. |
| Killing tensor and conservation | `KerrFormalization/Kerr/KillingTensor.lean`, `KerrFormalization/Kerr/Conservation.lean` | Scaffold / contains `sorry` | Useful as a map of intended theorem targets. |
| Paper 2 probes and open problems | `KerrFormalization/Paper2/*` | Experimental / contains `sorry` | These files encode research questions and probes; they are not all completed proofs. |
| Legacy verification target | `KerrFormalization/Verification.lean` | Not the recommended first check | The README already notes this target is legacy/in-progress. |

## What This Proves Today

The current repository proves that meaningful parts of the coordinate-data formalization are real Lean artifacts, not prose-only claims.

Concrete checked surfaces include the local-coordinate infrastructure, basic Schwarzschild/Kerr definitions, metric/inverse-metric support, Kerr horizons, and trusted exact-data layers.

## What This Does Not Yet Prove

The current repository should not be read as proving:

- full Kerr Ricci-flatness
- completed Schwarzschild/Kerr vacuum proofs
- completed Killing-Yano equation proof
- completed Killing tensor derivation
- completed Carter constant conservation chain
- complete abstract Lorentzian-manifold formalization

Those are active proof targets or scaffolds.

## Recommended First Inspection Path

For a technical reader with limited time:

1. Read the repository README through "Current formal status".
2. Run `lake exe cache get`.
3. Run `lake build KerrFormalization`.
4. Inspect `KerrFormalization/Kerr/Horizons.lean`.
5. Inspect `KerrFormalization/Kerr/Basic.lean`.
6. Run `rg -n "sorry|admit" KerrFormalization` to see the open proof boundary.
7. Treat Ricci/vacuum and hidden-symmetry files as research targets unless their `sorry` status changes.

## Why This Status Page Exists

AI-assisted scientific work needs visible proof boundaries.

For this project, the high-signal public claim is not "everything is solved." It is:

> Here is a checked core, here are the open proof targets, and here is the exact boundary between them.

That boundary is the artifact.
