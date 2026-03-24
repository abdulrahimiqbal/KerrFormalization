# Phase I Execution Report

## 1. What I changed
- Created `KerrFormalization/Trusted.lean`
- Created `KerrFormalization/Trusted/FreezeManifest.lean`
- Created `KerrFormalization/Trusted/ScalarExpr.lean`
- Created `KerrFormalization/Trusted/ScalarExprDeriv.lean`
- Created `KerrFormalization/Trusted/ExactField.lean`
- Created `KerrFormalization/Trusted/ExactMetricData.lean`
- Created `KerrFormalization/Trusted/ExactInverseMetric.lean`
- Created `KerrFormalization/Experimental.lean`
- Created `KerrFormalization/Schwarzschild/MetricExact.lean`
- Created `KerrFormalization/Schwarzschild/InverseMetricExact.lean`
- Created `KerrFormalization/Kerr/BoyerLindquistExact.lean`
- Created `KerrFormalization/Kerr/InverseMetricExact.lean`
- Created `scripts/freeze_manifest_shared.py`
- Created `scripts/generate_freeze_manifest.py`
- Created `scripts/verify_freeze_manifest.py`
- Created `aristotle_submissions/frozen_kernel/README.md`
- Created `aristotle_submissions/frozen_kernel/manifest.json`
- Edited `lakefile.lean`
- Edited `KerrFormalization/LocalCoordinates/Fields.lean`
- Edited `KerrFormalization/LocalCoordinates/InverseMetric.lean`
- Edited `KerrFormalization/Kerr/Basic.lean`
- Edited `KerrFormalization/Schwarzschild/Basic.lean`
- Edited `KerrFormalization/Schwarzschild/Metric.lean`
- Edited `KerrFormalization/Schwarzschild/InverseMetric.lean`
- Edited `KerrFormalization/Kerr/BoyerLindquist.lean`
- Edited `KerrFormalization/Kerr/InverseMetric.lean`
- Edited `KerrFormalization/Kerr.lean`
- Edited `KerrFormalization/Schwarzschild.lean`
- Edited `KerrFormalization.lean`
- Edited `README.md`

## 2. Mathlib/source pinning
- Old state: `lakefile.lean` required mathlib from `master`.
- New state: `lakefile.lean` now pins mathlib to the exact resolved rev already present in `lake-manifest.json`.
- Exact pinned rev: `11d58e7e9180ec5c67dbf676130c12900a04659a`.

## 3. Trusted kernel added
- Trusted surface files now exist in `KerrFormalization/Trusted.lean` and `KerrFormalization/Trusted/*`.
- The trusted kernel includes the exact expression AST, generated derivatives, exact field wrappers, exact metric data, exact inverse metric data, and the frozen manifest anchor.
- Intentionally excluded from the trusted surface:
  - `KerrFormalization/Kerr/Ricci.lean`
  - `KerrFormalization/Kerr/Vacuum.lean`
  - `KerrFormalization/Schwarzschild/Ricci.lean`
  - `KerrFormalization/Schwarzschild/Vacuum.lean`
  - hidden-symmetry / geodesic / conservation modules
- `KerrFormalization/Experimental.lean` exists as the namespace split placeholder, but it is not part of the trusted closure.
- The trusted closure is anchored in `KerrFormalization/Trusted/FreezeManifest.lean` and mirrored by `scripts/freeze_manifest_shared.py`.

## 4. Exact derivative kernel
- Implemented AST operators:
  - constants
  - coordinate variables
  - addition
  - subtraction
  - multiplication
  - division
  - integer powers
  - sine
  - cosine
- Implemented field constructors:
  - `ExactField.fromExpr`
  - `ExactField.const`
  - `ExactField.coord`
- Implemented generated derivative layer:
  - first derivatives by coordinate
  - second derivatives by coordinate pair
- What remains unsupported:
  - a general symbolic simplifier
  - any broader geometry pipeline beyond the exact scalar-expression kernel
  - quotient / ghost / perturbation infrastructure, which is deliberately deferred to Phase III
- `KerrFormalization/LocalCoordinates/Fields.lean` was left as compatibility-only legacy data; Phase I trusted code should use `KerrFormalization.Trusted` instead.

## 5. Metric/inverse migration
- Schwarzschild status:
  - `KerrFormalization/Schwarzschild/MetricExact.lean` now builds the trusted metric fields from `ExactField`.
  - `KerrFormalization/Schwarzschild/InverseMetricExact.lean` now builds the trusted inverse fields from exact expressions.
  - `KerrFormalization/Schwarzschild/Metric.lean` and `KerrFormalization/Schwarzschild/InverseMetric.lean` are compatibility wrappers.
- Kerr status:
  - `KerrFormalization/Kerr/BoyerLindquistExact.lean` now holds the exact Boyer-Lindquist metric fields.
  - `KerrFormalization/Kerr/InverseMetricExact.lean` now holds the exact inverse metric data.
  - `KerrFormalization/Kerr/BoyerLindquist.lean` and `KerrFormalization/Kerr/InverseMetric.lean` are compatibility wrappers.
  - No trusted Kerr metric path still uses `deriv2 := fun _ _ _ => 0`.
- Top-level re-exports were rewired so the public exact metric/inverse pair is the one used by the trusted surface.

## 6. Inverse correctness status
- The old vacuous contract `IsInverseMetric := True` was removed from the trusted path.
- `KerrFormalization/LocalCoordinates/InverseMetric.lean` now defines a real componentwise inverse relation over the coordinate domain.
- Schwarzschild inverse correctness:
  - partial only.
  - the exact inverse data is present, but the full componentwise proof remains a clearly delimited goal marker.
- Kerr inverse correctness:
  - partial only.
  - exact inverse data exists, but the full componentwise proof was not completed in this tranche.
  - `KerrFormalization/Kerr/InverseMetricExact.lean` includes a clearly delimited goal marker rather than a fake proof.

## 7. Checks run
- Targeted Lean checks passed:
  - `KerrFormalization/Trusted.lean`
  - `KerrFormalization/Trusted/FreezeManifest.lean`
  - `KerrFormalization/Trusted/ScalarExpr.lean`
  - `KerrFormalization/Trusted/ScalarExprDeriv.lean`
  - `KerrFormalization/Trusted/ExactField.lean`
  - `KerrFormalization/Trusted/ExactMetricData.lean`
  - `KerrFormalization/Trusted/ExactInverseMetric.lean`
  - `KerrFormalization/LocalCoordinates/Fields.lean`
  - `KerrFormalization/LocalCoordinates/InverseMetric.lean`
  - `KerrFormalization/Schwarzschild/Metric.lean`
  - `KerrFormalization/Schwarzschild/InverseMetric.lean`
  - `KerrFormalization/Schwarzschild/MetricExact.lean`
  - `KerrFormalization/Schwarzschild/InverseMetricExact.lean`
  - `KerrFormalization/Kerr/BoyerLindquist.lean`
  - `KerrFormalization/Kerr/InverseMetric.lean`
  - `KerrFormalization/Kerr/BoyerLindquistExact.lean`
  - `KerrFormalization/Kerr/InverseMetricExact.lean`
  - `KerrFormalization/Kerr.lean`
  - `KerrFormalization/Schwarzschild.lean`
- Manifest tooling:
  - `python3 scripts/generate_freeze_manifest.py` passed
  - `python3 scripts/verify_freeze_manifest.py` passed
- No current targeted Lean check is failing.

## 8. Remaining blockers before Phase II
- Schwarzschild and Kerr inverse correctness are both still partial markers, so the Ricci/vacuum lane should treat them as open proof obligations rather than trusted theorems.
- Exact Ricci/vacuum work still needs a real curvature pass driven by the exact derivative kernel.
- The legacy compatibility API remains available in `LocalCoordinates/Fields.lean`, so Phase II should stay on the frozen trusted surface only.

## 9. Next exact move
- Next 3 files to touch for the Schwarzschild exact Ricci canary:
  - `KerrFormalization/Schwarzschild/MetricExact.lean`
  - `KerrFormalization/Schwarzschild/InverseMetricExact.lean`
  - `KerrFormalization/Schwarzschild/Ricci.lean`
- Next 3 files to touch for Kerr exact Ricci:
  - `KerrFormalization/Kerr/BoyerLindquistExact.lean`
  - `KerrFormalization/Kerr/InverseMetricExact.lean`
  - `KerrFormalization/Kerr/Ricci.lean`
