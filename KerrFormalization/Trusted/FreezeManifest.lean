/-!
# Frozen trusted kernel manifest anchor

This file documents the Phase I trusted closure and the submission policy that
the generator/verifier scripts enforce.

The authoritative hashes live in `scripts/freeze_manifest_shared.py` and the
generated JSON manifest under `aristotle_submissions/frozen_kernel/manifest.json`.
-/

namespace KerrFormalization
namespace Trusted

/-- Phase I trusted closure, mirrored by the manifest generator/verifier. -/
def phase1TrustedClosure : List String :=
  [ "lean-toolchain"
  , "lakefile.lean"
  , "lake-manifest.json"
  , "KerrFormalization/LocalCoordinates/Basic.lean"
  , "KerrFormalization/LocalCoordinates/Fields.lean"
  , "KerrFormalization/LocalCoordinates/MetricData.lean"
  , "KerrFormalization/LocalCoordinates/InverseMetric.lean"
  , "KerrFormalization/Kerr/Basic.lean"
  , "KerrFormalization/Schwarzschild/Basic.lean"
  , "KerrFormalization/Trusted.lean"
  , "KerrFormalization/Trusted/FreezeManifest.lean"
  , "KerrFormalization/Trusted/ScalarExpr.lean"
  , "KerrFormalization/Trusted/ScalarExprDeriv.lean"
  , "KerrFormalization/Trusted/ExactField.lean"
  , "KerrFormalization/Trusted/ExactMetricData.lean"
  , "KerrFormalization/Trusted/ExactInverseMetric.lean"
  , "KerrFormalization/Schwarzschild/MetricExact.lean"
  , "KerrFormalization/Schwarzschild/InverseMetricExact.lean"
  , "KerrFormalization/Kerr/BoyerLindquistExact.lean"
  , "KerrFormalization/Kerr/InverseMetricExact.lean"
  ]

/-- Only theorem names recorded in the frozen manifest may be cited by Aristotle batches. -/
def phase1ExportedTheorems : List String :=
  [ "Schwarzschild.gttField_apply"
  , "Schwarzschild.grrField_apply"
  , "Schwarzschild.gThetaThetaField_apply"
  , "Schwarzschild.gPhiPhiField_apply"
  , "Schwarzschild.schwarzschild_inverse_componentwise"
  , "Kerr.gttField_apply"
  , "Kerr.grrField_apply"
  , "Kerr.gThetaThetaField_apply"
  , "Kerr.gtPhiField_apply"
  , "Kerr.gPhiPhiField_apply"
  ]

/-- Human-readable submission policy summary. -/
def phase1SubmissionPolicy : String :=
  "Aristotle batches must use only the frozen trusted closure and the theorem names listed in the manifest."

end Trusted
end KerrFormalization
