from __future__ import annotations

from pathlib import Path
import hashlib
import json

TRUSTED_CLOSURE = [
    "lean-toolchain",
    "lakefile.lean",
    "lake-manifest.json",
    "KerrFormalization/LocalCoordinates/Basic.lean",
    "KerrFormalization/LocalCoordinates/Fields.lean",
    "KerrFormalization/LocalCoordinates/MetricData.lean",
    "KerrFormalization/LocalCoordinates/InverseMetric.lean",
    "KerrFormalization/Kerr/Basic.lean",
    "KerrFormalization/Schwarzschild/Basic.lean",
    "KerrFormalization/Trusted.lean",
    "KerrFormalization/Trusted/FreezeManifest.lean",
    "KerrFormalization/Trusted/ScalarExpr.lean",
    "KerrFormalization/Trusted/ScalarExprDeriv.lean",
    "KerrFormalization/Trusted/ExactField.lean",
    "KerrFormalization/Trusted/ExactMetricData.lean",
    "KerrFormalization/Trusted/ExactInverseMetric.lean",
    "KerrFormalization/Schwarzschild/MetricExact.lean",
    "KerrFormalization/Schwarzschild/InverseMetricExact.lean",
    "KerrFormalization/Kerr/BoyerLindquistExact.lean",
    "KerrFormalization/Kerr/InverseMetricExact.lean",
]

EXPORTED_THEOREMS = [
    "Schwarzschild.gttField_apply",
    "Schwarzschild.grrField_apply",
    "Schwarzschild.gThetaThetaField_apply",
    "Schwarzschild.gPhiPhiField_apply",
    "Schwarzschild.schwarzschild_inverse_componentwise",
    "Kerr.gttField_apply",
    "Kerr.grrField_apply",
    "Kerr.gThetaThetaField_apply",
    "Kerr.gtPhiField_apply",
    "Kerr.gPhiPhiField_apply",
]

MANIFEST_PATH = Path("aristotle_submissions/frozen_kernel/manifest.json")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_lake_manifest(path: Path) -> dict:
    return json.loads(path.read_text())


def dependency_revs(manifest: dict) -> dict[str, str]:
    packages = manifest.get("packages", [])
    return {pkg["name"]: pkg["rev"] for pkg in packages if "name" in pkg and "rev" in pkg}


def trusted_hashes(repo_root: Path) -> dict[str, str]:
    return {rel: sha256_file(repo_root / rel) for rel in TRUSTED_CLOSURE}
