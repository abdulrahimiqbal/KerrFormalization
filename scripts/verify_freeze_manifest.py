from __future__ import annotations

from pathlib import Path
import json
import sys

from freeze_manifest_shared import MANIFEST_PATH, load_lake_manifest, trusted_hashes, dependency_revs


def fail(message: str) -> int:
    print(message, file=sys.stderr)
    return 1


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    if not MANIFEST_PATH.exists():
        return fail(f"missing manifest: {MANIFEST_PATH}")
    manifest = json.loads(MANIFEST_PATH.read_text())
    expected_toolchain = (repo_root / "lean-toolchain").read_text().strip()
    if manifest.get("lean_toolchain") != expected_toolchain:
        return fail("lean toolchain mismatch")
    current_lake_manifest = load_lake_manifest(repo_root / "lake-manifest.json")
    if manifest.get("dependency_revs") != dependency_revs(current_lake_manifest):
        return fail("dependency rev mismatch")
    expected_hashes = trusted_hashes(repo_root)
    if manifest.get("trusted_hashes") != expected_hashes:
        return fail("trusted file hash mismatch")
    if manifest.get("trusted_closure") != list(expected_hashes.keys()):
        return fail("trusted closure mismatch")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
