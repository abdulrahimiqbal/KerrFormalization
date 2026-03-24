from __future__ import annotations

from pathlib import Path
import json
import subprocess
import sys

from freeze_manifest_shared import (
    EXPORTED_THEOREMS,
    MANIFEST_PATH,
    TRUSTED_CLOSURE,
    dependency_revs,
    load_lake_manifest,
    trusted_hashes,
)


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    git_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo_root, text=True
    ).strip()
    lean_toolchain = (repo_root / "lean-toolchain").read_text().strip()
    lake_manifest = load_lake_manifest(repo_root / "lake-manifest.json")
    manifest = {
        "version": 1,
        "repo_root": str(repo_root),
        "git_commit": git_commit,
        "lean_toolchain": lean_toolchain,
        "dependency_revs": dependency_revs(lake_manifest),
        "trusted_closure": TRUSTED_CLOSURE,
        "trusted_hashes": trusted_hashes(repo_root),
        "exported_theorems": EXPORTED_THEOREMS,
    }
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
