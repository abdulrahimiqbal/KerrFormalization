# Frozen Kernel Submission Rule

This directory is the Phase I submission envelope for Aristotle batches.

Rules:
- Use only the frozen trusted closure listed in `manifest.json`.
- Do not rebuild or substitute live repo dependencies outside that closure.
- Cite only theorem names listed in `manifest.json`.
- Treat the manifest as the submission contract: if a source hash, toolchain, or dependency rev changes, the batch is no longer valid.
