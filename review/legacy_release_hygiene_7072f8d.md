# Legacy Release Hygiene for the 7072f8d Review Package

> **Historical assertion-checker record:** This file documents a superseded checker/release surface.
> It is not current theorem-status authority and does not establish `P = NP`. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

At the time of the frozen release, the reviewer-facing tree was intentionally limited to the residual-hardened 7072f8d package.

That historical reviewer package named these entrypoints:

```text
CURRENT_RELEASE.md
REPRODUCE.md
REVIEWER_MAP.md
canonical_proof_report.pdf
review/final_external_review_cover_7072f8d.md
review/hostile_review_checklist_7072f8d.md
review/submission_readiness_memo_7072f8d.md
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

Other release material remained recoverable through git history and historical tags but was not part of that frozen reviewer package. The current main-branch authority is the formal-reconstruction status linked above.
