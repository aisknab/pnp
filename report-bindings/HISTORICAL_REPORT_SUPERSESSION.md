# Historical report supersession audit

Current coordinate:

```text
PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01
```

Sanitized root report coordinate:

```text
PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/HISTORICAL_REPORT_SUPERSESSION.json
```

Checker:

```bash
node pcc-historical-report-supersession0.mjs --json
```

The root canonical report files are now sanitized status notices:

```text
canonical_proof_report.tex
canonical_proof_report.pdf
```

Earlier sealed-report artifacts and earlier revisions of these root report files contained direct theorem-emission wording. This audit now checks the current root TeX and PDF for required successor-boundary fragments and rejects if old direct theorem-emission fragments reappear.

## Current scope

```text
historicalReportSupersessionReady = true
historicalReportSanitizedReady = true
historicalDirectTheoremEmissionRepresented = false
historicalDirectTheoremEmissionSanitized = true
currentRootReportSanitized = true
currentPdfSanitized = true
currentBoundarySupersedesHistoricalEmission = true
publicTheoremEmissionAllowedBySupersession = false
```

## Boundary

The active status boundary remains:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

This audit does not rewrite earlier sealed tags or earlier durable artifact bundles. It only sanitizes the current root report surface and keeps earlier direct theorem-emission prose superseded by the current non-activation boundary.
