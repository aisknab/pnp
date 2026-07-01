# Historical report supersession audit

Current coordinate:

```text
PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/HISTORICAL_REPORT_SUPERSESSION.json
```

Checker:

```bash
node pcc-historical-report-supersession0.mjs --json
```

The root historical report files remain present:

```text
canonical_proof_report.tex
canonical_proof_report.pdf
```

Those historical files contain direct theorem-emission wording from the old sealed report path. This audit makes that surface explicit and binds it to the current successor status boundary rather than letting report prose silently define the active public-release state.

## Current scope

```text
historicalReportSupersessionReady = true
historicalDirectTheoremEmissionRepresented = true
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

This audit does not freeze the historical report. A later PR may mutate or replace `canonical_proof_report.tex` and `canonical_proof_report.pdf`; if it does, this manifest and checker should be updated to the new historical-report mode.
