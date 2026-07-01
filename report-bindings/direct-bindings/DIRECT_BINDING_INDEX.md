# Section 22 direct-binding index

Current coordinate:

```text
PNP-DIRECT-BINDING-INDEX-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/DIRECT_BINDING_INDEX.json
```

Checker:

```bash
node pcc-direct-binding-index0.mjs --json
```

This index collects the executable surfaces for all 27 historical Section 22 theorem-ledger rows. It is an index and consistency layer, not a theorem-activation layer.

The index verifies that every inventory row has a corresponding coverage row, closure-plan row, direct-binding manifest, checker file, and test file. It also verifies that all row surfaces preserve the current public-review boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The index intentionally records mixed row states. Some rows are direct-binding seeds, some are gap-transition seeds, G is a locked-NAND threshold seed, and Final/PACK are release-boundary seeds. None of these rows may flip `directCheckerBindingComplete` or discharge public theorem emission through this index.
