# Final PNP proof-report artefacts

Source commit: `37f1b2e38f6be8b2ecad1c3d447d6ed369882e63`
Source tag: `final-pnp-proof-report-37f1b2e`

This directory contains the materialized JSON artefacts emitted by:

```bash
npm run validate
node ./bin/write-final-pnp-proof-report0.mjs proof-artifacts/final-pnp-proof-report-37f1b2e/compact
node ./bin/write-final-pnp-proof-report0.mjs proof-artifacts/final-pnp-proof-report-37f1b2e/full --full
```

A valid reproduction must produce an accepted `CheckFinalPNPProofReport0` record whose theorem field is:

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The central digest ledger is in `release-seal.json`; file-level SHA256 checksums are in `SHA256SUMS`.

If repository access is restricted, request source and artefact access from pnp@keaton.com.au.
