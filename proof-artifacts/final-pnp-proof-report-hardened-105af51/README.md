# Hardened final PNP proof-report artefact bundle

Source/checker revision:

- source commit: 105af516128fa0f7cc9978e6381bb6d8afdc7058
- source tag: final-pnp-proof-report-hardened-105af51

Generated artefact revision before metadata seal:

- artefact JSON commit: 82e1a234a5a589c96c64dc12b2dd285e4b7d9b30
- prior artefact tag, if present: final-pnp-proof-report-artifacts-hardened-105af51

Sealed artefact release:

- sealed artefact tag: final-pnp-proof-report-artifacts-hardened-105af51-sealed
- bundle path: proof-artifacts/final-pnp-proof-report-hardened-105af51

Public theorem boundary:

```
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

Validation summary for this hardened release candidate:

```
tests=984
pass=984
fail=0
cancelled=0
skipped=0
todo=0
```

Verification modes:

1. Artefact verification checks this committed bundle against SHA256SUMS.
   SHA256SUMS does not contain a self-entry.
2. Regeneration verification reruns the proof-report writer and checks that
   CheckFinalPNPProofReport0 accepts with theorem statement P = NP and antecedent
   CheckPCCPackexp(GeneratePCCPack())=accept.
3. Exact release-context digest equality is required only when regenerating in
   the same clean release context.
