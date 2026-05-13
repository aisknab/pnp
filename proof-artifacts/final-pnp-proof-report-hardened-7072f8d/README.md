# Hardened final PNP proof-report artefact bundle

Source/checker revision:

- source commit: 7072f8d0bda6d44d240f9bb3fad624fd357e1278
- source tag: final-pnp-proof-report-hardened-7072f8d

Generated artefact JSON commit before metadata seal:

- 9526d5de8bdfc3f6f9d3d462044db18ba306cf2f

Sealed artefact release:

- sealed artefact tag: final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
- bundle path: proof-artifacts/final-pnp-proof-report-hardened-7072f8d

Public theorem boundary:

```
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

Validation summary for this hardened release candidate:

```
tests=1121
pass=1121
fail=0
cancelled=0
skipped=0
todo=0
duration_ms=2033521.892701
```

This release follows the residual-band hardening pass through Terminal MuBridge,
SaturatePositive, BCEL-ready residual witnesses, BN2, BN3, BN4, BN5/PkgC, BN6,
Realizer/HB closure, and ZeroSlack final closure.

Verification modes:

1. Artefact verification checks this committed bundle against SHA256SUMS.
   SHA256SUMS does not contain a self-entry.
2. Regeneration verification reruns the proof-report writer and checks that
   CheckFinalPNPProofReport0 accepts with theorem statement P = NP and antecedent
   CheckPCCPackexp(GeneratePCCPack())=accept.
3. Exact release-context digest equality is required only when regenerating in
   the same clean release context.
