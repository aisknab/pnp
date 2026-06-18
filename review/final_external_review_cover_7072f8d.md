# Final External Review Cover: Residual-Hardened 7072f8d PNP Release

Status: **external hostile-review package locked**.

This cover note identifies the frozen release artefacts, the public theorem boundary, and the first mathematical surfaces that reviewers should attack. It is not a substitute for mathematical review.

## Public theorem boundary

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The release does not ask reviewers to accept an ungated `P = NP` claim before checking the generated-package acceptance path. The public conclusion is asserted only at the accepted proof-report boundary.

## Frozen identifiers

```text
source commit:
7072f8d0bda6d44d240f9bb3fad624fd357e1278

source tag:
final-pnp-proof-report-hardened-7072f8d

artifact JSON commit:
9526d5de8bdfc3f6f9d3d462044db18ba306cf2f

sealed artifact commit:
9d1de19f827e5cb6880741352eb2349cbbb45994

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-7072f8d-sealed

canonical document commit:
3ba356c79b545d2c734283bf10d85d0710de2b60

canonical document tag:
final-pnp-proof-report-docs-hardened-7072f8d-sealed

artifact bundle:
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/

validation:
1121 tests, 1121 pass, 0 fail, 0 cancelled
```

## Frozen checksum anchors

```text
release-seal.json file checksum:
03a95ff0baeb5b251577780ecbce51e9b305fb611daddee4db9b05f2621d6bc7

SHA256SUMS detached checksum:
d1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356

compact proof-report summary canonical digest:
6b67a24b4139041f67c4228482d097bfe2552943d782991c75288bd5135478c0

full proof-report check-record digest:
ef07f27dcb0bd5c0b115cc7ff22109522f916859a2319265ab552ee6a6243a43

CheckPCCPackexp0 record digest:
62f688bc16c26d9400f7c3c309f266beeb8836519572dd72b3b57f5446a3f1e0
```

## Minimal independent reproduction

```bash
git clone https://github.com/aisknab/pnp.git pnp-review
cd pnp-review
git fetch --tags --force

git checkout final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-7072f8d
sha256sum -c "$BUNDLE/SHA256SUMS"
sha256sum -c "$BUNDLE/SHA256SUMS.sha256"

git checkout final-pnp-proof-report-hardened-7072f8d
npm ci
npm run validate
```

Expected validation summary:

```text
tests 1121
pass 1121
fail 0
cancelled 0
```

## Primary review documents

```text
canonical_proof_report.pdf
canonical_proof_report.tex
REPRODUCE.md
REVIEWER_MAP.md

review/external_review_handoff_7072f8d.md
review/final_external_review_cover_7072f8d.md
review/hostile_review_checklist_7072f8d.md
review/locked_nand_threshold_hostile_review_round1.md
review/residual_band_zeroslack_hostile_review_round1.md
```

## Attack order

1. Locked NAND threshold theorem.
2. Terminal MuBridge and whole-span cheaper-word descent.
3. SaturatePositive and exposure routing.
4. BCEL-ready positive nucleus construction.
5. BN2 side-tight coherent optima.
6. BN3 finite request-envelope joint realizability.
7. BN4 activation-exact cancellation.
8. BN5/PkgC localization and singletonization.
9. BN6 packet collapse and selector completeness.
10. Realizer/HB closure.
11. ZeroSlack final contradiction and certificate-size closure.
12. Final theorem boundary and no-claim-before-accept discipline.

## What counts as a useful hostile report

A useful report should identify one of:

```text
a false lemma;
a missing proof obligation;
a counterexample circuit or support;
a selector packet not represented by K2/K3/Ksp;
a positive residual-slack case that still reaches ZeroSlack;
a quotient-mode equality used constructively in full mode;
a hidden minimization call;
a stale proof reference;
an accepted tamper fixture that should reject;
a public P = NP conclusion before the accepted package/replay/certificate boundary.
```

Use this format:

```text
claim attacked:
file / theorem / checker:
minimal counterexample or missing obligation:
expected acceptance behavior:
actual acceptance behavior:
suggested patch:
```

## Current status

This is an external-review-ready release candidate, not a substitute for independent mathematical verification. The remaining gate toward a serious Clay submission is hostile mathematical review by people who did not write the proof and who are specifically asked to find a counterexample or missing obligation.
