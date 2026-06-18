# Reproducing the Hardened Final PNP Proof-Report Release

This file describes the reproducibility protocol for the hardened final proof-report release.

## Public theorem boundary

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

This is the only public theorem boundary asserted by the release package. The conclusion is conditional on the accepted generated package and the accepted proof-report chain.

## Canonical identifiers

### Source/checker revision

```text
source commit: 7072f8d0bda6d44d240f9bb3fad624fd357e1278
source tag:    final-pnp-proof-report-hardened-7072f8d
```

### Hardened artifact bundle

```text
generated artifact commit before metadata seal:
9526d5de8bdfc3f6f9d3d462044db18ba306cf2f

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-7072f8d-sealed

bundle path:
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

### Current canonical manuscript

```text
canonical_proof_report.tex
canonical_proof_report.pdf
```

The manuscript revision is the current `main` commit that contains the 7072f8d residual-hardened release-seal update to `canonical_proof_report.tex` and `canonical_proof_report.pdf`.

## Toolchain

The release was validated with Node 20.x and npm 10.x. A reviewer should begin with:

```bash
node --version
npm --version
git --version
```

## Clean checkout

```bash
git clone https://github.com/aisknab/pnp.git pnp-review
cd pnp-review
git fetch --tags --force
```

To inspect the source/checker revision:

```bash
git checkout final-pnp-proof-report-hardened-7072f8d
git rev-parse HEAD
```

Expected source commit:

```text
7072f8d0bda6d44d240f9bb3fad624fd357e1278
```

To inspect the sealed artifact release:

```bash
git checkout final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
git rev-parse HEAD
```

The sealed artifact tree must contain:

```text
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/README.md
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/release-seal.json
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS.sha256
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/final-pnp-proof-report.summary.json
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/final-pnp-proof-report.full.json
```

## Artifact checksum verification

From the sealed artifact tag:

```bash
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-7072f8d

sha256sum -c "$BUNDLE/SHA256SUMS"
sha256sum -c "$BUNDLE/SHA256SUMS.sha256"
```

Expected result:

```text
all listed files pass
```

`SHA256SUMS` intentionally has no self-entry. Its checksum is stored in the detached file `SHA256SUMS.sha256`.

## Full validation

From `main` or from the source/checker tag:

```bash
npm ci
npm run validate | tee validate-hardened.log
```

Expected summary:

```text
tests 1121
pass 1121
fail 0
cancelled 0
skipped 0
todo 0
duration_ms 2033521.892701
```

## Targeted hardened-chain tests

A faster reviewer smoke test is:

```bash
node --test test/pcc-gpack0.test.mjs
node --test test/pcc-global-proof-dag0.test.mjs
node --test test/pcc-final-framework0.test.mjs
node --test test/pcc-final0.test.mjs
node --test test/pcc-final-integration-materialized0.test.mjs
node --test test/pcc-final-integration-concrete-materialized0.test.mjs
node --test test/pcc-pack-concrete-materialized0.test.mjs
node --test test/pcc-check-pcc-pack-exp0.test.mjs
node --test test/pcc-integrated-pipeline0.test.mjs
node --test test/pcc-runall0.test.mjs
```

Expected result: all pass.

## Proof-report regeneration

From the source/checker tag or current `main`:

```bash
TMP=/tmp/pnp-proof-report-hardened-repro
rm -rf "$TMP"
mkdir -p "$TMP/compact" "$TMP/full"

node ./bin/write-final-pnp-proof-report0.mjs "$TMP/compact" \
  > "$TMP/final-pnp-proof-report.summary.json"

node ./bin/write-final-pnp-proof-report0.mjs "$TMP/full" --full \
  > "$TMP/final-pnp-proof-report.full.json"
```

The regenerated summary and full record must satisfy:

```text
checker: CheckFinalPNPProofReport0
tag: accept
status: accepted
theorem.statement: P = NP
theorem.antecedent: CheckPCCPackexp(GeneratePCCPack())=accept
publicConclusionStatement: CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
checkPCCPackexpAccepted: true
finalPNPProofReportAccepted: true
```

Exact release-context digest equality is required only when regenerating in the same clean release context. Fresh context regeneration is accepted if it preserves the accepted theorem, accepted package/replay/certificate linkage, and public theorem boundary.

## RunAll public-status smoke

```bash
node --input-type=module <<'NODE'
import { RunAll0 } from './pcc-runall0.mjs';

const out = await RunAll0();

console.log(JSON.stringify({
  tag: out.tag,
  checker: out.checker,
  digest: out.Digest,
  status: out.NF?.status,
  finalVerdict: out.NF?.finalVerdict,
  publicConclusionEmitted: out.NF?.publicConclusionEmitted,
  publicConclusion: out.NF?.publicConclusion,
  checkPCCPackexpAccepted: out.NF?.checkPCCPackexpAccepted,
  checkPCCPackexpPublicConclusionOnlyAfterAcceptRun:
    out.NF?.checkPCCPackexpPublicConclusionOnlyAfterAcceptRun,
  checkPCCPackexpFinalTheoremGLinkageComplete:
    out.NF?.checkPCCPackexpFinalTheoremGLinkageComplete,
  checkPCCPackexpFinalIntegrationGlobalGLinkageComplete:
    out.NF?.checkPCCPackexpFinalIntegrationGlobalGLinkageComplete,
  checkPCCPackexpGlobalProofDAGHasGThresholdProofNode:
    out.NF?.checkPCCPackexpGlobalProofDAGHasGThresholdProofNode,
}, null, 2));
NODE
```

Expected key fields:

```text
tag = accept
finalVerdict = accept
publicConclusionEmitted = true
publicConclusion.consequent = P = NP
checkPCCPackexpAccepted = true
checkPCCPackexpFinalTheoremGLinkageComplete = true
checkPCCPackexpFinalIntegrationGlobalGLinkageComplete = true
checkPCCPackexpGlobalProofDAGHasGThresholdProofNode = true
```

## Reviewer caution

The executable artifacts are a proof-carrying checker package and release-gate package. They do not replace mathematical review of the reduction and threshold proof. A reviewer should separately inspect the locked NAND threshold theorem, the residual-band minimization theorem, the absence of hidden minimization, and the final SAT-in-P implication.
