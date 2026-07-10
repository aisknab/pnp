# Quick replay of the historical legacy-v0 release

> **Historical replay only:** This file describes the superseded 7072f8d assertion-checker release.
> Reproduction verifies historical bytes and implemented predicate behavior. It does not establish
> `P = NP` and does not change the current formal-reconstruction status. See
> [`status/FORMAL_RECONSTRUCTION_STATUS.json`](../../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`docs/FORMAL_RECONSTRUCTION.md`](../../docs/FORMAL_RECONSTRUCTION.md).

The supported launcher on current `main` is:

```bash
npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d
```

It verifies immutable tag identities before running anything from the pinned source checkout.
Run it in a disposable, secret-free environment without repository write credentials; restrict
network access where practical because the operation executes historical JavaScript.

This file describes the reproducibility protocol for the historical hardened proof-report release.

## Historical checker-claim boundary

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

This was the claim boundary recorded by the historical release package. It is not a current theorem
statement or an independently established implication.

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

### Historical 56-page claim manuscript

```text
canonical_proof_report.tex
canonical_proof_report.pdf
```

These filenames identify the 56-page claim manuscript in the pinned legacy source tree. The
historical manuscript is no longer carried at the current repository root: retrieve it only from
the pinned source tag above. Its immutable coordinate is recorded by this archive, but its theorem
wording is not current authority.

The files with those names on current `main` are instead the generated, concise six-page
formal-reconstruction report. That report is derived from the compiled Lean inventory and the
false concrete publication gate; it does not establish `P = NP` or reproduce the historical claim
artifact.

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

## Historical full validation

Run the recorded validation from the pinned source/checker tag. On current `main`, `npm run pnp:verify`
is the conservative formal-reconstruction verifier and must not be interpreted as replay acceptance.

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

## Historical proof-report regeneration

On current `main`, regeneration is an explicit historical replay:

```bash
TMP=/tmp/pnp-proof-report-hardened-repro
rm -rf "$TMP"
mkdir -p "$TMP/compact" "$TMP/full"

node ./bin/write-final-pnp-proof-report0.mjs --historical-replay "$TMP/compact" \
  > "$TMP/final-pnp-proof-report.summary.json"

node ./bin/write-final-pnp-proof-report0.mjs --historical-replay "$TMP/full" --full \
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

Exact release-context digest equality is relevant only to historical byte reproduction. A fresh replay
that reproduces acceptance records remains assertion-checker evidence, not theorem acceptance.

## Historical RunAll smoke

```bash
node --input-type=module <<'NODE'
import { RunAll0 } from './pcc-runall0.mjs';

const out = await RunAll0(undefined, { historicalReplay: true });

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

The executable artifacts are historical assertion-bearing records and checker outputs. They do not
replace a concrete, assumption-audited formal derivation of the reduction, threshold, minimizer,
ZeroSlack result, runtime bounds, and final complexity implication.
