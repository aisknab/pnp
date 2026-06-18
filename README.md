# pnp

Core JavaScript utilities for p=np verification experiments.

## Independent review status

As of 18 June 2026, Edward Savage is the only contacted reviewer who provided substantive technical feedback. No contacted reviewer has independently confirmed, reproduced, validated, endorsed, or formally rejected the claimed result.

External-review status is tracked in [EXTERNAL_REVIEW_STATUS.md](./EXTERNAL_REVIEW_STATUS.md). Outreach records are not proof evidence, and silence should not be interpreted as acceptance, rejection, or an assessment of the claim.

## Requirements

- Node.js 20 or newer
- npm 10 or newer

## Install

```sh
npm install
```

## Usage

```js
import {
  makeMinimalBootstrapContext,
  name,
  digestObject0,
} from '@aisknab/pnp';

const ctx = makeMinimalBootstrapContext();
const digest = digestObject0(ctx, name('example'));
```

The primary module is [`pcc-core.mjs`](./pcc-core.mjs). It exports codec helpers, canonicalization utilities, digest functions, row-key validation helpers, route checks, and a minimal bootstrap context.

## Scripts

```sh
npm run check
npm test
npm run validate
```

## Public RunAll0 entry point

The public entry point is `RunAll0`.

```bash
npm run smoke
```

For the full replay record:

```bash
npm run smoke:full
```

The emitted public conclusion is conditional:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

The generator is untrusted. The checker validates the materialized package, compares canonical bytes rather than digest equality, and emits a public `P = NP` conclusion only after the final replay accepts. A reject run emits a replayable first failure and no public theorem conclusion.

The package entry point is:

```js
import { RunAll0 } from '@aisknab/pnp';

const out = await RunAll0();
console.log(out.tag, out.NF.publicConclusion);
```

## Release audit

Run the release audit after the public smoke test:

```bash
npm run release:audit
```

For the full release audit record:

```bash
npm run release:audit:full
```

The release audit checks the public package surface, package exports, README claim boundary, orphaned tests, syntax of checker modules, deterministic repeated `RunAll0` execution, mutation safety of the synthetic full-stack input, the public surface freeze phase, and the materialized public-status release gate.

## Internal materialized package path

The materialized path is separate from synthetic `RunAll0` fixtures. It is for checking external JSON envelopes that represent future real generated proof artefacts.

The current internal file-based flow is:

```text
MaterializedPCCPack0.json
  -> CheckMaterializedPCCPackShell0
  -> ExtractMaterializedCore0
  -> CheckMaterializedPhaseManifest0
  -> CheckMaterializedArtefactInventory0
  -> CheckMaterializedArtefactDeps0
  -> CheckMaterializedProofRefs0
  -> CheckMaterializedBounds0
  -> CheckMaterializedNoHiddenMin0
  -> CheckMaterializedImports0
  -> CheckMaterializedAggregate0
```

Run a shell check:

```bash
npm run materialized:shell -- ./path/to/MaterializedPCCPack0.json
```

Run the full aggregate check:

```bash
npm run materialized:aggregate -- ./path/to/MaterializedPCCPack0.json
```

Run the full aggregate check with complete output:

```bash
npm run materialized:aggregate:full -- ./path/to/MaterializedPCCPack0.json
```

The materialized acceptance bridge is separate. It verifies that a public conclusion is emitted only when both the materialized package precondition and the external replay are accepted.

```bash
npm run materialized:bridge -- ./path/to/MaterializedAcceptanceBridge0.json
npm run materialized:bridge:full -- ./path/to/MaterializedAcceptanceBridge0.json
```

The bridge must not emit `P = NP` unless:

```text
CheckPCCPackexp status = accepted
ExternalAcceptRunReplay verdict = accept
```

The public claim boundary remains conditional:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

## Internal materialized fixture writer

The internal materialized fixture writer emits example external JSON files that can be checked by the materialized path scripts.

A materialized fixture digest can be resolved only against known written fixture files:

npm run materialized:resolve-digest -- <sha256-hex> --dir ./materialized-fixtures0

This is a checked reverse lookup over indexed fixture bytes. It is not cryptographic inversion.

```bash
npm run materialized:write-fixtures -- ./materialized-fixtures0
```

This writes:

```text
MaterializedPCCPack0.json
MaterializedAcceptanceBridge.pending0.json
MaterializedAcceptanceBridge.accepted0.json
```

The generated files are engineering fixtures. They are useful for validating the external materialized checker path. They are not a proof package acceptance claim.

A canonical-envelope version can be written with:

```bash
npm run materialized:write-fixtures -- ./materialized-fixtures0 --canonical
```

## Internal materialized accept-run check

The materialized accept-run checker reads an external `MaterializedAcceptRun0.json` file. It validates the generated package reference, aggregate check digest, replay transcript, audit logs, first-failure log, verdict, and public claim boundary.

```bash
npm run materialized:accept-run -- ./path/to/MaterializedAcceptRun0.json
npm run materialized:accept-run:full -- ./path/to/MaterializedAcceptRun0.json
```

The accept-run envelope must not embed `Pgen`, `CoreBytes`, or `PackBytes`. It refers to the generated package by file path and checks the materialized aggregate digest.

A public conclusion is emitted only when:

```text
ReplayTranscript.verdict = accept
ReplayTranscript.replayAccepted = true
```

For `pending` or `reject`, no public `P = NP` conclusion is emitted.

## Internal materialized accept-run fixture writer

The internal materialized accept-run fixture writer emits a package fixture and three accept-run envelopes:

```bash
npm run materialized:write-accept-runs -- ./materialized-accept-run-fixtures0
```

This writes:

```text
MaterializedPCCPack0.json
MaterializedAcceptRun.pending0.json
MaterializedAcceptRun.reject0.json
MaterializedAcceptRun.accepted0.json
```

Each accept-run fixture is checked by `CheckMaterializedAcceptRunFile0` and the accept-run CLI. The pending and reject fixtures emit no public conclusion. The accepted fixture records public conclusion emission only after accepted replay.

## Internal materialized final verdict check

The materialized final verdict checker reads an external `MaterializedAcceptRun0.json` file, verifies it through `CheckMaterializedAcceptRunFile0`, and emits the final materialized verdict summary.

```bash
npm run materialized:final-verdict -- ./path/to/MaterializedAcceptRun0.json
npm run materialized:final-verdict:full -- ./path/to/MaterializedAcceptRun0.json
```

The final verdict may be `pending`, `reject`, or `accept`.

For `pending` and `reject`, no public `P = NP` conclusion is emitted. For `accept`, the public conclusion is emitted only after the materialized accept-run replay is accepted.

The claim boundary remains conditional:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

## Internal materialized final-run fixture writer

The internal materialized final-run fixture writer emits final-verdict-ready accept-run envelopes:

```bash
npm run materialized:write-final-runs -- ./materialized-final-run-fixtures0
```

This writes the package fixture and:

```text
MaterializedAcceptRun.pending0.json
MaterializedAcceptRun.reject0.json
MaterializedAcceptRun.accepted0.json
```

Each file is verified through `CheckMaterializedFinalVerdictFile0` and the final verdict CLI.

Pending and reject final-run fixtures emit no public conclusion. The accepted final-run fixture emits the conditional public conclusion only after accepted replay.

## Internal materialized public status check

The materialized public status checker reads an external `MaterializedAcceptRun0.json` file, verifies it through the materialized final verdict checker, and emits a compact materialized-path status record.

```bash
npm run materialized:public-status -- ./path/to/MaterializedAcceptRun0.json
npm run materialized:public-status:full -- ./path/to/MaterializedAcceptRun0.json
```

The materialized public status path is separate from synthetic `RunAll0`.

The status is one of:

```text
pending
rejected
accepted
```

Only `accepted` emits the public conclusion. `pending` and `rejected` emit no public `P = NP` conclusion.

The claim boundary remains conditional:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

## Internal materialized public status release gate

The materialized public status roundtrip command is the internal release gate for the materialized status path.

```bash
npm run materialized:public-status-roundtrip -- ./materialized-public-status-roundtrip0
npm run materialized:public-status-roundtrip:full -- ./materialized-public-status-roundtrip0
```

It writes final-run fixtures, compares repeated fixture bytes for determinism, checks the package fixture through the materialized aggregate checker, and checks pending, rejected, and accepted accept-run files through the materialized public status checker.

The gate verifies:

```text
pending  -> no public P = NP conclusion
rejected -> no public P = NP conclusion
accepted -> emits the conditional public conclusion
```

This path is separate from synthetic `RunAll0`. It is an external materialized-file path for future generated package candidates.

The claim boundary remains conditional:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

## Release audit materialized gate flags

The release audit CLI can explicitly include or skip the materialized public status gate.

```bash
npm run release:audit -- --materialized-gate
npm run release:audit -- --no-materialized-gate
npm run release:audit:full -- --materialized-gate
```

The materialized gate can write its temporary fixtures to a chosen directory:

```bash
npm run release:audit -- --materialized-gate --materialized-gate-out ./materialized-public-status-roundtrip0
```

The inner CLI checks can be disabled for a faster local structural check:

```bash
npm run release:audit -- --materialized-gate --no-materialized-gate-cli
```

The materialized gate remains separate from synthetic `RunAll0`. It verifies deterministic external-file fixtures and the rule that only accepted replay emits the conditional public conclusion.

## Release audit materialized gate summary

The release audit normal form and CLI summary expose the materialized public status gate result.

The summary includes:

```text
materializedPublicStatusGateDigest
materializedPublicStatusGateFileCount
materializedPublicStatusGateDirectRecordCount
materializedPublicStatusGateCliRecordCount
materializedPublicStatusGateAcceptedPublicConclusionOnly
```

When the gate is enabled, the release audit requires the materialized path to prove:

```text
deterministic repeated fixture bytes
materializedPath = true
syntheticRunAll = false
acceptedPublicConclusionOnly = true
```

This makes the materialized public-status release gate visible in the final release audit artefact rather than only present as an internal ledger phase.

## Release audit surface freeze

The release audit normal form and CLI summary have a frozen key surface. The surface freeze is checked by the release audit itself.

The frozen normal form keys include:

```text
kind
checker
version
rootDir
moduleCount
testCount
requiredExports
requiredScripts
checkerCoverageCount
materializedPublicStatusGate
materializedPublicStatusGateSummary
materializedPublicStatusGateDigest
materializedPublicStatusGateFileCount
materializedPublicStatusGateDirectRecordCount
materializedPublicStatusGateCliRecordCount
materializedPublicStatusGateAcceptedPublicConclusionOnly
publicConclusion
```

The frozen CLI summary exposes the same materialized gate proof fields plus the release audit digest.

Future changes to the release surface should fail the surface-freeze tests and the `surfaceFreeze` ledger phase unless the frozen key lists are intentionally updated.

## Public entry release surface freeze

The public release surface is frozen by `CheckPublicEntryReleaseSurface0`.

The freeze covers:

```text
index.mjs export names
package.json exports keys and values
package.json bin keys and values
package.json script keys and values
```

The checker rejects missing keys, extra keys, and changed mapping values. This makes accidental changes to the public release surface fail loudly before they can alter the acceptance artefact.

This checker is internal. It freezes the current public entry rather than adding new public exports.

## Release audit public surface freeze phase

The release audit executes the public entry release surface freeze checker as a ledger phase named `publicSurfaceFreeze`.

The phase verifies:

```text
index.mjs public export names
package.json exports map
package.json bin map
package.json script map
```

The phase is separate from the materialized public-status gate. It protects the release API and command surface, while the materialized gate protects the external materialized acceptance path.

The phase can be disabled only by configuration in internal tests. The default release audit enables it.

## Release audit public surface freeze summary

The release audit normal form and CLI summary expose the public surface freeze result.

The summary includes:

```text
publicSurfaceFreezeDigest
publicSurfaceFreezePublicEntryExportCount
publicSurfaceFreezePackageExportCount
publicSurfaceFreezePackageBinCount
publicSurfaceFreezePackageScriptCount
publicSurfaceFreezeSurfaceFrozen
```

When enabled, the release audit requires the public surface freeze checker to prove:

```text
surfaceFrozen = true
index.mjs exports are frozen
package exports are frozen
package bin entries are frozen
package scripts are frozen
```

This makes the public API and command surface freeze visible in the final release audit artefact.

## Release audit public surface freeze negative coverage

The release audit includes negative coverage for the public surface freeze phase.

The negative checks prove that `CheckReleaseAudit0` rejects if the public surface freeze checker returns an accepted record with:

```text
wrong normal-form kind
surfaceFrozen = false
zero public entry export count
zero package export count
zero package bin count
zero package script count
missing normal form
```

All such failures surface at:

```text
CheckReleaseAudit0.publicSurfaceFreeze
```

This makes the public release surface freeze a checked release-audit invariant rather than a passive file inventory entry.

## Release audit phase-order freeze

The release audit ledger phase order is frozen.

The expected order is:

```text
shape
requiredFiles
staleSrc
packageJson
testInventory
readme
syntax
runAllDeterminism
runAllMutation
cliSmoke
publicSurfaceFreeze
materializedPublicStatusGate
surfaceFreeze
```

The `surfaceFreeze` phase validates both the output surface and the phase order. Future phase insertions, deletions, or reorderings should fail loudly unless the frozen phase list is intentionally updated.

## Release audit hard-gate default

The default release audit CLI run executes the public surface freeze and the materialized public-status gate.

```bash
npm run release:audit
npm run release:audit:full
```

For fast local structural checks, use:

```bash
npm run release:audit -- --fast-local
npm run release:audit:full -- --fast-local
```

Fast local mode keeps the public surface freeze enabled and skips only the heavier materialized public-status roundtrip gate.

The explicit gate flags remain available:

```bash
npm run release:audit -- --materialized-gate
npm run release:audit -- --no-materialized-gate
npm run release:audit -- --materialized-gate --materialized-gate-out ./materialized-public-status-roundtrip0
```

## Release audit README wording freeze

The README release-boundary wording is checked by `CheckReadmeReleaseBoundary0`.

The checker freezes the conditional theorem boundary, release audit wording, hard-gate CLI wording, materialized status gate wording, public surface freeze wording, and stale-layout exclusions.

It rejects missing required release-boundary snippets and legacy layout descriptions before they can enter the release audit artefact.

## Release audit README negative integration

The release audit README phase is backed by `CheckReadmeReleaseBoundary0`.

The integration proves that stale layout wording, overclaiming theorem wording, malformed README-boundary normal forms, and disabled README boundary claims reject at:

```text
CheckReleaseAudit0.readme
```

This makes README claim-boundary validation an active release-audit gate rather than passive prose checking.


### Final certificate public-status gate

The final certificate public-status gate records the accepted final certificate while preserving the conditional claim boundary. It reports `finalCertificatePublicStatusGateDigest`, `finalCertificatePublicStatusGateCertificateDigest`, `finalCertificatePublicStatusGateFinalVerdictDigest`, `finalCertificatePublicStatusGateAcceptRunDigest`, and `finalCertificatePublicStatusGatePccPackDigest`.

The gate also exposes canonical-byte roots and acceptance transcript digests. The public theorem statement remains conditional on accepted replay: `CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP`.
