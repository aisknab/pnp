# pnp

Core JavaScript utilities for p=np verification experiments.

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

The release audit checks the public package surface, package exports, README claim boundary, stale duplicate ES modules under `src`, orphaned tests, syntax of checker modules, deterministic repeated `RunAll0` execution, and mutation safety of the synthetic full-stack input.

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

