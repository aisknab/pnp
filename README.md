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

