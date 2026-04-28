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

