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
