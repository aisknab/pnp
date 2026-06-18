#!/usr/bin/env node

import {
  writeMaterializedGlobalProofDAGFiles0,
} from '../pcc-global-proof-dag-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-global-proof-dag0';
const full = args.includes('--full');

const result = await writeMaterializedGlobalProofDAGFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    files: result.files,
  }, null, 2));
}
