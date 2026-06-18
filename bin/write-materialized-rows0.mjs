#!/usr/bin/env node

import {
  writeMaterializedRowsFiles0,
} from '../pcc-rows-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-rows0';
const full = args.includes('--full');

const result = await writeMaterializedRowsFiles0(outDir);

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
