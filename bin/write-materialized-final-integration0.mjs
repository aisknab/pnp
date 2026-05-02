#!/usr/bin/env node

import {
  writeMaterializedFinalIntegrationFiles0,
} from '../pcc-final-integration-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-final-integration0';
const full = args.includes('--full');

const result = await writeMaterializedFinalIntegrationFiles0(outDir);

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
