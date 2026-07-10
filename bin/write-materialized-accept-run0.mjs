#!/usr/bin/env node

import { EnforceHistoricalReplayCli0 } from '../pcc-legacy-replay-gate0.mjs';

import {
  writeMaterializedGeneratedAcceptRunFiles0,
} from '../pcc-accept-run-materialized0.mjs';

EnforceHistoricalReplayCli0({ entrypoint: 'bin/write-materialized-accept-run0.mjs' });

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-accept-run0';
const full = args.includes('--full');

const result = await writeMaterializedGeneratedAcceptRunFiles0(outDir, {
  historicalReplay: true,
});

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    finalVerdictDigest: result.finalVerdict.Digest,
    files: result.files,
  }, null, 2));
}
