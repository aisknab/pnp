#!/usr/bin/env node

import { EnforceHistoricalReplayCli0 } from '../pcc-legacy-replay-gate0.mjs';

import {
  WriteMaterializedFinalRunFixtureSet0,
  summarizeMaterializedFinalRunFixtureWriter0,
} from '../pcc-materialized-final-run-fixtures0.mjs';

EnforceHistoricalReplayCli0({ entrypoint: 'bin/write-materialized-final-run-fixtures0.mjs' });

const args = process.argv.slice(2);
const full = args.includes('--full');

const outIndex = args.indexOf('--out');
const outputDir = outIndex >= 0
  ? args[outIndex + 1]
  : args.find((arg) => !arg.startsWith('--'));

const canonicalEnvelopeBytes = args.includes('--canonical');
const overwrite = !args.includes('--no-overwrite');
const verifyAcceptRunWriter = !args.includes('--no-accept-run-writer-verify');
const verifyDirect = !args.includes('--no-direct-verify');
const verifyCli = !args.includes('--no-cli-verify');

const record = await WriteMaterializedFinalRunFixtureSet0({
    historicalReplay: true,
  ...(outputDir ? { outputDir } : {}),
  canonicalEnvelopeBytes,
  overwrite,
  verifyAcceptRunWriter,
  verifyDirect,
  verifyCli,
});

console.log(JSON.stringify(full ? record : summarizeMaterializedFinalRunFixtureWriter0(record), null, 2));

if (record.tag !== 'accept') {
  process.exitCode = 1;
}
