#!/usr/bin/env node

import {
  WriteMaterializedAcceptRunFixtureSet0,
  summarizeMaterializedAcceptRunFixtureWriter0,
} from '../pcc-materialized-accept-run-fixtures0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');

const outIndex = args.indexOf('--out');
const outputDir = outIndex >= 0
  ? args[outIndex + 1]
  : args.find((arg) => !arg.startsWith('--'));

const canonicalEnvelopeBytes = args.includes('--canonical');
const overwrite = !args.includes('--no-overwrite');
const verifyDirect = !args.includes('--no-direct-verify');
const verifyCli = !args.includes('--no-cli-verify');

const record = await WriteMaterializedAcceptRunFixtureSet0({
  ...(outputDir ? { outputDir } : {}),
  canonicalEnvelopeBytes,
  overwrite,
  verifyDirect,
  verifyCli,
});

console.log(JSON.stringify(full ? record : summarizeMaterializedAcceptRunFixtureWriter0(record), null, 2));

if (record.tag !== 'accept') {
  process.exitCode = 1;
}