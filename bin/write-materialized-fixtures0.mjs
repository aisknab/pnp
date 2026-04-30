#!/usr/bin/env node

import {
  WriteMaterializedFixtureSet0,
  summarizeMaterializedFixtureWriter0,
} from '../pcc-materialized-fixture-writer0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');

const outIndex = args.indexOf('--out');
const outputDir = outIndex >= 0
  ? args[outIndex + 1]
  : args.find((arg) => !arg.startsWith('--'));

const canonicalEnvelopeBytes = args.includes('--canonical');
const overwrite = !args.includes('--no-overwrite');
const verify = !args.includes('--no-verify');

const record = await WriteMaterializedFixtureSet0({
  ...(outputDir ? { outputDir } : {}),
  canonicalEnvelopeBytes,
  overwrite,
  verify,
});

console.log(JSON.stringify(full ? record : summarizeMaterializedFixtureWriter0(record), null, 2));

if (record.tag !== 'accept') {
  process.exitCode = 1;
}