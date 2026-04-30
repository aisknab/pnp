#!/usr/bin/env node

import path from 'node:path';

import {
  CheckMaterializedFixtureRoundtrip0,
} from '../pcc-materialized-fixture-roundtrip0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const canonical = args.includes('--canonical');
const noCli = args.includes('--no-cli');

const outIndex = args.indexOf('--out');
const outputBase = outIndex >= 0
  ? args[outIndex + 1]
  : args.find((arg) => !arg.startsWith('--'));

const base = outputBase ?? path.join(process.cwd(), 'materialized-roundtrip0');

const out = await CheckMaterializedFixtureRoundtrip0({
  outputDirA: path.join(base, 'a'),
  outputDirB: path.join(base, 'b'),
  canonicalEnvelopeBytes: canonical,
  runCliChecks: !noCli,
});

console.log(JSON.stringify(full ? out : summarizeRoundtrip0(out), null, 2));

if (out.tag !== 'accept') {
  process.exitCode = 1;
}

function summarizeRoundtrip0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      outputDirA: out.NF.outputDirA,
      outputDirB: out.NF.outputDirB,
      fileCount: out.NF.fileCount,
      deterministic: out.NF.deterministic,
      canonicalEnvelopeBytes: out.NF.canonicalEnvelopeBytes,
      directRecordCount: out.NF.directRecords.length,
      cliRecordCount: out.NF.cliRecords.length,
      digest: out.Digest,
    };
  }

  return {
    tag: out.tag,
    checker: out.checker,
    coord: out.Coord,
    path: out.Path,
    witness: out.Witness,
    digest: out.Digest,
  };
}