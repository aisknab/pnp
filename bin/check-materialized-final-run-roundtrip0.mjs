#!/usr/bin/env node

import {
  CheckMaterializedFinalRunRoundtrip0,
} from '../pcc-materialized-final-run-roundtrip0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const canonical = args.includes('--canonical');
const noCli = args.includes('--no-cli');

const outIndex = args.indexOf('--out');
const outputDir = outIndex >= 0
  ? args[outIndex + 1]
  : args.find((arg) => !arg.startsWith('--'));

const out = await CheckMaterializedFinalRunRoundtrip0({
  ...(outputDir ? { outputDir } : {}),
  canonicalEnvelopeBytes: canonical,
  runCliChecks: !noCli,
});

console.log(JSON.stringify(full ? out : summarizeFinalRunRoundtrip0(out), null, 2));

if (out.tag !== 'accept') {
  process.exitCode = 1;
}

function summarizeFinalRunRoundtrip0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      outputDir: out.NF.outputDir,
      fileCount: out.NF.fileCount,
      deterministic: out.NF.deterministic,
      acceptedPublicConclusionOnly: out.NF.acceptedPublicConclusionOnly,
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