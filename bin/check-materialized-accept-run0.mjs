#!/usr/bin/env node

import {
  CheckMaterializedAcceptRunFile0,
} from '../pcc-materialized-accept-run0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const filePath = args.find((arg) => !arg.startsWith('--'));

if (!filePath) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'check-materialized-accept-run0',
    coord: 'check-materialized-accept-run0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/check-materialized-accept-run0.mjs <MaterializedAcceptRun0.json> [--full]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await CheckMaterializedAcceptRunFile0(filePath);

  console.log(JSON.stringify(full ? out : summarizeMaterializedAcceptRun0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function summarizeMaterializedAcceptRun0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      filePath: out.NF.filePath,
      byteLength: out.NF.byteLength,
      verdict: out.NF.verdict,
      replayAccepted: out.NF.replayAccepted,
      publicConclusionEmitted: out.NF.publicConclusionEmitted,
      acceptRunDigest: out.NF.acceptRunDigest,
      fileDigest: out.NF.fileDigest,
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