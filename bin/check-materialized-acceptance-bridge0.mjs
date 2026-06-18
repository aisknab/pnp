#!/usr/bin/env node

import {
  CheckMaterializedAcceptanceBridgeFile0,
} from '../pcc-materialized-acceptance-bridge0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const filePath = args.find((arg) => !arg.startsWith('--'));

if (!filePath) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'check-materialized-acceptance-bridge0',
    coord: 'check-materialized-acceptance-bridge0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/check-materialized-acceptance-bridge0.mjs <MaterializedAcceptanceBridge0.json> [--full]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await CheckMaterializedAcceptanceBridgeFile0(filePath);

  console.log(JSON.stringify(full ? out : summarizeMaterializedAcceptanceBridge0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function summarizeMaterializedAcceptanceBridge0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      filePath: out.NF.filePath,
      byteLength: out.NF.byteLength,
      replayVerdict: out.NF.replayVerdict,
      publicConclusionEmitted: out.NF.publicConclusionEmitted,
      bridgeDigest: out.NF.bridgeDigest,
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