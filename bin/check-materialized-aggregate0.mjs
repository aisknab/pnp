#!/usr/bin/env node

import {
  CheckMaterializedAggregateFile0,
} from '../pcc-materialized-aggregate0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const requireCanonicalEnvelopeBytes = args.includes('--canonical-envelope-bytes');
const filePath = args.find((arg) => !arg.startsWith('--'));

if (!filePath) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'check-materialized-aggregate0',
    coord: 'check-materialized-aggregate0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/check-materialized-aggregate0.mjs <MaterializedPCCPack0.json> [--full] [--canonical-envelope-bytes]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await CheckMaterializedAggregateFile0(filePath, {
    loaderConfig: {
      requireCanonicalEnvelopeBytes,
    },
  });

  console.log(JSON.stringify(full ? out : summarizeMaterializedAggregate0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function summarizeMaterializedAggregate0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      filePath: out.NF.filePath,
      byteLength: out.NF.byteLength,
      phaseCount: out.NF.phaseCount,
      packDigest: out.NF.packDigest,
      aggregateDigest: out.NF.aggregateDigest,
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