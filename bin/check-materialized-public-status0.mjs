#!/usr/bin/env node

import {
  CheckMaterializedPublicStatusFile0,
} from '../pcc-materialized-public-status0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const filePath = args.find((arg) => !arg.startsWith('--'));

if (!filePath) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'check-materialized-public-status0',
    coord: 'check-materialized-public-status0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/check-materialized-public-status0.mjs <MaterializedAcceptRun0.json> [--full]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await CheckMaterializedPublicStatusFile0(filePath);

  console.log(JSON.stringify(full ? out : summarizeMaterializedPublicStatus0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function summarizeMaterializedPublicStatus0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      materializedPath: out.NF.materializedPath,
      syntheticRunAll: out.NF.syntheticRunAll,
      status: out.NF.status,
      verdict: out.NF.verdict,
      replayAccepted: out.NF.replayAccepted,
      publicConclusionEmitted: out.NF.publicConclusionEmitted,
      publicConclusion: out.NF.publicConclusion,
      claimBoundary: out.NF.claimBoundary,
      acceptRunFilePath: out.NF.acceptRunFilePath,
      generatedPackagePath: out.NF.generatedPackagePath,
      rejectLogCount: out.NF.rejectLogCount,
      acceptRunDigest: out.NF.acceptRunDigest,
      finalVerdictDigest: out.NF.finalVerdictDigest,
      aggregateDigest: out.NF.aggregateDigest,
      transcriptDigest: out.NF.transcriptDigest,
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