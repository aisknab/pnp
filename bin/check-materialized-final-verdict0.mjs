#!/usr/bin/env node

import {
  CheckMaterializedFinalVerdictFile0,
} from '../pcc-materialized-final-verdict0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const filePath = args.find((arg) => !arg.startsWith('--'));

if (!filePath) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'check-materialized-final-verdict0',
    coord: 'check-materialized-final-verdict0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/check-materialized-final-verdict0.mjs <MaterializedAcceptRun0.json> [--full]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await CheckMaterializedFinalVerdictFile0(filePath);

  console.log(JSON.stringify(full ? out : summarizeMaterializedFinalVerdict0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function summarizeMaterializedFinalVerdict0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      filePath: out.NF.filePath,
      byteLength: out.NF.byteLength,
      verdict: out.NF.verdict,
      replayAccepted: out.NF.replayAccepted,
      publicConclusionEmitted: out.NF.publicConclusionEmitted,
      publicConclusion: out.NF.publicConclusion,
      claimBoundary: out.NF.claimBoundary,
      rejectLogCount: out.NF.rejectLogCount,
      generatedPackagePath: out.NF.generatedPackagePath,
      aggregateDigest: out.NF.aggregateDigest,
      transcriptDigest: out.NF.transcriptDigest,
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