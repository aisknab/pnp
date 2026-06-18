#!/usr/bin/env node

import {
  RunAll0,
} from '../pcc-runall0.mjs';

const full = process.argv.includes('--full');
const out = await RunAll0();

const payload = full
  ? out
  : summarizeRunAll0(out);

console.log(JSON.stringify(payload, null, 2));

if (out.tag !== 'accept') {
  process.exitCode = 1;
}

function summarizeRunAll0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      status: out.NF.status,
      claimBoundary: out.NF.claimBoundary,
      finalVerdict: out.NF.finalVerdict,
      publicConclusionEmitted: out.NF.publicConclusionEmitted,
      publicConclusion: out.NF.publicConclusion,
      checkerCount: out.NF.checkerCount,
      phaseCount: out.NF.phaseCount,
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