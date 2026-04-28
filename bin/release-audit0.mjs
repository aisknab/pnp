#!/usr/bin/env node

import {
  CheckReleaseAudit0,
} from '../pcc-release-audit0.mjs';

const full = process.argv.includes('--full');

const out = await CheckReleaseAudit0({
  runCliSmoke: false,
});

console.log(JSON.stringify(full ? out : summarizeReleaseAudit0(out), null, 2));

if (out.tag !== 'accept') {
  process.exitCode = 1;
}

function summarizeReleaseAudit0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      moduleCount: out.NF.moduleCount,
      testCount: out.NF.testCount,
      checkerCoverageCount: out.NF.checkerCoverageCount,
      publicConclusion: out.NF.publicConclusion,
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