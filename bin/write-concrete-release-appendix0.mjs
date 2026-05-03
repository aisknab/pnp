#!/usr/bin/env node

import {
  writeConcreteReleaseAppendixFiles0,
} from '../pcc-concrete-release-appendix0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-release-appendix0';
const full = args.includes('--full');

const result = await writeConcreteReleaseAppendixFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    releaseAuditDigest: result.checked.NF.releaseAuditDigest,
    pccPackDigest: result.checked.NF.pccPackDigest,
    finalVerdictDigest: result.checked.NF.finalVerdictDigest,
    certificateDigest: result.checked.NF.certificateDigest,
    concreteRows: result.checked.NF.concreteRows,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    concreteGlobalFirewalls: result.checked.NF.concreteGlobalFirewalls,
    concreteGlobalProofDAG: result.checked.NF.concreteGlobalProofDAG,
    publicConclusion: result.checked.NF.publicConclusion,
    files: result.files,
  }, null, 2));
}
