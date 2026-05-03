#!/usr/bin/env node

import {
  writeReleaseAuditConcreteFinalCertificateGateFiles0,
} from '../pcc-release-audit-final-certificate-concrete-gate0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './release-audit-concrete-final-certificate-gate0';
const full = args.includes('--full');

const result = await writeReleaseAuditConcreteFinalCertificateGateFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    releaseAuditDigest: result.checked.NF.releaseAuditDigest,
    concreteRows: result.checked.NF.concreteRows,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    concreteGlobalFirewalls: result.checked.NF.concreteGlobalFirewalls,
    concreteGlobalProofDAG: result.checked.NF.concreteGlobalProofDAG,
    certificateDigest: result.checked.NF.certificateDigest,
    finalVerdictDigest: result.checked.NF.finalVerdictDigest,
    pccPackDigest: result.checked.NF.pccPackDigest,
    publicConclusion: result.checked.NF.publicConclusion,
    files: result.files,
  }, null, 2));
}
