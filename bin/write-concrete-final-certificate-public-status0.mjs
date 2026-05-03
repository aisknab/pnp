#!/usr/bin/env node

import {
  writeConcreteFinalCertificatePublicStatusFiles0,
} from '../pcc-final-certificate-public-status-concrete0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-final-certificate-public-status0';
const full = args.includes('--full');

const result = await writeConcreteFinalCertificatePublicStatusFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    concreteRows: result.checked.NF.concreteRows,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    concreteGlobalFirewalls: result.checked.NF.concreteGlobalFirewalls,
    concreteGlobalProofDAG: result.checked.NF.concreteGlobalProofDAG,
    statusUsesConcreteFinalCertificate: result.checked.NF.statusUsesConcreteFinalCertificate,
    publicConclusionEmitted: result.checked.NF.publicConclusionEmitted,
    certificateDigest: result.checked.NF.certificateDigest,
    finalVerdictDigest: result.checked.NF.finalVerdictDigest,
    files: result.files,
  }, null, 2));
}
