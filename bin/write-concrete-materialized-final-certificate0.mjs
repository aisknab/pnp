#!/usr/bin/env node

import {
  writeConcreteMaterializedFinalCertificateFiles0,
} from '../pcc-final-certificate-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-final-certificate0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedFinalCertificateFiles0(outDir);

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
    finalCertificateUsesConcreteAcceptRun: result.checked.NF.finalCertificateUsesConcreteAcceptRun,
    pccPackDigest: result.checked.NF.pccPackDigest,
    finalVerdictRecordDigest: result.checked.NF.finalVerdictRecordDigest,
    files: result.files,
  }, null, 2));
}
