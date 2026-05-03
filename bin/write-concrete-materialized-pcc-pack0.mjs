#!/usr/bin/env node

import {
  writeConcreteMaterializedPCCPackFiles0,
} from '../pcc-pack-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-pcc-pack0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedPCCPackFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    concreteKBundle: result.checked.NF.concreteKBundle,
    concreteHardCheck: result.checked.NF.concreteHardCheck,
    concreteRows: result.checked.NF.concreteRows,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    concreteGlobalFirewalls: result.checked.NF.concreteGlobalFirewalls,
    concreteGlobalProofDAG: result.checked.NF.concreteGlobalProofDAG,
    concreteFinalIntegration: result.checked.NF.concreteFinalIntegration,
    pccPackLinkedToFinalTheorem: result.checked.NF.pccPackLinkedToFinalTheorem,
    files: result.files,
  }, null, 2));
}
