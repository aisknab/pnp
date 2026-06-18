#!/usr/bin/env node

import {
  writeConcreteMaterializedFinalIntegrationFiles0,
} from '../pcc-final-integration-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-final-integration0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedFinalIntegrationFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    concreteGlobalProofDAG: result.checked.NF.concreteGlobalProofDAG,
    concreteKBundle: result.checked.NF.concreteKBundle,
    concreteRows: result.checked.NF.concreteRows,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    concreteGlobalFirewalls: result.checked.NF.concreteGlobalFirewalls,
    gpackFieldCoverageComplete: result.checked.NF.gpackFieldCoverageComplete,
    rowFamGCoverageComplete: result.checked.NF.rowFamGCoverageComplete,
    finalIntegrationUsesGPack: result.checked.NF.finalIntegrationUsesGPack,
    files: result.files,
  }, null, 2));
}
