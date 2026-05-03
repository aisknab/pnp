#!/usr/bin/env node

import {
  writeConcreteMaterializedGeneratedAcceptRunFiles0,
} from '../pcc-accept-run-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-accept-run0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedGeneratedAcceptRunFiles0(outDir);

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
    pccPackLinkedToAcceptRun: result.checked.NF.pccPackLinkedToAcceptRun,
    files: result.files,
  }, null, 2));
}
