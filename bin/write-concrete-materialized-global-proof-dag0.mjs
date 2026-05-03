#!/usr/bin/env node

import {
  writeConcreteMaterializedGlobalProofDAGFiles0,
} from '../pcc-global-proof-dag-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-global-proof-dag0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedGlobalProofDAGFiles0(outDir);

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
    nodeCount: result.checked.NF.nodeCount,
    syntheticMarkerCount: result.checked.NF.syntheticMarkerCount,
    forbiddenMarkerCount: result.checked.NF.forbiddenMarkerCount,
    files: result.files,
  }, null, 2));
}
