#!/usr/bin/env node

import {
  writeConcreteMaterializedLocalPackagesFiles0,
} from '../pcc-local-packages-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-local-packages0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedLocalPackagesFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    concreteRows: result.checked.NF.concreteRows,
    packageCount: result.checked.NF.packageCount,
    familyCount: result.checked.NF.familyCount,
    syntheticMarkerCount: result.checked.NF.syntheticMarkerCount,
    forbiddenMarkerCount: result.checked.NF.forbiddenMarkerCount,
    files: result.files,
  }, null, 2));
}
