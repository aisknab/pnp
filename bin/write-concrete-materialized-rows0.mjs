#!/usr/bin/env node

import {
  writeConcreteMaterializedRowsFiles0,
} from '../pcc-rows-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-rows0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedRowsFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    rowCount: result.checked.NF.rowCount,
    concreteIfaceHash: result.checked.NF.concreteIfaceHash,
    syntheticIfaceHashCount: result.checked.NF.syntheticIfaceHashCount,
    scaffoldMarkerCount: result.checked.NF.scaffoldMarkerCount,
    files: result.files,
  }, null, 2));
}
