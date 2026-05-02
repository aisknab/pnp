#!/usr/bin/env node

import {
  writeMaterializedScaffoldBurndownFiles0,
} from '../pcc-materialized-scaffold-burndown0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-scaffold-burndown0';
const full = args.includes('--full');

const result = await writeMaterializedScaffoldBurndownFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    status: result.checked.NF.status,
    strictReady: result.checked.NF.strictReady,
    markerHitCount: result.checked.NF.markerHitCount,
    syntheticMarkerCount: result.checked.NF.syntheticMarkerCount,
    forbiddenMarkerCount: result.checked.NF.forbiddenMarkerCount,
    files: result.files,
  }, null, 2));
}
