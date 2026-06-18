#!/usr/bin/env node

import {
  writeConcreteMaterializedHardFiles0,
} from '../pcc-hard-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-hard0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedHardFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    checkerCoverageComplete: result.checked.NF.checkerCoverageComplete,
    rowKeyCoverageComplete: result.checked.NF.rowKeyCoverageComplete,
    routePriorityComplete: result.checked.NF.routePriorityComplete,
    proofRefPolicyComplete: result.checked.NF.proofRefPolicyComplete,
    hashDisciplineComplete: result.checked.NF.hashDisciplineComplete,
    noMinCoverageComplete: result.checked.NF.noMinCoverageComplete,
    importPolicyComplete: result.checked.NF.importPolicyComplete,
    diagnosticsPolicyComplete: result.checked.NF.diagnosticsPolicyComplete,
    files: result.files,
  }, null, 2));
}
