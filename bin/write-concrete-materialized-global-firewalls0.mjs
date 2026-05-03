#!/usr/bin/env node

import {
  writeConcreteMaterializedGlobalFirewallsFiles0,
} from '../pcc-global-firewalls-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-global-firewalls0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedGlobalFirewallsFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    phases: result.checked.NF.phases,
    syntheticMarkerCount: result.checked.NF.syntheticMarkerCount,
    forbiddenMarkerCount: result.checked.NF.forbiddenMarkerCount,
    files: result.files,
  }, null, 2));
}
