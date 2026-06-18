#!/usr/bin/env node

import {
  writeConcreteMaterializedKBundleFiles0,
} from '../pcc-k-concrete-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-materialized-kbundle0';
const full = args.includes('--full');

const result = await writeConcreteMaterializedKBundleFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    kernelRuleCoverageComplete: result.checked.NF.kernelRuleCoverageComplete,
    sigmaProofRefsResolve: result.checked.NF.sigmaProofRefsResolve,
    reflectionProofRefsResolve: result.checked.NF.reflectionProofRefsResolve,
    noOpaqueProofRefs: result.checked.NF.noOpaqueProofRefs,
    noExecutableMinSymbols: result.checked.NF.noExecutableMinSymbols,
    files: result.files,
  }, null, 2));
}
