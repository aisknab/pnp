import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  AuditIndependentVerifiersNoSharedCode0,
} from '../scripts/audit-independent-verifiers-no-shared-code.mjs';

async function loadPolicy0() {
  const text = await readFile(new URL('../independent-verifiers/NO_SHARED_CODE_POLICY.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

test('independent verifier no-shared-code audit accepts current repository policy', async () => {
  const out = await AuditIndependentVerifiersNoSharedCode0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.claimStatus, 'independent-verifier-no-shared-code-policy-accepted');
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
  assert.equal(out.noSharedCodePolicy.importsJavaScriptCheckerCode, false);
  assert.equal(out.noSharedCodePolicy.spawnsJavaScriptRuntime, false);
  assert.ok(out.scannedPythonSourceCount >= 2);
});

test('independent verifier no-shared-code audit rejects boundary activation', async () => {
  const policy = await loadPolicy0();
  policy.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditIndependentVerifiersNoSharedCode0({
    policyOverride: policy,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'Policy.ValidationFailed');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('independent verifier no-shared-code audit rejects forbidden Python imports', async () => {
  const out = await AuditIndependentVerifiersNoSharedCode0({
    writeOutput: false,
    sourceTextOverrides: {
      'independent-verifiers/python/verify_minimal_kernel.py': 'import subprocess\n',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PythonImport.Forbidden');
  assert.deepEqual(out.path, ['independent-verifiers/python/verify_minimal_kernel.py', 1]);
});

test('independent verifier no-shared-code audit rejects dynamic execution patterns', async () => {
  const out = await AuditIndependentVerifiersNoSharedCode0({
    writeOutput: false,
    sourceTextOverrides: {
      'independent-verifiers/python/verify_minimal_kernel.py': 'import json\nvalue = eval("1 + 1")\n',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'Source.ForbiddenExecutablePattern');
  assert.deepEqual(out.path, ['independent-verifiers/python/verify_minimal_kernel.py']);
  assert.equal(out.witness.pattern, 'eval(');
});

test('independent verifier no-shared-code audit rejects policy claims of shared JS imports', async () => {
  const policy = await loadPolicy0();
  policy.policy.verifiers[0].importsJavaScriptCheckerCode = true;

  const out = await AuditIndependentVerifiersNoSharedCode0({
    policyOverride: policy,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'Policy.ValidationFailed');
  assert.deepEqual(out.path, ['policy', 'verifiers', 0, 'importsJavaScriptCheckerCode']);
});
