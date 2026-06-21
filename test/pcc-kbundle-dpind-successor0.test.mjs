import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckKBundleDPIndSuccessor0,
  makeKBundleDPIndSuccessor0,
} from '../pcc-kbundle-dpind-successor0.mjs';

test('DPInd KBundle expands the rule set and remains development-only', async () => {
  const out = await CheckKBundleDPIndSuccessor0(makeKBundleDPIndSuccessor0());
  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'development-only');
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, [
    'Eq', 'Subst', 'Record', 'DAGInd', 'LedgerInd',
    'OblTopoInd', 'TraceInd', 'FiniteExhaust',
  ]);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, [
    'Eq', 'Subst', 'Record', 'DAGInd', 'LedgerInd',
    'OblTopoInd', 'TraceInd', 'FiniteExhaust', 'DPInd',
  ]);
  assert.equal(out.NF.semanticKImplMissingRules.length, 7);
  assert.equal(out.NF.semanticKImplMissingRules.includes('DPInd'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('Hall'), true);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, [
    'KImpl.SemanticRuleCoverage',
    'K0.SemanticConformance',
    'Sigma.SemanticDerivations',
    'Reflection.SemanticSoundness',
  ]);
});

test('DPInd KBundle rejects final purpose while readiness is blocked', async () => {
  const out = await CheckKBundleDPIndSuccessor0(
    makeKBundleDPIndSuccessor0({ Purpose: 'final-theorem' }),
  );
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleDPIndSuccessor0.semanticReadiness');
});
