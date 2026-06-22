import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplMinCounterexampleSuccessor0,
} from '../pcc-kimpl-mincounterexample-successor0.mjs';

import {
  CheckKBundleIntArithFinalTheoremReadiness0,
  CheckKBundleIntArithSuccessor0,
  makeKBundleIntArithSuccessor0,
} from '../pcc-kbundle-intarith-successor0.mjs';

const predecessorRules = [
  'Eq',
  'Subst',
  'Record',
  'DAGInd',
  'LedgerInd',
  'OblTopoInd',
  'TraceInd',
  'FiniteExhaust',
  'DPInd',
  'Hall',
  'RankInd',
  'MinCounterexample',
];

const intArithRules = [...predecessorRules, 'IntArith'];

test('IntArith KBundle expands the semantic rule set but remains development-only', async () => {
  const out = await CheckKBundleIntArithSuccessor0(
    makeKBundleIntArithSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleIntArithSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, intArithRules);
  assert.equal(out.NF.semanticKImplMissingRules.length, 3);
  assert.equal(out.NF.semanticKImplMissingRules.includes('IntArith'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('Transport'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplIntArithFinalTheoremReadiness0',
  );
  assert.equal(out.NF.semanticKImplFinalReady, false);
  assert.equal(out.NF.legacyBundleAccepted, true);
  assert.equal(out.NF.legacyConformanceSemanticStatus, 'structural-only');
  assert.equal(out.NF.legacySigmaSemanticStatus, 'registry-shape-only');
  assert.equal(out.NF.legacyReflectionSemanticStatus, 'mapping-shape-only');
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, [
    'KImpl.SemanticRuleCoverage',
    'K0.SemanticConformance',
    'Sigma.SemanticDerivations',
    'Reflection.SemanticSoundness',
  ]);
});

test('IntArith KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleIntArithSuccessor0(
    makeKBundleIntArithSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleIntArithSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit IntArith KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleIntArithFinalTheoremReadiness0(
    makeKBundleIntArithSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleIntArithFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('IntArith KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleIntArithSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('IntArith KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleIntArithSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('IntArith KBundle rejects a stale MinCounterexample-only child KImpl', async () => {
  const input = makeKBundleIntArithSuccessor0();
  input.SemanticKImpl = makeKImplMinCounterexampleSuccessor0();

  const out = await CheckKBundleIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleIntArithSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'IntArith development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'IntArith successor KImpl kind must be KImplSemanticIntArithSuccessor0',
  );
});

test('IntArith KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleIntArithSuccessor0();
  input.Policy.predecessorKBundleCannotImplyIntArithReadiness = false;

  const out = await CheckKBundleIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic KBundle release policy must match the fail-closed policy',
  );
});

test('IntArith KBundle propagates Sigma structural rejection through the MinCounterexample predecessor boundary', async () => {
  const input = makeKBundleIntArithSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleIntArithSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample predecessor KBundle rejected the twelve-rule semantic base',
  );
});

test('IntArith KBundle readiness binds the IntArith final-probe digest', async () => {
  const out = await CheckKBundleIntArithSuccessor0(
    makeKBundleIntArithSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  const blocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(
    blocker.digest.hex,
    out.NF.semanticKImplFinalProbeDigest.hex,
  );
  assert.equal(
    blocker.checker,
    'CheckKImplIntArithFinalTheoremReadiness0',
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
