import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplRankIndSuccessor0,
} from '../pcc-kimpl-rankind-successor0.mjs';

import {
  CheckKBundleMinCounterexampleFinalTheoremReadiness0,
  CheckKBundleMinCounterexampleSuccessor0,
  makeKBundleMinCounterexampleSuccessor0,
} from '../pcc-kbundle-mincounterexample-successor0.mjs';

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
];

const minCounterexampleRules = [
  ...predecessorRules,
  'MinCounterexample',
];

test('MinCounterexample KBundle expands the semantic rule set but remains development-only', async () => {
  const out = await CheckKBundleMinCounterexampleSuccessor0(
    makeKBundleMinCounterexampleSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleMinCounterexampleSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(
    out.NF.semanticKImplSupportedRules,
    minCounterexampleRules,
  );
  assert.equal(out.NF.semanticKImplMissingRules.length, 4);
  assert.equal(
    out.NF.semanticKImplMissingRules.includes('MinCounterexample'),
    false,
  );
  assert.equal(out.NF.semanticKImplMissingRules.includes('IntArith'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplMinCounterexampleFinalTheoremReadiness0',
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

test('MinCounterexample KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleMinCounterexampleSuccessor0(
    makeKBundleMinCounterexampleSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit MinCounterexample KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleMinCounterexampleFinalTheoremReadiness0(
    makeKBundleMinCounterexampleSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('MinCounterexample KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleMinCounterexampleSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleSuccessor0.input',
  );
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('MinCounterexample KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleMinCounterexampleSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleSuccessor0.input',
  );
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('MinCounterexample KBundle rejects a stale RankInd-only child KImpl', async () => {
  const input = makeKBundleMinCounterexampleSuccessor0();
  input.SemanticKImpl = makeKImplRankIndSuccessor0();

  const out = await CheckKBundleMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleSuccessor0.semanticKImpl',
  );
  assert.equal(
    out.Witness.reason,
    'MinCounterexample development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'MinCounterexample successor KImpl kind must be KImplSemanticMinCounterexampleSuccessor0',
  );
});

test('MinCounterexample KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleMinCounterexampleSuccessor0();
  input.Policy.predecessorKBundleCannotImplyMinCounterexampleReadiness = false;

  const out = await CheckKBundleMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleSuccessor0.input',
  );
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic KBundle release policy must match the fail-closed policy',
  );
});

test('MinCounterexample KBundle propagates Sigma structural rejection through the RankInd predecessor boundary', async () => {
  const input = makeKBundleMinCounterexampleSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleMinCounterexampleSuccessor0.predecessorKBundle',
  );
  assert.equal(
    out.Witness.reason,
    'RankInd predecessor KBundle rejected the eleven-rule semantic base',
  );
});

test('MinCounterexample KBundle readiness binds the MinCounterexample final-probe digest', async () => {
  const out = await CheckKBundleMinCounterexampleSuccessor0(
    makeKBundleMinCounterexampleSuccessor0(),
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
    'CheckKImplMinCounterexampleFinalTheoremReadiness0',
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
