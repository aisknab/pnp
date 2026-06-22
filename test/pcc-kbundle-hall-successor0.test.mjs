import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplDPIndSuccessor0,
} from '../pcc-kimpl-dpind-successor0.mjs';

import {
  CheckKBundleHallFinalTheoremReadiness0,
  CheckKBundleHallSuccessor0,
  makeKBundleHallSuccessor0,
} from '../pcc-kbundle-hall-successor0.mjs';

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
];

const hallRules = [...predecessorRules, 'Hall'];

test('Hall KBundle expands the semantic rule set but remains development-only', async () => {
  const out = await CheckKBundleHallSuccessor0(
    makeKBundleHallSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleHallSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, hallRules);
  assert.equal(out.NF.semanticKImplMissingRules.length, 6);
  assert.equal(out.NF.semanticKImplMissingRules.includes('Hall'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('RankInd'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplHallFinalTheoremReadiness0',
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

test('Hall KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleHallSuccessor0(
    makeKBundleHallSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleHallSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit Hall KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleHallFinalTheoremReadiness0(
    makeKBundleHallSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleHallFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('Hall KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleHallSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleHallSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('Hall KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleHallSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleHallSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('Hall KBundle rejects a stale DPInd-only child KImpl', async () => {
  const input = makeKBundleHallSuccessor0();
  input.SemanticKImpl = makeKImplDPIndSuccessor0();

  const out = await CheckKBundleHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleHallSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'Hall development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'Hall successor KImpl kind must be KImplSemanticHallSuccessor0',
  );
});

test('Hall KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleHallSuccessor0();
  input.Policy.predecessorKBundleCannotImplyHallReadiness = false;

  const out = await CheckKBundleHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleHallSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic KBundle release policy must match the fail-closed policy',
  );
});

test('Hall KBundle propagates Sigma structural rejection through the DPInd predecessor boundary', async () => {
  const input = makeKBundleHallSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleHallSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'DPInd predecessor KBundle rejected the nine-rule semantic base',
  );
});

test('Hall KBundle readiness binds the Hall final-probe digest', async () => {
  const out = await CheckKBundleHallSuccessor0(
    makeKBundleHallSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  const blocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(
    blocker.digest.hex,
    out.NF.semanticKImplFinalProbeDigest.hex,
  );
  assert.equal(blocker.checker, 'CheckKImplHallFinalTheoremReadiness0');
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
