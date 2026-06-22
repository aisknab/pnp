import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplHallSuccessor0,
} from '../pcc-kimpl-hall-successor0.mjs';

import {
  CheckKBundleRankIndFinalTheoremReadiness0,
  CheckKBundleRankIndSuccessor0,
  makeKBundleRankIndSuccessor0,
} from '../pcc-kbundle-rankind-successor0.mjs';

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
];

const rankIndRules = [...predecessorRules, 'RankInd'];

test('RankInd KBundle expands the semantic rule set but remains development-only', async () => {
  const out = await CheckKBundleRankIndSuccessor0(
    makeKBundleRankIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleRankIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, rankIndRules);
  assert.equal(out.NF.semanticKImplMissingRules.length, 5);
  assert.equal(out.NF.semanticKImplMissingRules.includes('RankInd'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('MinCounterexample'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplRankIndFinalTheoremReadiness0',
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

test('RankInd KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleRankIndSuccessor0(
    makeKBundleRankIndSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleRankIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'RankInd semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit RankInd KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleRankIndFinalTheoremReadiness0(
    makeKBundleRankIndSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleRankIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'RankInd semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('RankInd KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleRankIndSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleRankIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'RankInd semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('RankInd KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleRankIndSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleRankIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('RankInd KBundle rejects a stale Hall-only child KImpl', async () => {
  const input = makeKBundleRankIndSuccessor0();
  input.SemanticKImpl = makeKImplHallSuccessor0();

  const out = await CheckKBundleRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleRankIndSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'RankInd development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'RankInd successor KImpl kind must be KImplSemanticRankIndSuccessor0',
  );
});

test('RankInd KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleRankIndSuccessor0();
  input.Policy.predecessorKBundleCannotImplyRankIndReadiness = false;

  const out = await CheckKBundleRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleRankIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'RankInd semantic KBundle release policy must match the fail-closed policy',
  );
});

test('RankInd KBundle propagates Sigma structural rejection through the Hall predecessor boundary', async () => {
  const input = makeKBundleRankIndSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleRankIndSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'Hall predecessor KBundle rejected the ten-rule semantic base',
  );
});

test('RankInd KBundle readiness binds the RankInd final-probe digest', async () => {
  const out = await CheckKBundleRankIndSuccessor0(
    makeKBundleRankIndSuccessor0(),
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
    'CheckKImplRankIndFinalTheoremReadiness0',
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
