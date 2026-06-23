import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplTransportSuccessor0,
} from '../pcc-kimpl-transport-successor0.mjs';

import {
  CheckKBundleTruthVecFinalTheoremReadiness0,
  CheckKBundleTruthVecSuccessor0,
  makeKBundleTruthVecSuccessor0,
} from '../pcc-kbundle-truthvec-successor0.mjs';

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
  'IntArith',
  'Transport',
];

const truthVecRules = [...predecessorRules, 'TruthVec'];

test('TruthVec KBundle expands the semantic rule set but remains development-only', async () => {
  const out = await CheckKBundleTruthVecSuccessor0(
    makeKBundleTruthVecSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleTruthVecSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, truthVecRules);
  assert.deepEqual(out.NF.semanticKImplMissingRules, ['FiniteRel']);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplTruthVecFinalTheoremReadiness0',
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

test('TruthVec KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleTruthVecSuccessor0(
    makeKBundleTruthVecSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTruthVecSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit TruthVec KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleTruthVecFinalTheoremReadiness0(
    makeKBundleTruthVecSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleTruthVecFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('TruthVec KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleTruthVecSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('TruthVec KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleTruthVecSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('TruthVec KBundle rejects a stale Transport-only child KImpl', async () => {
  const input = makeKBundleTruthVecSuccessor0();
  input.SemanticKImpl = makeKImplTransportSuccessor0();

  const out = await CheckKBundleTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTruthVecSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'TruthVec development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'TruthVec successor KImpl kind must be KImplSemanticTruthVecSuccessor0',
  );
});

test('TruthVec KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleTruthVecSuccessor0();
  input.Policy.predecessorKBundleCannotImplyTruthVecReadiness = false;

  const out = await CheckKBundleTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic KBundle release policy must match the fail-closed policy',
  );
});

test('TruthVec KBundle propagates Sigma structural rejection through the Transport predecessor boundary', async () => {
  const input = makeKBundleTruthVecSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTruthVecSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'Transport predecessor KBundle rejected the fourteen-rule semantic base',
  );
});

test('TruthVec KBundle readiness binds the TruthVec final-probe digest', async () => {
  const out = await CheckKBundleTruthVecSuccessor0(
    makeKBundleTruthVecSuccessor0(),
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
    'CheckKImplTruthVecFinalTheoremReadiness0',
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
