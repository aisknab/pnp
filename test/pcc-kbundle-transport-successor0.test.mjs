import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplIntArithSuccessor0,
} from '../pcc-kimpl-intarith-successor0.mjs';

import {
  CheckKBundleTransportFinalTheoremReadiness0,
  CheckKBundleTransportSuccessor0,
  makeKBundleTransportSuccessor0,
} from '../pcc-kbundle-transport-successor0.mjs';

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
];

const transportRules = [...predecessorRules, 'Transport'];

test('Transport KBundle expands the semantic rule set but remains development-only', async () => {
  const out = await CheckKBundleTransportSuccessor0(
    makeKBundleTransportSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleTransportSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, transportRules);
  assert.equal(out.NF.semanticKImplMissingRules.length, 2);
  assert.equal(out.NF.semanticKImplMissingRules.includes('Transport'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('TruthVec'), true);
  assert.equal(out.NF.semanticKImplMissingRules.includes('FiniteRel'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplTransportFinalTheoremReadiness0',
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

test('Transport KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleTransportSuccessor0(
    makeKBundleTransportSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTransportSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit Transport KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleTransportFinalTheoremReadiness0(
    makeKBundleTransportSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleTransportFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('Transport KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleTransportSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('Transport KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleTransportSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('Transport KBundle rejects a stale IntArith-only child KImpl', async () => {
  const input = makeKBundleTransportSuccessor0();
  input.SemanticKImpl = makeKImplIntArithSuccessor0();

  const out = await CheckKBundleTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTransportSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'Transport development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'Transport successor KImpl kind must be KImplSemanticTransportSuccessor0',
  );
});

test('Transport KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleTransportSuccessor0();
  input.Policy.predecessorKBundleCannotImplyTransportReadiness = false;

  const out = await CheckKBundleTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic KBundle release policy must match the fail-closed policy',
  );
});

test('Transport KBundle propagates Sigma structural rejection through the IntArith predecessor boundary', async () => {
  const input = makeKBundleTransportSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTransportSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'IntArith predecessor KBundle rejected the thirteen-rule semantic base',
  );
});

test('Transport KBundle readiness binds the Transport final-probe digest', async () => {
  const out = await CheckKBundleTransportSuccessor0(
    makeKBundleTransportSuccessor0(),
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
    'CheckKImplTransportFinalTheoremReadiness0',
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
