import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplTraceIndSuccessor0,
} from '../pcc-kimpl-traceind-successor0.mjs';

import {
  CheckKBundleFiniteExhaustFinalTheoremReadiness0,
  CheckKBundleFiniteExhaustSuccessor0,
  makeKBundleFiniteExhaustSuccessor0,
} from '../pcc-kbundle-finiteexhaust-successor0.mjs';

test('FiniteExhaust KBundle accepts only as development-only and expands the semantic rule set', async () => {
  const out = await CheckKBundleFiniteExhaustSuccessor0(
    makeKBundleFiniteExhaustSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleFiniteExhaustSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
    'TraceInd',
  ]);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
    'TraceInd',
    'FiniteExhaust',
  ]);
  assert.equal(out.NF.semanticKImplMissingRules.length, 8);
  assert.equal(out.NF.semanticKImplMissingRules.includes('FiniteExhaust'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('DPInd'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplFiniteExhaustFinalTheoremReadiness0',
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
  const kimplBlocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(
    kimplBlocker.checker,
    'CheckKImplFiniteExhaustFinalTheoremReadiness0',
  );
});

test('FiniteExhaust KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleFiniteExhaustSuccessor0(
    makeKBundleFiniteExhaustSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteExhaustSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit FiniteExhaust KBundle final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKBundleFiniteExhaustFinalTheoremReadiness0(
    makeKBundleFiniteExhaustSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleFiniteExhaustFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('FiniteExhaust KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleFiniteExhaustSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteExhaustSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('FiniteExhaust KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleFiniteExhaustSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteExhaustSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
  );
});

test('FiniteExhaust KBundle rejects a stale TraceInd-only child KImpl', async () => {
  const input = makeKBundleFiniteExhaustSuccessor0();
  input.SemanticKImpl = makeKImplTraceIndSuccessor0();

  const out = await CheckKBundleFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteExhaustSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'FiniteExhaust successor KImpl kind must be KImplSemanticFiniteExhaustSuccessor0',
  );
});

test('FiniteExhaust KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleFiniteExhaustSuccessor0();
  input.Policy.predecessorKBundleCannotImplyFiniteExhaustReadiness = false;

  const out = await CheckKBundleFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteExhaustSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust semantic KBundle release policy must match the fail-closed policy',
  );
});

test('FiniteExhaust KBundle propagates legacy Sigma structural rejection through the predecessor boundary', async () => {
  const input = makeKBundleFiniteExhaustSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteExhaustSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'TraceInd predecessor KBundle rejected the seven-rule semantic base',
  );
});

test('FiniteExhaust KBundle computed readiness is bound to the final-probe digest', async () => {
  const out = await CheckKBundleFiniteExhaustSuccessor0(
    makeKBundleFiniteExhaustSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  const blocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(
    blocker.digest.hex,
    out.NF.semanticKImplFinalProbeDigest.hex,
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
