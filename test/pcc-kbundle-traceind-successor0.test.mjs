import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplOblTopoIndSuccessor0,
} from '../pcc-kimpl-obltopoind-successor0.mjs';

import {
  CheckKBundleTraceIndFinalTheoremReadiness0,
  CheckKBundleTraceIndSuccessor0,
  makeKBundleTraceIndSuccessor0,
} from '../pcc-kbundle-traceind-successor0.mjs';

test('TraceInd KBundle accepts only as development-only and expands the semantic rule set', async () => {
  const out = await CheckKBundleTraceIndSuccessor0(
    makeKBundleTraceIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleTraceIndSuccessor0');
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
  ]);
  assert.equal(out.NF.semanticKImplMissingRules.length, 9);
  assert.equal(out.NF.semanticKImplMissingRules.includes('TraceInd'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('FiniteExhaust'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplTraceIndFinalTheoremReadiness0',
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
    'CheckKImplTraceIndFinalTheoremReadiness0',
  );
});

test('TraceInd KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleTraceIndSuccessor0(
    makeKBundleTraceIndSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTraceIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'TraceInd semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit TraceInd KBundle final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKBundleTraceIndFinalTheoremReadiness0(
    makeKBundleTraceIndSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleTraceIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'TraceInd semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('TraceInd KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleTraceIndSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTraceIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'TraceInd semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('TraceInd KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleTraceIndSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTraceIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'TraceInd semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
  );
});

test('TraceInd KBundle rejects a stale OblTopoInd-only child KImpl', async () => {
  const input = makeKBundleTraceIndSuccessor0();
  input.SemanticKImpl = makeKImplOblTopoIndSuccessor0();

  const out = await CheckKBundleTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTraceIndSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'TraceInd development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'TraceInd successor KImpl kind must be KImplSemanticTraceIndSuccessor0',
  );
});

test('TraceInd KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleTraceIndSuccessor0();
  input.Policy.predecessorKBundleCannotImplyTraceIndReadiness = false;

  const out = await CheckKBundleTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTraceIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'TraceInd semantic KBundle release policy must match the fail-closed policy',
  );
});

test('TraceInd KBundle propagates legacy Sigma structural rejection through the predecessor boundary', async () => {
  const input = makeKBundleTraceIndSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleTraceIndSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd predecessor KBundle rejected the six-rule semantic base',
  );
});

test('TraceInd KBundle computed readiness is bound to the TraceInd final-probe digest', async () => {
  const out = await CheckKBundleTraceIndSuccessor0(
    makeKBundleTraceIndSuccessor0(),
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
