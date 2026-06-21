import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplLedgerIndSuccessor0,
} from '../pcc-kimpl-ledgerind-successor0.mjs';

import {
  CheckKBundleOblTopoIndFinalTheoremReadiness0,
  CheckKBundleOblTopoIndSuccessor0,
  makeKBundleOblTopoIndSuccessor0,
} from '../pcc-kbundle-obltopoind-successor0.mjs';

test('OblTopoInd KBundle accepts only as development-only and expands the semantic rule set', async () => {
  const out = await CheckKBundleOblTopoIndSuccessor0(
    makeKBundleOblTopoIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleOblTopoIndSuccessor0');
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
  ]);
  assert.equal(out.NF.semanticKImplMissingRules.length, 10);
  assert.equal(out.NF.semanticKImplMissingRules.includes('OblTopoInd'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('TraceInd'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplOblTopoIndFinalTheoremReadiness0',
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
    'CheckKImplOblTopoIndFinalTheoremReadiness0',
  );
});

test('OblTopoInd KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleOblTopoIndSuccessor0(
    makeKBundleOblTopoIndSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleOblTopoIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit OblTopoInd KBundle final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKBundleOblTopoIndFinalTheoremReadiness0(
    makeKBundleOblTopoIndSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleOblTopoIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('OblTopoInd KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleOblTopoIndSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('OblTopoInd KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleOblTopoIndSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
  );
});

test('OblTopoInd KBundle rejects a stale LedgerInd-only child KImpl', async () => {
  const input = makeKBundleOblTopoIndSuccessor0();
  input.SemanticKImpl = makeKImplLedgerIndSuccessor0();

  const out = await CheckKBundleOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleOblTopoIndSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'OblTopoInd successor KImpl kind must be KImplSemanticOblTopoIndSuccessor0',
  );
});

test('OblTopoInd KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleOblTopoIndSuccessor0();
  input.Policy.predecessorKBundleCannotImplyOblTopoIndReadiness = false;

  const out = await CheckKBundleOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic KBundle release policy must match the fail-closed policy',
  );
});

test('OblTopoInd KBundle propagates legacy Sigma structural rejection through the predecessor boundary', async () => {
  const input = makeKBundleOblTopoIndSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleOblTopoIndSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'LedgerInd predecessor KBundle rejected the five-rule semantic base',
  );
});

test('OblTopoInd KBundle computed readiness is bound to the final-probe digest', async () => {
  const out = await CheckKBundleOblTopoIndSuccessor0(
    makeKBundleOblTopoIndSuccessor0(),
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
