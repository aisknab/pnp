import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplDAGIndSuccessor0,
} from '../pcc-kimpl-dagind-successor0.mjs';

import {
  CheckKBundleLedgerIndFinalTheoremReadiness0,
  CheckKBundleLedgerIndSuccessor0,
  makeKBundleLedgerIndSuccessor0,
} from '../pcc-kbundle-ledgerind-successor0.mjs';

test('LedgerInd KBundle accepts only as development-only and expands the semantic rule set', async () => {
  const out = await CheckKBundleLedgerIndSuccessor0(
    makeKBundleLedgerIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleLedgerIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
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
  ]);
  assert.equal(out.NF.semanticKImplMissingRules.length, 11);
  assert.equal(out.NF.semanticKImplMissingRules.includes('LedgerInd'), false);
  assert.equal(out.NF.semanticKImplMissingRules.includes('OblTopoInd'), true);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplLedgerIndFinalTheoremReadiness0',
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
    'CheckKImplLedgerIndFinalTheoremReadiness0',
  );
});

test('LedgerInd KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleLedgerIndSuccessor0(
    makeKBundleLedgerIndSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleLedgerIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit LedgerInd KBundle final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKBundleLedgerIndFinalTheoremReadiness0(
    makeKBundleLedgerIndSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleLedgerIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('LedgerInd KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleLedgerIndSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('LedgerInd KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleLedgerIndSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
  );
});

test('LedgerInd KBundle rejects a stale DAGInd-only child KImpl', async () => {
  const input = makeKBundleLedgerIndSuccessor0();
  input.SemanticKImpl = makeKImplDAGIndSuccessor0();

  const out = await CheckKBundleLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleLedgerIndSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'LedgerInd development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'LedgerInd successor KImpl kind must be KImplSemanticLedgerIndSuccessor0',
  );
});

test('LedgerInd KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleLedgerIndSuccessor0();
  input.Policy.predecessorKBundleCannotImplyLedgerIndReadiness = false;

  const out = await CheckKBundleLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic KBundle release policy must match the fail-closed policy',
  );
});

test('LedgerInd KBundle propagates legacy Sigma structural rejection through the predecessor boundary', async () => {
  const input = makeKBundleLedgerIndSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleLedgerIndSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'phase-6 predecessor KBundle rejected the Eq/Subst/Record/DAGInd base',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'legacy KBundle structural checker rejected',
  );
});

test('LedgerInd KBundle computed readiness is bound to the LedgerInd final-probe digest', async () => {
  const out = await CheckKBundleLedgerIndSuccessor0(
    makeKBundleLedgerIndSuccessor0(),
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
    out.NF.computedReadinessDigest.alg,
    'SHA256',
  );
});
