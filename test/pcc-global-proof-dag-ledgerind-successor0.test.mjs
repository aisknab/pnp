import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSemanticSuccessor0,
} from '../pcc-kbundle-semantic-successor0.mjs';

import {
  makeKBundleLedgerIndSuccessor0,
} from '../pcc-kbundle-ledgerind-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGLedgerIndFinalTheoremReadiness0,
  CheckGlobalProofDAGLedgerIndSuccessor0,
  makeGlobalProofDAGLedgerIndSuccessor0,
} from '../pcc-global-proof-dag-ledgerind-successor0.mjs';

test('LedgerInd global gate accepts structural legacy graph only as development-only', async () => {
  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(
    makeGlobalProofDAGLedgerIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGLedgerIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.predecessorGlobalFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.predecessorGlobalSemanticKernelNodeIds, [
    'K.Eq',
    'K.Subst',
    'K.Record',
    'K.DAGInd',
  ]);
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.equal(out.NF.semanticKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
  ]);
  assert.equal(out.NF.semanticKBundleMissingRules.length, 11);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('LedgerInd'), false);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('OblTopoInd'), true);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    'K.Eq',
    'K.Subst',
    'K.Record',
    'K.DAGInd',
    'K.LedgerInd',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 11);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.equal(out.NF.legacyFinalNodesStructurallyAccepted, true);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, [
    'Final.PackageSoundness',
    'Final.GeneratedPackageSufficiency',
    'Final.AcceptedPackageImpliesSATinP',
    'Final.AcceptedPackageImpliesPEqualsNP',
  ]);
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'KBundle.LedgerIndFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('LedgerInd global gate rejects final-theorem purpose while computed gate is blocked', async () => {
  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(
    makeGlobalProofDAGLedgerIndSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGLedgerIndSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit LedgerInd global final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckGlobalProofDAGLedgerIndFinalTheoremReadiness0(
    makeGlobalProofDAGLedgerIndSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGLedgerIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('LedgerInd global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGLedgerIndSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('LedgerInd global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGLedgerIndSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
  );
});

test('LedgerInd global gate rejects a stale phase-6 KBundle', async () => {
  const input = makeGlobalProofDAGLedgerIndSuccessor0();
  input.KBundle = makeKBundleSemanticSuccessor0();

  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGLedgerIndSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'LedgerInd development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'LedgerInd semantic KBundle kind must be KBundleSemanticLedgerIndSuccessor0',
  );
});

test('LedgerInd global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGLedgerIndSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyLedgerIndReadiness = false;

  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('LedgerInd global gate propagates successor KBundle rejection', async () => {
  const bundle = makeKBundleLedgerIndSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGLedgerIndSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGLedgerIndSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'phase-6 predecessor global gate rejected the Eq/Subst/Record/DAGInd base',
  );
});

test('LedgerInd global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGLedgerIndSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGLedgerIndSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'phase-6 predecessor global gate rejected the Eq/Subst/Record/DAGInd base',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'legacy global proof DAG structural checker rejected',
  );
});

test('computed LedgerInd global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGLedgerIndSuccessor0(
    makeGlobalProofDAGLedgerIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(
    out.NF.computedGlobalGate.semanticKBundleComputedReadinessDigest.hex,
    out.NF.semanticKBundleComputedReadinessDigest.hex,
  );
  const finalGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.FinalTheorem.Readiness',
  );
  assert.equal(finalGate.ready, false);
  assert.deepEqual(finalGate.premises, [
    'Gate.KBundle.LedgerIndFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  const ledgerNode = out.NF.semanticOverlay.semanticKernelNodeIds.find(
    (id) => id === 'K.LedgerInd',
  );
  assert.equal(ledgerNode, 'K.LedgerInd');
});
