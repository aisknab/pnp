import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleLedgerIndSuccessor0,
} from '../pcc-kbundle-ledgerind-successor0.mjs';

import {
  makeKBundleOblTopoIndSuccessor0,
} from '../pcc-kbundle-obltopoind-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGOblTopoIndFinalTheoremReadiness0,
  CheckGlobalProofDAGOblTopoIndSuccessor0,
  makeGlobalProofDAGOblTopoIndSuccessor0,
} from '../pcc-global-proof-dag-obltopoind-successor0.mjs';

test('OblTopoInd global gate accepts the legacy graph only as development-only', async () => {
  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(
    makeGlobalProofDAGOblTopoIndSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGOblTopoIndSuccessor0');
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
    'K.LedgerInd',
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
    'OblTopoInd',
  ]);
  assert.equal(out.NF.semanticKBundleMissingRules.length, 10);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('OblTopoInd'), false);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('TraceInd'), true);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    'K.Eq',
    'K.Subst',
    'K.Record',
    'K.DAGInd',
    'K.LedgerInd',
    'K.OblTopoInd',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 10);
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
    'KBundle.OblTopoIndFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('OblTopoInd global gate rejects final-theorem purpose while computed gate is blocked', async () => {
  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(
    makeGlobalProofDAGOblTopoIndSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGOblTopoIndSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit OblTopoInd global final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckGlobalProofDAGOblTopoIndFinalTheoremReadiness0(
    makeGlobalProofDAGOblTopoIndSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGOblTopoIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('OblTopoInd global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGOblTopoIndSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('OblTopoInd global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGOblTopoIndSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
  );
});

test('OblTopoInd global gate rejects a stale LedgerInd KBundle', async () => {
  const input = makeGlobalProofDAGOblTopoIndSuccessor0();
  input.KBundle = makeKBundleLedgerIndSuccessor0();

  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGOblTopoIndSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'OblTopoInd semantic KBundle kind must be KBundleSemanticOblTopoIndSuccessor0',
  );
});

test('OblTopoInd global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGOblTopoIndSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyOblTopoIndReadiness = false;

  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('OblTopoInd global gate propagates successor KBundle rejection', async () => {
  const bundle = makeKBundleOblTopoIndSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGOblTopoIndSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGOblTopoIndSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'LedgerInd predecessor global gate rejected the five-rule semantic base',
  );
});

test('OblTopoInd global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGOblTopoIndSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGOblTopoIndSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'LedgerInd predecessor global gate rejected the five-rule semantic base',
  );
});

test('computed OblTopoInd global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGOblTopoIndSuccessor0(
    makeGlobalProofDAGOblTopoIndSuccessor0(),
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
    'Gate.KBundle.OblTopoIndFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.OblTopoInd'),
    true,
  );
});
