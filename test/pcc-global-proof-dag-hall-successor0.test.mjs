import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleDPIndSuccessor0,
} from '../pcc-kbundle-dpind-successor0.mjs';

import {
  makeKBundleHallSuccessor0,
} from '../pcc-kbundle-hall-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGHallFinalTheoremReadiness0,
  CheckGlobalProofDAGHallSuccessor0,
  makeGlobalProofDAGHallSuccessor0,
} from '../pcc-global-proof-dag-hall-successor0.mjs';

const predecessorNodeIds = [
  'K.Eq',
  'K.Subst',
  'K.Record',
  'K.DAGInd',
  'K.LedgerInd',
  'K.OblTopoInd',
  'K.TraceInd',
  'K.FiniteExhaust',
  'K.DPInd',
];

const hallRules = [
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

test('Hall global gate expands the overlay and keeps final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGHallSuccessor0(
    makeGlobalProofDAGHallSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGHallSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.predecessorGlobalFinalNodesQuarantined, true);
  assert.deepEqual(
    out.NF.predecessorGlobalSemanticKernelNodeIds,
    predecessorNodeIds,
  );
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.equal(out.NF.semanticKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, hallRules);
  assert.equal(out.NF.semanticKBundleMissingRules.length, 6);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('Hall'), false);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('RankInd'), true);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    ...predecessorNodeIds,
    'K.Hall',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 6);
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
    'KBundle.HallFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('Hall global gate rejects final-theorem purpose while computed readiness is blocked', async () => {
  const out = await CheckGlobalProofDAGHallSuccessor0(
    makeGlobalProofDAGHallSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGHallSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'Hall successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit Hall global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGHallFinalTheoremReadiness0(
    makeGlobalProofDAGHallSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGHallFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('Hall global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGHallSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGHallSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('Hall global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGHallSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGHallSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('Hall global gate rejects a stale DPInd KBundle', async () => {
  const input = makeGlobalProofDAGHallSuccessor0();
  input.KBundle = makeKBundleDPIndSuccessor0();

  const out = await CheckGlobalProofDAGHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGHallSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'Hall development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'Hall semantic KBundle kind must be KBundleSemanticHallSuccessor0',
  );
});

test('Hall global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGHallSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyHallReadiness = false;

  const out = await CheckGlobalProofDAGHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGHallSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'Hall semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('Hall global gate propagates successor KBundle structural rejection', async () => {
  const bundle = makeKBundleHallSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGHallSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGHallSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'DPInd predecessor global gate rejected the nine-rule semantic base',
  );
});

test('Hall global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGHallSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGHallSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'DPInd predecessor global gate rejected the nine-rule semantic base',
  );
});

test('computed Hall global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGHallSuccessor0(
    makeGlobalProofDAGHallSuccessor0(),
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
    'Gate.KBundle.HallFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.Hall'),
    true,
  );
});
