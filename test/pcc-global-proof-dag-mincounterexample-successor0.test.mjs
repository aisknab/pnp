import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleRankIndSuccessor0,
} from '../pcc-kbundle-rankind-successor0.mjs';

import {
  makeKBundleMinCounterexampleSuccessor0,
} from '../pcc-kbundle-mincounterexample-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGMinCounterexampleFinalTheoremReadiness0,
  CheckGlobalProofDAGMinCounterexampleSuccessor0,
  makeGlobalProofDAGMinCounterexampleSuccessor0,
} from '../pcc-global-proof-dag-mincounterexample-successor0.mjs';

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
  'K.Hall',
  'K.RankInd',
];

const minCounterexampleRules = [
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
];

test('MinCounterexample global gate expands the overlay and keeps final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(
    makeGlobalProofDAGMinCounterexampleSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(
    out.checker,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0',
  );
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
  assert.deepEqual(
    out.NF.semanticKBundleSupportedRules,
    minCounterexampleRules,
  );
  assert.equal(out.NF.semanticKBundleMissingRules.length, 4);
  assert.equal(
    out.NF.semanticKBundleMissingRules.includes('MinCounterexample'),
    false,
  );
  assert.equal(out.NF.semanticKBundleMissingRules.includes('IntArith'), true);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    ...predecessorNodeIds,
    'K.MinCounterexample',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 4);
  assert.equal(
    out.NF.semanticOverlay.globalSemanticNodeDerivationsReady,
    false,
  );
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
    'KBundle.MinCounterexampleFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('MinCounterexample global gate rejects final-theorem purpose while computed readiness is blocked', async () => {
  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(
    makeGlobalProofDAGMinCounterexampleSuccessor0({
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit MinCounterexample global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGMinCounterexampleFinalTheoremReadiness0(
    makeGlobalProofDAGMinCounterexampleSuccessor0({
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('MinCounterexample global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGMinCounterexampleSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.input',
  );
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('MinCounterexample global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGMinCounterexampleSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.input',
  );
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('MinCounterexample global gate rejects a stale RankInd KBundle', async () => {
  const input = makeGlobalProofDAGMinCounterexampleSuccessor0();
  input.KBundle = makeKBundleRankIndSuccessor0();

  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.semanticKBundle',
  );
  assert.equal(
    out.Witness.reason,
    'MinCounterexample development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'MinCounterexample semantic KBundle kind must be KBundleSemanticMinCounterexampleSuccessor0',
  );
});

test('MinCounterexample global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGMinCounterexampleSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyMinCounterexampleReadiness = false;

  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.input',
  );
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('MinCounterexample global gate propagates successor KBundle structural rejection', async () => {
  const bundle = makeKBundleMinCounterexampleSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGMinCounterexampleSuccessor0({
    KBundle: bundle,
  });

  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.predecessorGlobal',
  );
  assert.equal(
    out.Witness.reason,
    'RankInd predecessor global gate rejected the eleven-rule semantic base',
  );
});

test('MinCounterexample global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGMinCounterexampleSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGMinCounterexampleSuccessor0.predecessorGlobal',
  );
  assert.equal(
    out.Witness.reason,
    'RankInd predecessor global gate rejected the eleven-rule semantic base',
  );
});

test('computed MinCounterexample global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGMinCounterexampleSuccessor0(
    makeGlobalProofDAGMinCounterexampleSuccessor0(),
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
    'Gate.KBundle.MinCounterexampleFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes(
      'K.MinCounterexample',
    ),
    true,
  );
});
