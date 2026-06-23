import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleTransportSuccessor0,
} from '../pcc-kbundle-transport-successor0.mjs';

import {
  makeKBundleTruthVecSuccessor0,
} from '../pcc-kbundle-truthvec-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGTruthVecFinalTheoremReadiness0,
  CheckGlobalProofDAGTruthVecSuccessor0,
  makeGlobalProofDAGTruthVecSuccessor0,
} from '../pcc-global-proof-dag-truthvec-successor0.mjs';

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
  'K.MinCounterexample',
  'K.IntArith',
  'K.Transport',
];

const truthVecRules = [
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
  'TruthVec',
];

test('TruthVec global gate expands the overlay and keeps final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGTruthVecSuccessor0(
    makeGlobalProofDAGTruthVecSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGTruthVecSuccessor0');
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
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, truthVecRules);
  assert.deepEqual(out.NF.semanticKBundleMissingRules, ['FiniteRel']);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    ...predecessorNodeIds,
    'K.TruthVec',
  ]);
  assert.deepEqual(out.NF.semanticOverlay.blockedKernelNodeIds, ['K.FiniteRel']);
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
    'KBundle.TruthVecFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('TruthVec global gate rejects final-theorem purpose while computed readiness is blocked', async () => {
  const out = await CheckGlobalProofDAGTruthVecSuccessor0(
    makeGlobalProofDAGTruthVecSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGTruthVecSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'TruthVec successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit TruthVec global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGTruthVecFinalTheoremReadiness0(
    makeGlobalProofDAGTruthVecSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGTruthVecFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('TruthVec global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGTruthVecSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('TruthVec global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGTruthVecSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('TruthVec global gate rejects a stale Transport KBundle', async () => {
  const input = makeGlobalProofDAGTruthVecSuccessor0();
  input.KBundle = makeKBundleTransportSuccessor0();

  const out = await CheckGlobalProofDAGTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTruthVecSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'TruthVec development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'TruthVec semantic KBundle kind must be KBundleSemanticTruthVecSuccessor0',
  );
});

test('TruthVec global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGTruthVecSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyTruthVecReadiness = false;

  const out = await CheckGlobalProofDAGTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'TruthVec semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('TruthVec global gate propagates successor KBundle structural rejection', async () => {
  const bundle = makeKBundleTruthVecSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGTruthVecSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTruthVecSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'Transport predecessor global gate rejected the fourteen-rule semantic base',
  );
});

test('TruthVec global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGTruthVecSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTruthVecSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'Transport predecessor global gate rejected the fourteen-rule semantic base',
  );
});

test('computed TruthVec global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGTruthVecSuccessor0(
    makeGlobalProofDAGTruthVecSuccessor0(),
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
    'Gate.KBundle.TruthVecFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.TruthVec'),
    true,
  );
});
