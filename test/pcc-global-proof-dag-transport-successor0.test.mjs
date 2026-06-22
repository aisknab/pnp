import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleIntArithSuccessor0,
} from '../pcc-kbundle-intarith-successor0.mjs';

import {
  makeKBundleTransportSuccessor0,
} from '../pcc-kbundle-transport-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGTransportFinalTheoremReadiness0,
  CheckGlobalProofDAGTransportSuccessor0,
  makeGlobalProofDAGTransportSuccessor0,
} from '../pcc-global-proof-dag-transport-successor0.mjs';

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
];

const transportRules = [
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
];

test('Transport global gate expands the overlay and keeps final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGTransportSuccessor0(
    makeGlobalProofDAGTransportSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGTransportSuccessor0');
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
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, transportRules);
  assert.equal(out.NF.semanticKBundleMissingRules.length, 2);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('Transport'), false);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('TruthVec'), true);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('FiniteRel'), true);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    ...predecessorNodeIds,
    'K.Transport',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 2);
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
    'KBundle.TransportFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('Transport global gate rejects final-theorem purpose while computed readiness is blocked', async () => {
  const out = await CheckGlobalProofDAGTransportSuccessor0(
    makeGlobalProofDAGTransportSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGTransportSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'Transport successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit Transport global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGTransportFinalTheoremReadiness0(
    makeGlobalProofDAGTransportSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGTransportFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('Transport global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGTransportSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('Transport global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGTransportSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('Transport global gate rejects a stale IntArith KBundle', async () => {
  const input = makeGlobalProofDAGTransportSuccessor0();
  input.KBundle = makeKBundleIntArithSuccessor0();

  const out = await CheckGlobalProofDAGTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTransportSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'Transport development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'Transport semantic KBundle kind must be KBundleSemanticTransportSuccessor0',
  );
});

test('Transport global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGTransportSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyTransportReadiness = false;

  const out = await CheckGlobalProofDAGTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'Transport semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('Transport global gate propagates successor KBundle structural rejection', async () => {
  const bundle = makeKBundleTransportSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGTransportSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTransportSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'IntArith predecessor global gate rejected the thirteen-rule semantic base',
  );
});

test('Transport global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGTransportSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGTransportSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'IntArith predecessor global gate rejected the thirteen-rule semantic base',
  );
});

test('computed Transport global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGTransportSuccessor0(
    makeGlobalProofDAGTransportSuccessor0(),
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
    'Gate.KBundle.TransportFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.Transport'),
    true,
  );
});
