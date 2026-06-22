import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleMinCounterexampleSuccessor0,
} from '../pcc-kbundle-mincounterexample-successor0.mjs';

import {
  makeKBundleIntArithSuccessor0,
} from '../pcc-kbundle-intarith-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGIntArithFinalTheoremReadiness0,
  CheckGlobalProofDAGIntArithSuccessor0,
  makeGlobalProofDAGIntArithSuccessor0,
} from '../pcc-global-proof-dag-intarith-successor0.mjs';

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
];

const intArithRules = [
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
];

test('IntArith global gate expands the overlay and keeps final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGIntArithSuccessor0(
    makeGlobalProofDAGIntArithSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGIntArithSuccessor0');
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
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, intArithRules);
  assert.equal(out.NF.semanticKBundleMissingRules.length, 3);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('IntArith'), false);
  assert.equal(out.NF.semanticKBundleMissingRules.includes('Transport'), true);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    ...predecessorNodeIds,
    'K.IntArith',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 3);
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
    'KBundle.IntArithFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('IntArith global gate rejects final-theorem purpose while computed readiness is blocked', async () => {
  const out = await CheckGlobalProofDAGIntArithSuccessor0(
    makeGlobalProofDAGIntArithSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGIntArithSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'IntArith successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit IntArith global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGIntArithFinalTheoremReadiness0(
    makeGlobalProofDAGIntArithSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGIntArithFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('IntArith global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGIntArithSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('IntArith global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGIntArithSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('IntArith global gate rejects a stale MinCounterexample KBundle', async () => {
  const input = makeGlobalProofDAGIntArithSuccessor0();
  input.KBundle = makeKBundleMinCounterexampleSuccessor0();

  const out = await CheckGlobalProofDAGIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGIntArithSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'IntArith development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'IntArith semantic KBundle kind must be KBundleSemanticIntArithSuccessor0',
  );
});

test('IntArith global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGIntArithSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyIntArithReadiness = false;

  const out = await CheckGlobalProofDAGIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'IntArith semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('IntArith global gate propagates successor KBundle structural rejection', async () => {
  const bundle = makeKBundleIntArithSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGIntArithSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGIntArithSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample predecessor global gate rejected the twelve-rule semantic base',
  );
});

test('IntArith global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGIntArithSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGIntArithSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample predecessor global gate rejected the twelve-rule semantic base',
  );
});

test('computed IntArith global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGIntArithSuccessor0(
    makeGlobalProofDAGIntArithSuccessor0(),
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
    'Gate.KBundle.IntArithFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.IntArith'),
    true,
  );
});
