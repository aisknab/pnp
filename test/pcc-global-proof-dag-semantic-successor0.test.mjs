import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSemanticSuccessor0,
} from '../pcc-kbundle-semantic-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGSemanticFinalTheoremReadiness0,
  CheckGlobalProofDAGSemanticSuccessor0,
  makeGlobalProofDAGSemanticSuccessor0,
} from '../pcc-global-proof-dag-semantic-successor0.mjs';

test('semantic global DAG accepts structural legacy graph only as development-only', async () => {
  const out = await CheckGlobalProofDAGSemanticSuccessor0(
    makeGlobalProofDAGSemanticSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGSemanticSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.equal(out.NF.semanticKBundlePublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.equal(out.NF.legacyFinalNodesStructurallyAccepted, true);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, [
    'Final.PackageSoundness',
    'Final.GeneratedPackageSufficiency',
    'Final.AcceptedPackageImpliesSATinP',
    'Final.AcceptedPackageImpliesPEqualsNP',
  ]);
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    'K.Eq',
    'K.Subst',
    'K.Record',
    'K.DAGInd',
  ]);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 12);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'KBundle.FinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('semantic global DAG rejects final-theorem purpose while computed gate is blocked', async () => {
  const out = await CheckGlobalProofDAGSemanticSuccessor0(
    makeGlobalProofDAGSemanticSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGSemanticSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit semantic global final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckGlobalProofDAGSemanticFinalTheoremReadiness0(
    makeGlobalProofDAGSemanticSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGSemanticFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('semantic global DAG rejects caller-supplied readiness assertions', async () => {
  const input = makeGlobalProofDAGSemanticSuccessor0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSemanticSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('semantic global DAG rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeGlobalProofDAGSemanticSuccessor0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSemanticSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
  );
});

test('semantic global DAG rejects a weakened final-node quarantine policy', async () => {
  const input = makeGlobalProofDAGSemanticSuccessor0();
  input.Policy.legacyFinalNodesQuarantinedUntilSemanticGateAccepts = false;

  const out = await CheckGlobalProofDAGSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSemanticSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('semantic global DAG propagates successor KBundle rejection', async () => {
  const bundle = makeKBundleSemanticSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGSemanticSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSemanticSuccessor0.semanticKBundle');
  assert.equal(out.Witness.reason, 'development semantic KBundle rejected');
});

test('semantic global DAG propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGSemanticSuccessor0({
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSemanticSuccessor0.legacyGlobalDAG');
  assert.equal(
    out.Witness.reason,
    'legacy global proof DAG structural checker rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'GlobalProofDAG0 is missing a required final theorem node',
  );
});

test('computed global gate binds the successor KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGSemanticSuccessor0(
    makeGlobalProofDAGSemanticSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(
    out.NF.computedGlobalGate.semanticKBundleComputedReadinessDigest.hex,
    out.NF.semanticKBundleComputedReadinessDigest.hex,
  );
  const gateNode = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.FinalTheorem.Readiness',
  );
  assert.equal(gateNode.ready, false);
  assert.deepEqual(gateNode.premises, [
    'Gate.KBundle.FinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
});
