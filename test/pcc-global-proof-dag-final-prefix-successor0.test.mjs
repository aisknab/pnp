import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalPrefixFinalTheoremReadiness0,
  CheckGlobalProofDAGFinalPrefixSuccessor0,
  makeGlobalProofDAGFinalPrefixSuccessor0,
} from '../pcc-global-proof-dag-final-prefix-successor0.mjs';

import {
  makeFinalPrefixSuccessorInput0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

test('final-prefix successor refines two nodes but keeps public emission disabled', async () => {
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(
    makeFinalPrefixSuccessorInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.equal(out.NF.globalFinalPrefixRefinementsReady, true);
  assert.deepEqual(out.NF.globalFinalPrefixNodeIds, GLOBAL_FINAL_PREFIX_NODE_IDS0);
  assert.deepEqual(out.NF.globalFinalRemainingNodeIds, GLOBAL_FINAL_REMAINING_NODE_IDS0);
  assert.equal(out.NF.boundedExecutableFinalPrefixRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedFinalPrefixTheoremSoundnessNotClaimed, true);
  assert.deepEqual(
    out.NF.semanticOverlay.semanticFinalPrefixNodeIds,
    GLOBAL_FINAL_PREFIX_NODE_IDS0,
  );
  assert.deepEqual(
    out.NF.semanticOverlay.blockedFinalNodeIds,
    GLOBAL_FINAL_REMAINING_NODE_IDS0,
  );
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.FinalSATReductionDerivation',
    'GlobalDAG.FinalComplexityImplication',
  ]);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('final-prefix successor rejects final purpose while two implication gates are blocked', async () => {
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(
    makeFinalPrefixSuccessorInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalPrefixSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic final-prefix global successor is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 2);
  assert.deepEqual(
    out.Witness.semanticallyRefinedFinalNodeIds,
    GLOBAL_FINAL_PREFIX_NODE_IDS0,
  );
  assert.deepEqual(out.Witness.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
});

test('explicit final-prefix final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGFinalPrefixFinalTheoremReadiness0(
    makeFinalPrefixSuccessorInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalPrefixFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('final-prefix successor rejects caller-supplied readiness assertions', async () => {
  const input = makeFinalPrefixSuccessorInput0();
  input.globalFinalPrefixRefinementsReady = true;
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.input');
  assert.deepEqual(out.Path, ['globalFinalPrefixRefinementsReady']);
});

test('final-prefix overlay binds both nodes to checked refinement digests', async () => {
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(
    makeFinalPrefixSuccessorInput0(),
  );

  assert.equal(out.tag, 'accept');
  const byId = new Map(
    out.NF.globalFinalPrefixRefinementDigests.map((entry) => [entry.nodeId, entry]),
  );
  for (const binding of out.NF.semanticOverlay.semanticFinalPrefixBindings) {
    const refinement = byId.get(binding.nodeId);
    assert.equal(binding.refinementDigest.hex, refinement.digest.hex);
    assert.equal(binding.globalNodeDigest.hex, refinement.globalNodeDigest.hex);
    assert.equal(binding.dependencyNodeDigest.hex, refinement.dependencyNodeDigest.hex);
    assert.equal(binding.sourceRecordDigest.hex, refinement.sourceRecordDigest.hex);
    assert.equal(binding.positiveRecordDigest.hex, refinement.positiveRecordDigest.hex);
    assert.equal(binding.negativeRecordDigest.hex, refinement.negativeRecordDigest.hex);
    assert.equal(binding.checkerContractDigest.hex, refinement.checkerContractDigest.hex);
    assert.equal(binding.conclusionDigest.hex, refinement.conclusionDigest.hex);
    assert.equal(binding.publiclyActive, false);
  }
  assert.equal(
    out.NF.computedGlobalGate.nodes.find(
      (node) => node.id === 'Gate.GlobalDAG.FinalPrefixRefinements',
    ).ready,
    true,
  );
  assert.equal(
    out.NF.computedGlobalGate.nodes.find(
      (node) => node.id === 'Gate.FinalTheorem.Readiness',
    ).ready,
    false,
  );
});

test('final-prefix successor rejects a final-purpose child KBundle', async () => {
  const input = makeFinalPrefixSuccessorInput0();
  input.KBundle.Purpose = 'final-theorem';
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('final-prefix successor rejects a stale Sigma-only KBundle at the package predecessor', async () => {
  const input = makeGlobalProofDAGFinalPrefixSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'semantic package predecessor global gate rejected before final-prefix upgrade',
  );
});

test('final-prefix successor rejects a stale prefix binding digest', async () => {
  const input = makeFinalPrefixSuccessorInput0();
  input.FinalPrefixSemanticDerivations = {
    ...input.FinalPrefixSemanticDerivations,
    refinements: input.FinalPrefixSemanticDerivations.refinements.map((entry, index) => (
      index === 1
        ? {
            ...entry,
            packCoreDigest: {
              alg: 'SHA256',
              hex: '0'.repeat(64),
            },
          }
        : entry
    )),
  };
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.semanticFinalPrefix');
  assert.equal(
    out.Witness.reason,
    'bounded semantic final-prefix refinement checker rejected',
  );
});
