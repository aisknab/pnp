import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_NODE_ID0,
} from '../pcc-global-final-sat-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalSATFinalTheoremReadiness0,
  CheckGlobalProofDAGFinalSATSuccessor0,
} from '../pcc-global-proof-dag-final-sat-successor0.mjs';

import {
  makeFinalSATSuccessorInput0,
} from './helpers/pcc-global-final-sat-fixture0.mjs';

test('final SAT successor activates SAT implication refinement while complexity implication remains blocked', async () => {
  const out = await CheckGlobalProofDAGFinalSATSuccessor0(
    makeFinalSATSuccessorInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGFinalSATSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalFinalPrefixReady, true);
  assert.equal(out.NF.predecessorGlobalFinalSATReady, false);
  assert.equal(out.NF.globalFinalPrefixRefinementsReady, true);
  assert.equal(out.NF.globalFinalSATSemanticReady, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalAcceptedPackageImpliesSATinPRefinementReady, true);
  assert.equal(out.NF.globalFinalSATNodeId, GLOBAL_FINAL_SAT_NODE_ID0);
  assert.equal(out.NF.boundedExecutableSATReductionRefinementOnly, true);
  assert.equal(out.NF.unrestrictedSATReductionSoundnessNotClaimed, true);
  assert.equal(out.NF.complexityClassImplicationNotClaimed, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);

  assert.deepEqual(out.NF.semanticOverlay.semanticFinalSATNodeIds, [GLOBAL_FINAL_SAT_NODE_ID0]);
  assert.deepEqual(out.NF.semanticOverlay.blockedFinalNodeIds, [GLOBAL_FINAL_COMPLEXITY_NODE_ID0]);
  assert.equal(out.NF.semanticOverlay.semanticNodeIds.includes(GLOBAL_FINAL_SAT_NODE_ID0), true);
  assert.equal(out.NF.semanticOverlay.structuralOnlyNodeIds.includes(GLOBAL_FINAL_SAT_NODE_ID0), false);
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.FinalComplexityImplication',
  ]);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('final SAT successor rejects final purpose while complexity implication remains blocked', async () => {
  const out = await CheckGlobalProofDAGFinalSATSuccessor0(
    makeFinalSATSuccessorInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalSATSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic final SAT global successor is not ready for final-theorem use',
  );
  assert.deepEqual(out.Witness.remainingBlockedFinalNodeIds, [GLOBAL_FINAL_COMPLEXITY_NODE_ID0]);
  assert.deepEqual(out.Witness.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
});

test('explicit final SAT final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGFinalSATFinalTheoremReadiness0(
    makeFinalSATSuccessorInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalSATFinalTheoremReadiness0.purpose');
  assert.deepEqual(out.Path, ['Purpose']);
});

test('final SAT successor rejects caller-supplied readiness assertions', async () => {
  const input = makeFinalSATSuccessorInput0();
  input.globalFinalSATReductionDerivationReady = true;
  const out = await CheckGlobalProofDAGFinalSATSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalSATSuccessor0.input');
  assert.deepEqual(out.Path, ['globalFinalSATReductionDerivationReady']);
});

test('final SAT overlay binds the SAT node to the semantic refinement digest', async () => {
  const out = await CheckGlobalProofDAGFinalSATSuccessor0(
    makeFinalSATSuccessorInput0(),
  );

  assert.equal(out.tag, 'accept');
  const binding = out.NF.semanticOverlay.semanticFinalSATBindings[0];
  const refinement = out.NF.globalFinalSATRefinementDigests[0];
  assert.equal(binding.nodeId, GLOBAL_FINAL_SAT_NODE_ID0);
  assert.equal(binding.refinementDigest.hex, refinement.digest.hex);
  assert.equal(binding.globalNodeDigest.hex, refinement.globalNodeDigest.hex);
  assert.equal(binding.finalIntegrationDigest.hex, refinement.finalIntegrationDigest.hex);
  assert.equal(binding.satDecisionDigest.hex, refinement.satDecisionDigest.hex);
  assert.equal(binding.satBoundsDigest.hex, refinement.satBoundsDigest.hex);
  assert.equal(binding.checkerContractDigest.hex, refinement.checkerContractDigest.hex);
  assert.equal(binding.conclusionDigest.hex, refinement.conclusionDigest.hex);
  assert.equal(binding.publiclyActive, false);
});
