import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalSATReductionFinalTheoremReadiness0,
  CheckGlobalProofDAGFinalSATReductionSuccessor0,
  makeGlobalProofDAGFinalSATReductionSuccessor0,
} from '../pcc-global-proof-dag-final-sat-reduction-successor0.mjs';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeInput0({ Purpose = 'development', ...options } = {}) {
  const surfaces = makeFinalPrefixSurfaces0(options);
  return makeGlobalProofDAGFinalSATReductionSuccessor0({
    ...surfaces,
    SATReductionSemanticDerivations:
      makeGlobalFinalSATReductionSemanticSuite0({
        LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
        PCCPack: surfaces.PCCPack,
      }),
    Purpose,
  });
}

test('final SAT-reduction successor activates the SAT-in-P refinement but keeps P=NP blocked', async () => {
  const out = await CheckGlobalProofDAGFinalSATReductionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGFinalSATReductionSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalFinalPrefixReady, true);
  assert.equal(out.NF.predecessorGlobalSATReductionReady, false);
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.equal(out.NF.globalFinalPrefixRefinementsReady, true);
  assert.equal(out.NF.globalFinalSATReductionSemanticReady, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalFinalSATReductionNodeId, GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0);
  assert.equal(out.NF.globalFinalComplexityNodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(out.NF.boundedExecutableSATReductionRefinementOnly, true);
  assert.equal(out.NF.unrestrictedSATReductionSoundnessNotClaimed, true);
  assert.equal(out.NF.satInPConclusionRemainsPubliclyQuarantined, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);

  assert.deepEqual(
    out.NF.semanticOverlay.semanticFinalSATReductionNodeIds,
    [GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0],
  );
  assert.equal(
    out.NF.semanticOverlay.semanticFinalSATReductionBinding.nodeId,
    GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  );
  assert.deepEqual(
    out.NF.semanticOverlay.blockedFinalNodeIds,
    [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
  );
  assert.deepEqual(
    out.NF.semanticOverlay.quarantinedFinalNodeIds,
    GLOBAL_DAG_REQUIRED_FINALS0,
  );
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.FinalComplexityImplication',
  ]);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('final SAT-reduction successor rejects final purpose while P=NP implication remains blocked', async () => {
  const out = await CheckGlobalProofDAGFinalSATReductionSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalSATReductionSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic final SAT-reduction global successor is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 1);
  assert.deepEqual(out.Witness.remainingBlockedFinalNodeIds, [GLOBAL_FINAL_COMPLEXITY_NODE_ID0]);
});

test('explicit final SAT-reduction final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGFinalSATReductionFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalSATReductionFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('final SAT-reduction successor rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.globalFinalSATReductionDerivationReady = true;
  const out = await CheckGlobalProofDAGFinalSATReductionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalSATReductionSuccessor0.input');
  assert.deepEqual(out.Path, ['globalFinalSATReductionDerivationReady']);
});

test('final SAT-reduction successor rejects a stale Sigma-only KBundle at the predecessor boundary', async () => {
  const input = makeGlobalProofDAGFinalSATReductionSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });
  const out = await CheckGlobalProofDAGFinalSATReductionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalSATReductionSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'semantic final-prefix predecessor global gate rejected before SAT-reduction upgrade',
  );
});

test('final SAT-reduction overlay binds the SAT-in-P node to the checked derivation digest', async () => {
  const out = await CheckGlobalProofDAGFinalSATReductionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const binding = out.NF.semanticOverlay.semanticFinalSATReductionBinding;
  const derivation = out.NF.satReductionDerivation;
  assert.equal(binding.derivationDigest.hex, derivation.derivationDigest.hex);
  assert.equal(binding.globalNodeDigest.hex, derivation.globalNodeDigest.hex);
  assert.equal(binding.finalIntegrationDigest.hex, derivation.finalIntegrationDigest.hex);
  assert.equal(binding.satDecisionDigest.hex, derivation.satDecisionDigest.hex);
  assert.equal(binding.satBoundsDigest.hex, derivation.satBoundsDigest.hex);
  assert.equal(binding.positiveRecordDigest.hex, derivation.positiveRecordDigest.hex);
  assert.equal(binding.decisionNegativeProbeDigest.hex, derivation.decisionNegativeProbeDigest.hex);
  assert.equal(binding.minimizerNegativeProbeDigest.hex, derivation.minimizerNegativeProbeDigest.hex);
  assert.equal(binding.publiclyActive, false);
});
