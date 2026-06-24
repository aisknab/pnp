import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalPrefixSuccessor0,
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
