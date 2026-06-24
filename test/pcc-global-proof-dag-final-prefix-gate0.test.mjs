import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalPrefixFinalTheoremReadiness0,
  CheckGlobalProofDAGFinalPrefixSuccessor0,
} from '../pcc-global-proof-dag-final-prefix-successor0.mjs';

import {
  makeFinalPrefixSuccessorInput0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

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
