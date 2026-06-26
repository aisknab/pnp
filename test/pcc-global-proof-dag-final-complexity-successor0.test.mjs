import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  makeGlobalFinalComplexitySemanticSuite0,
} from '../pcc-global-final-complexity-semantic0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0,
  CheckGlobalProofDAGFinalComplexitySuccessor0,
  makeGlobalProofDAGFinalComplexitySuccessor0,
} from '../pcc-global-proof-dag-final-complexity-successor0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeInput0({ Purpose = 'development' } = {}) {
  const surfaces = makeFinalPrefixSurfaces0();
  const SATReductionSemanticDerivations =
    makeGlobalFinalSATReductionSemanticSuite0({
      LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
      PCCPack: surfaces.PCCPack,
    });
  const ComplexitySemanticDerivations =
    makeGlobalFinalComplexitySemanticSuite0({
      LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
      PCCPack: surfaces.PCCPack,
    });
  return makeGlobalProofDAGFinalComplexitySuccessor0({
    ...surfaces,
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
    Purpose,
  });
}

test('final complexity successor completes semantic final-node coverage but keeps public emission gated', async () => {
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, true);
  assert.equal(out.NF.globalFinalDerivationsReady, true);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, true);
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.remainingBlockedFinalNodeIds, []);
  assert.deepEqual(out.NF.semanticOverlay.blockedFinalNodeIds, []);
  assert.deepEqual(out.NF.semanticOverlay.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(
    out.NF.semanticOverlay.semanticFinalComplexityNodeIds.includes(
      GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    ),
    true,
  );
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'Release.PublicTheoremEmission',
  ]);
});

test('final complexity successor rejects final purpose until public emission gate is represented', async () => {
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalComplexitySuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.blockers.filter((entry) => !entry.ready)[0].coordinate,
    'Release.PublicTheoremEmission',
  );
});

test('explicit final complexity readiness gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('final complexity successor rejects caller readiness assertions', async () => {
  const input = makeInput0();
  input.globalFinalComplexityImplicationReady = true;
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalComplexitySuccessor0.input');
  assert.deepEqual(out.Path, ['globalFinalComplexityImplicationReady']);
});
