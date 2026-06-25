import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckGlobalFinalSATReductionSemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  makeGlobalFinalSATReductionSemanticInput0,
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeInput0() {
  const surfaces = makeFinalPrefixSurfaces0();
  return makeGlobalFinalSATReductionSemanticInput0({
    ...surfaces,
    SATReductionSemanticDerivations:
      makeGlobalFinalSATReductionSemanticSuite0({
        LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
        PCCPack: surfaces.PCCPack,
      }),
  });
}

test('SAT reduction semantic checker accepts the bounded refinement and leaves complexity blocked', async () => {
  const out = await CheckGlobalFinalSATReductionSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.globalFinalSATReductionSemanticReady, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalFinalSATReductionNodeId, GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0);
  assert.equal(out.NF.globalFinalComplexityNodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(out.NF.boundedExecutableSATReductionRefinementOnly, true);
  assert.equal(out.NF.unrestrictedSATReductionSoundnessNotClaimed, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.satReductionDerivation.decisionComparator, 'minSize>baseline');
  assert.equal(out.NF.satReductionDerivation.residualSlackBound, 4);
  assert.equal(out.NF.satReductionDerivation.finalPolynomialExponent, 42);
});

test('SAT reduction semantic checker rejects caller readiness assertions', async () => {
  const out = await CheckGlobalFinalSATReductionSemantic0({
    ...makeInput0(),
    globalFinalSATReductionDerivationReady: true,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATReductionSemantic0.input');
  assert.deepEqual(out.Path, ['globalFinalSATReductionDerivationReady']);
});

test('SAT reduction semantic checker rejects a stale binding digest', async () => {
  const base = makeInput0();
  const out = await CheckGlobalFinalSATReductionSemantic0({
    ...base,
    SATReductionSemanticDerivations: {
      ...base.SATReductionSemanticDerivations,
      reductionBinding: {
        ...base.SATReductionSemanticDerivations.reductionBinding,
        satDecisionDigest: {
          alg: 'SHA256',
          hex: '0'.repeat(64),
        },
      },
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATReductionSemantic0.semanticSATReductionSuite');
});

test('SAT reduction semantic derivation binds required digests', async () => {
  const out = await CheckGlobalFinalSATReductionSemantic0(makeInput0());
  const derivation = out.NF.satReductionDerivation;

  assert.equal(out.tag, 'accept');
  for (const field of [
    'derivationDigest',
    'globalNodeDigest',
    'finalIntegrationDigest',
    'satDecisionDigest',
    'satBoundsDigest',
    'pccMinBridgeDigest',
    'positiveRecordDigest',
    'decisionNegativeProbeDigest',
    'minimizerNegativeProbeDigest',
    'checkerContractDigest',
    'conclusionDigest',
  ]) {
    assert.equal(derivation[field].alg, 'SHA256');
  }
});
