import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalFinalSATReductionSemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  makeGlobalFinalSATReductionSemanticInput0,
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  makeGlobalFinalPrefixSemanticSuite0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  makeFinalPrefixSurfaces0,
  withoutFinalPrefixDigest0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeInput0(options = {}) {
  const surfaces = makeFinalPrefixSurfaces0(options);
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

test('SAT reduction semantic checker rejects payload drift on the SAT-reduction node', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0
      ? withoutFinalPrefixDigest0(node, { payload: { promoted: true } })
      : node
  ));
  const out = await CheckGlobalFinalSATReductionSemantic0(
    makeInput0({ LegacyGlobalProofDAG: dag }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalFinalSATReductionSemantic0.finalSATReduction.Final.AcceptedPackageImpliesSATinP',
  );
});

test('SAT reduction semantic checker propagates a nonexact decision comparator through final integration', async () => {
  const input = makeInput0();
  const pack = {
    ...input.PCCPack,
    FinalIntegration: {
      ...input.PCCPack.FinalIntegration,
      SATDecision: {
        ...input.PCCPack.FinalIntegration.SATDecision,
        DecisionRule: {
          ...input.PCCPack.FinalIntegration.SATDecision.DecisionRule,
          comparator: 'minSize>=baseline',
        },
      },
    },
  };
  const out = await CheckGlobalFinalSATReductionSemantic0({
    ...input,
    PCCPack: pack,
    FinalPrefixSemanticDerivations: makeGlobalFinalPrefixSemanticSuite0({
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      PCCPack: pack,
    }),
    SATReductionSemanticDerivations:
      makeGlobalFinalSATReductionSemanticSuite0({
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        PCCPack: pack,
      }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATReductionSemantic0.finalIntegration');
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
