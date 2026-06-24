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

test('SAT-reduction semantic checker derives the SAT-in-P final coordinate but leaves P=NP blocked', async () => {
  const out = await CheckGlobalFinalSATReductionSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalFinalSATReductionSemantic0');
  assert.equal(out.NF.globalFinalSATReductionSemanticReady, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalFinalPrefixRefinementsReady, true);
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.equal(out.NF.globalFinalSATReductionNodeId, GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0);
  assert.equal(out.NF.globalFinalComplexityNodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(out.NF.boundedExecutableSATReductionRefinementOnly, true);
  assert.equal(out.NF.unrestrictedSATReductionSoundnessNotClaimed, true);
  assert.equal(out.NF.satInPPublicConclusionNotActivated, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);

  const derivation = out.NF.satReductionDerivation;
  assert.equal(derivation.nodeId, GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0);
  assert.equal(derivation.decisionComparator, 'minSize>baseline');
  assert.equal(derivation.residualSlackBound, 4);
  assert.equal(derivation.finalPolynomialExponent, 42);
  assert.equal(derivation.ready, true);
});

test('SAT-reduction semantic checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    globalFinalSATReductionDerivationReady: true,
  };
  const out = await CheckGlobalFinalSATReductionSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATReductionSemantic0.input');
  assert.deepEqual(out.Path, ['globalFinalSATReductionDerivationReady']);
  assert.equal(
    out.Witness.reason,
    'global SAT-reduction semantic checker rejects caller-supplied readiness or truth assertions',
  );
});

test('SAT-reduction semantic checker rejects a stale reduction binding digest', async () => {
  const input = makeInput0();
  input.SATReductionSemanticDerivations = {
    ...input.SATReductionSemanticDerivations,
    reductionBinding: {
      ...input.SATReductionSemanticDerivations.reductionBinding,
      satDecisionDigest: {
        alg: 'SHA256',
        hex: '0'.repeat(64),
      },
    },
  };
  const out = await CheckGlobalFinalSATReductionSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATReductionSemantic0.semanticSATReductionSuite');
  assert.equal(
    out.Witness.reason,
    'SAT-reduction semantic suite must exactly match the computed final-node, dependency, final-integration, and checker bindings',
  );
});

test('SAT-reduction semantic checker rejects a caller truth payload on the SAT-in-P node', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0
      ? withoutFinalPrefixDigest0(node, { payload: { publicSATinP: true } })
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
  assert.equal(
    out.Witness.reason,
    'SAT-reduction global node must retain empty imports/payload, Full mode, and null route/rank',
  );
});

test('SAT-reduction semantic checker propagates a nonexact SAT decision comparator through final integration', async () => {
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
    SATReductionSemanticDerivations:
      makeGlobalFinalSATReductionSemanticSuite0({
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        PCCPack: pack,
      }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATReductionSemantic0.finalIntegration');
  assert.equal(
    out.Witness.reason,
    'SAT-reduction refinement requires accepted final integration',
  );
});

test('SAT-reduction semantic derivation digests bind integration, decision, bounds, and probes', async () => {
  const out = await CheckGlobalFinalSATReductionSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  const derivation = out.NF.satReductionDerivation;
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
