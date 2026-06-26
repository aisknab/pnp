import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckGlobalFinalSATSemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_NODE_ID0,
  makeGlobalFinalSATSemanticSuite0,
} from '../pcc-global-final-sat-semantic0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeFinalSATSemanticInput0,
  withoutFinalSATDigest0,
} from './helpers/pcc-global-final-sat-fixture0.mjs';

test('final SAT checker refines accepted-package-to-SAT-in-P while complexity implication remains blocked', async () => {
  const out = await CheckGlobalFinalSATSemantic0(makeFinalSATSemanticInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalFinalSATSemantic0');
  assert.equal(out.NF.globalFinalSATSemanticReady, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalAcceptedPackageImpliesSATinPRefinementReady, true);
  assert.equal(out.NF.finalSATNodeId, GLOBAL_FINAL_SAT_NODE_ID0);
  assert.equal(out.NF.remainingFinalComplexityNodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(out.NF.finalIntegrationAccepted, true);
  assert.equal(out.NF.globalFinalPrefixRefinementsReady, true);
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.equal(out.NF.comparator, 'minSize>baseline');
  assert.equal(out.NF.residualSlackBound, 4);
  assert.equal(out.NF.finalSATPolynomialExponent, 42);
  assert.equal(out.NF.boundedExecutableSATReductionRefinementOnly, true);
  assert.equal(out.NF.unrestrictedSATReductionSoundnessNotClaimed, true);
  assert.equal(out.NF.complexityClassImplicationNotClaimed, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.negativeDecisionCoord.startsWith('CheckSATDecision0.'), true);
  assert.equal(out.NF.negativeBoundsCoord.startsWith('CheckSATBounds0.'), true);
});

test('final SAT checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeFinalSATSemanticInput0(),
    globalFinalSATReductionDerivationReady: true,
  };
  const out = await CheckGlobalFinalSATSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATSemantic0.input');
  assert.deepEqual(out.Path, ['globalFinalSATReductionDerivationReady']);
  assert.equal(
    out.Witness.reason,
    'global final SAT semantic checker rejects caller-supplied readiness or truth assertions',
  );
});

test('final SAT checker rejects a stale semantic binding digest', async () => {
  const base = makeFinalSATSemanticInput0();
  const input = {
    ...base,
    SemanticFinalSAT: {
      ...base.SemanticFinalSAT,
      refinement: {
        ...base.SemanticFinalSAT.refinement,
        satDecisionRecordDigest: {
          alg: 'SHA256',
          hex: '0'.repeat(64),
        },
      },
    },
  };
  const out = await CheckGlobalFinalSATSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATSemantic0.semanticFinalSATSuite');
  assert.equal(
    out.Witness.reason,
    'global final SAT semantic suite must exactly match the computed final-node, dependency, integration, and checker bindings',
  );
});

test('final SAT checker rejects caller truth payload on the SAT implication node', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === GLOBAL_FINAL_SAT_NODE_ID0
      ? withoutFinalSATDigest0(node, { payload: { provesSATinP: true } })
      : node
  ));
  const out = await CheckGlobalFinalSATSemantic0(makeFinalSATSemanticInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATSemantic0.finalSATNode');
  assert.equal(
    out.Witness.reason,
    'final SAT global node must retain empty imports/payload, Full mode, and null route/rank',
  );
});

test('final SAT checker propagates a non-exact SAT decision through final integration', async () => {
  const input = makeFinalSATSemanticInput0();
  const pack = {
    ...input.PCCPack,
    FinalIntegration: {
      ...input.PCCPack.FinalIntegration,
      SATDecision: {
        ...input.PCCPack.FinalIntegration.SATDecision,
        DecisionRule: {
          ...input.PCCPack.FinalIntegration.SATDecision.DecisionRule,
          usesExactMinimum: false,
        },
      },
    },
  };
  const out = await CheckGlobalFinalSATSemantic0({
    ...input,
    PCCPack: pack,
    SemanticFinalSAT: makeGlobalFinalSATSemanticSuite0({
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      PCCPack: pack,
    }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalSATSemantic0.finalIntegration');
});

test('final SAT refinement digests bind node, dependencies, integration, decision, and bounds records', async () => {
  const out = await CheckGlobalFinalSATSemantic0(makeFinalSATSemanticInput0());

  assert.equal(out.tag, 'accept');
  for (const digest of [
    out.NF.refinementDigest,
    out.NF.globalNodeDigest,
    out.NF.finalIntegrationDigest,
    out.NF.satDecisionDigest,
    out.NF.satBoundsDigest,
    out.NF.checkerContractDigest,
    out.NF.conclusionDigest,
    out.NF.negativeDecisionRecordDigest,
    out.NF.negativeBoundsRecordDigest,
  ]) {
    assert.equal(digest.alg, 'SHA256');
  }
  assert.equal(out.NF.dependencyNodeDigests.length, 3);
  for (const digest of out.NF.dependencyNodeDigests) {
    assert.equal(digest.alg, 'SHA256');
  }
});
