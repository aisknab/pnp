import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckGlobalFinalComplexitySemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
  makeGlobalFinalComplexitySemanticInput0,
  makeGlobalFinalComplexitySemanticSuite0,
} from '../pcc-global-final-complexity-semantic0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeInput0() {
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
  return makeGlobalFinalComplexitySemanticInput0({
    ...surfaces,
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
  });
}

test('complexity semantic checker accepts guarded implication while public emission remains separate', async () => {
  const out = await CheckGlobalFinalComplexitySemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.globalFinalComplexitySemanticReady, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.globalFinalDerivationsReady, true);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, true);
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.globalFinalComplexityNodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(
    out.NF.globalFinalComplexityDependencyNodeId,
    GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
  );
  assert.equal(out.NF.boundedExecutableComplexityImplicationOnly, true);
  assert.equal(out.NF.unrestrictedComplexityImplicationSoundnessNotClaimed, true);

  const derivation = out.NF.complexityImplicationDerivation;
  assert.equal(derivation.ready, true);
  assert.equal(derivation.sourceConclusion, 'P = NP');
  assert.equal(derivation.sourceAssumptions.includes('SAT in P'), true);
  assert.equal(derivation.sourceAssumptions.includes('SAT is NP-complete'), true);
});

test('complexity semantic checker rejects caller readiness assertions', async () => {
  const out = await CheckGlobalFinalComplexitySemantic0({
    ...makeInput0(),
    globalFinalComplexityImplicationReady: true,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalComplexitySemantic0.input');
  assert.deepEqual(out.Path, ['globalFinalComplexityImplicationReady']);
});

test('complexity semantic checker rejects a stale semantic binding digest', async () => {
  const base = makeInput0();
  const out = await CheckGlobalFinalComplexitySemantic0({
    ...base,
    ComplexitySemanticDerivations: {
      ...base.ComplexitySemanticDerivations,
      complexityBinding: {
        ...base.ComplexitySemanticDerivations.complexityBinding,
        finalTheoremDigest: {
          alg: 'SHA256',
          hex: '0'.repeat(64),
        },
      },
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalComplexitySemantic0.semanticComplexitySuite');
});

test('complexity semantic derivation binds the final theorem and negative probes', async () => {
  const out = await CheckGlobalFinalComplexitySemantic0(makeInput0());
  const derivation = out.NF.complexityImplicationDerivation;

  assert.equal(out.tag, 'accept');
  for (const field of [
    'derivationDigest',
    'globalNodeDigest',
    'dependencyNodeDigest',
    'dependencyRefinementDigest',
    'finalTheoremDigest',
    'satInPImplicationDigest',
    'complexityImplicationDigest',
    'positiveRecordDigest',
    'premiseNegativeProbeDigest',
    'unconditionalNegativeProbeDigest',
    'checkerContractDigest',
    'conclusionDigest',
  ]) {
    assert.equal(derivation[field].alg, 'SHA256');
  }
});
