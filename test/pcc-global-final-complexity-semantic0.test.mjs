import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckGlobalFinalComplexitySemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  makeGlobalFinalComplexitySemanticInput0,
  makeGlobalFinalComplexitySemanticSuite0,
} from '../pcc-global-final-complexity-semantic0.mjs';

import {
  STANDARD_COMPLEXITY_BASIS0,
} from '../pcc-complexity-bridge0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeInput0() {
  const LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0();
  const surfaces = makeFinalPrefixSurfaces0({ LegacyGlobalProofDAG });
  const SATReductionSemanticDerivations =
    makeGlobalFinalSATReductionSemanticSuite0({
      LegacyGlobalProofDAG,
      PCCPack: surfaces.PCCPack,
    });
  return makeGlobalFinalComplexitySemanticInput0({
    ...surfaces,
    SATReductionSemanticDerivations,
    ComplexityBasis: STANDARD_COMPLEXITY_BASIS0,
    ComplexitySemanticDerivations:
      makeGlobalFinalComplexitySemanticSuite0({
        LegacyGlobalProofDAG,
        PCCPack: surfaces.PCCPack,
        SATReductionSemanticDerivations,
        ComplexityBasis: STANDARD_COMPLEXITY_BASIS0,
      }),
  });
}

test('final complexity checker accepts the guarded bridge while publication remains disabled', async () => {
  const out = await CheckGlobalFinalComplexitySemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.globalFinalComplexitySemanticReady, true);
  assert.equal(out.NF.globalFinalComplexityImplicationRefinementReady, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, true);
  assert.equal(out.NF.allGlobalFinalCoordinatesBoundedRefined, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, true);
  assert.equal(out.NF.guardedComplexityRefinementOnly, true);
  assert.equal(out.NF.cookLevinFormalizationIncluded, false);
  assert.equal(out.NF.unrestrictedComplexityImplicationSoundnessNotClaimed, true);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.complexityDerivation.nodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(out.NF.complexityDerivation.ready, true);
});

test('final complexity checker rejects caller-supplied readiness assertions', async () => {
  const out = await CheckGlobalFinalComplexitySemantic0({
    ...makeInput0(),
    globalFinalComplexityImplicationReady: true,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalComplexitySemantic0.input');
  assert.deepEqual(out.Path, ['globalFinalComplexityImplicationReady']);
});

test('final complexity checker rejects a stale complexity binding', async () => {
  const base = makeInput0();
  const out = await CheckGlobalFinalComplexitySemantic0({
    ...base,
    ComplexitySemanticDerivations: {
      ...base.ComplexitySemanticDerivations,
      complexityBinding: {
        ...base.ComplexitySemanticDerivations.complexityBinding,
        sourceImplicationDigest: {
          alg: 'SHA256',
          hex: '0'.repeat(64),
        },
      },
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalComplexitySemantic0.semanticComplexitySuite');
});

test('final complexity derivation binds required digests', async () => {
  const out = await CheckGlobalFinalComplexitySemantic0(makeInput0());
  const derivation = out.NF.complexityDerivation;

  assert.equal(out.tag, 'accept');
  for (const field of [
    'derivationDigest',
    'globalNodeDigest',
    'dependencyNodeDigest',
    'dependencyDerivationDigest',
    'complexityBasisDigest',
    'sourceImplicationDigest',
    'finalPublicTheoremDigest',
    'finalTheoremRecordDigest',
    'complexityBridgeRecordDigest',
    'premiseRemovalNegativeProbeDigest',
    'unconditionalClaimNegativeProbeDigest',
    'checkerContractDigest',
    'conclusionDigest',
  ]) {
    assert.equal(derivation[field].alg, 'SHA256');
  }
});
