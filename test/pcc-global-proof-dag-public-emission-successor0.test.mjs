import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  makeGlobalFinalComplexitySemanticSuite0,
} from '../pcc-global-final-complexity-semantic0.mjs';

import {
  PUBLIC_EMISSION_BLOCKERS0,
} from '../pcc-public-emission-gate0.mjs';

import {
  CheckGlobalProofDAGPublicEmissionSuccessor0,
  makeGlobalProofDAGPublicEmissionSuccessor0,
} from '../pcc-global-proof-dag-public-emission-successor0.mjs';

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
  return makeGlobalProofDAGPublicEmissionSuccessor0({
    ...surfaces,
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
  });
}

test('public-emission successor keeps bounded semantic DAG complete but publication blocked', async () => {
  const out = await CheckGlobalProofDAGPublicEmissionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGPublicEmissionSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalSemanticNodeDerivationsReady, true);
  assert.equal(out.NF.predecessorGlobalFinalDerivationsReady, true);
  assert.equal(out.NF.publicEmissionGateRepresentedReady, true);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, true);
  assert.equal(out.NF.globalFinalDerivationsReady, true);
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.releasePublicTheoremEmissionBlocked, true);
  assert.deepEqual(out.NF.releasePublicTheoremEmissionBlockers, PUBLIC_EMISSION_BLOCKERS0);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.sourceAndArtifactAccessPublicWithoutRequest, true);
});
