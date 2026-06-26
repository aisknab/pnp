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
  CheckPublicTheoremEmissionGate0,
  PUBLIC_EMISSION_BLOCKERS0,
  PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0,
  makePublicTheoremEmissionGateInput0,
  makePublicTheoremEmissionGateSuite0,
} from '../pcc-public-emission-gate0.mjs';

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
  return makePublicTheoremEmissionGateInput0({
    ...surfaces,
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
  });
}

test('public theorem emission gate accepts only as a represented blocked release gate', async () => {
  const out = await CheckPublicTheoremEmissionGate0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPublicTheoremEmissionGate0');
  assert.equal(out.NF.publicEmissionGateRepresentedReady, true);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, true);
  assert.equal(out.NF.globalFinalDerivationsReady, true);
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.sourceAndArtifactAccessPublicWithoutRequest, true);
  assert.deepEqual(out.NF.blockerCoordinates, PUBLIC_EMISSION_BLOCKERS0);
});

test('public theorem emission gate rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    publicTheoremEmissionAllowed: true,
  };
  const out = await CheckPublicTheoremEmissionGate0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckPublicTheoremEmissionGate0.input');
  assert.deepEqual(out.Path, ['publicTheoremEmissionAllowed']);
});

test('public theorem emission gate rejects a mutated documentation coordinate', async () => {
  const input = makeInput0();
  const badCoordinate = {
    ...PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0,
    sealedReleaseNotOverwritten: false,
  };
  const out = await CheckPublicTheoremEmissionGate0({
    ...input,
    DocumentationCoordinate: badCoordinate,
    PublicEmissionGate: makePublicTheoremEmissionGateSuite0({
      DocumentationCoordinate: badCoordinate,
    }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckPublicTheoremEmissionGate0.documentationCoordinate');
  assert.deepEqual(out.Path, ['DocumentationCoordinate']);
});

test('public theorem emission gate rejects a stale gate binding digest', async () => {
  const input = makeInput0();
  const out = await CheckPublicTheoremEmissionGate0({
    ...input,
    PublicEmissionGate: {
      ...input.PublicEmissionGate,
      binding: {
        ...input.PublicEmissionGate.binding,
        policyDigest: {
          alg: 'SHA256',
          hex: '0'.repeat(64),
        },
      },
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckPublicTheoremEmissionGate0.publicEmissionGateSuite');
});
