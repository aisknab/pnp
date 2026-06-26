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
  CheckPublicationCoordinateGate0,
  PUBLICATION_COORDINATE_DISCHARGED_BLOCKERS0,
  PUBLICATION_COORDINATE_REMAINING_BLOCKERS0,
  PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
  makePublicationCoordinateGateInput0,
  makePublicationCoordinateGateSuite0,
} from '../pcc-publication-coordinate-gate0.mjs';

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
  return makePublicationCoordinateGateInput0({
    ...surfaces,
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
  });
}

test('publication coordinate gate discharges only the immutable-documentation blocker', async () => {
  const out = await CheckPublicationCoordinateGate0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPublicationCoordinateGate0');
  assert.equal(out.NF.publicationCoordinateGateReady, true);
  assert.equal(out.NF.publicEmissionPredecessorAccepted, true);
  assert.deepEqual(out.NF.priorBlockerCoordinates, PUBLIC_EMISSION_BLOCKERS0);
  assert.equal(out.NF.documentationImmutablePublicRevisionReady, true);
  assert.equal(out.NF.documentationImmutablePublicRevisionBlocked, false);
  assert.deepEqual(
    out.NF.dischargedBlockerCoordinates,
    PUBLICATION_COORDINATE_DISCHARGED_BLOCKERS0,
  );
  assert.deepEqual(
    out.NF.remainingBlockerCoordinates,
    PUBLICATION_COORDINATE_REMAINING_BLOCKERS0,
  );
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.sourceAndArtifactAccessPublicWithoutRequest, true);
  assert.equal(out.NF.publicReviewPublicationFraming, true);
  assert.equal(out.NF.independentMathematicalReviewStillRequired, true);
  assert.equal(out.NF.independentCheckerSoundnessReviewStillRequired, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.externalReviewAcceptanceReady, false);
});

test('publication coordinate gate rejects a mutated public-review coordinate', async () => {
  const input = makeInput0();
  const badCoordinate = {
    ...PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
    publicTheoremEmissionNotActivated: false,
  };
  const out = await CheckPublicationCoordinateGate0({
    ...input,
    PublicationDocumentationCoordinate: badCoordinate,
    PublicationCoordinateGate: makePublicationCoordinateGateSuite0({
      PublicationDocumentationCoordinate: badCoordinate,
    }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckPublicationCoordinateGate0.publicationDocumentationCoordinate',
  );
  assert.deepEqual(out.Path, ['PublicationDocumentationCoordinate']);
});

test('publication coordinate gate rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    documentationImmutablePublicRevisionReady: true,
  };
  const out = await CheckPublicationCoordinateGate0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckPublicationCoordinateGate0.input');
  assert.deepEqual(out.Path, ['documentationImmutablePublicRevisionReady']);
  assert.equal(
    out.Witness.reason,
    'publication coordinate gate rejects caller-supplied readiness or truth assertions',
  );
});

test('publication coordinate digest binds payload and transport hashes', async () => {
  const out = await CheckPublicationCoordinateGate0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.publicationDocumentationCoordinate.texPayloadSha256.length, 64);
  assert.equal(out.NF.publicationDocumentationCoordinate.pdfPayloadSha256.length, 64);
  assert.equal(out.NF.publicationDocumentationCoordinate.texPatchSha256.length, 64);
  assert.equal(out.NF.publicationDocumentationCoordinateDigest.alg, 'SHA256');
  assert.equal(out.NF.publicationCoordinateGateBindingDigest.alg, 'SHA256');
  assert.equal(out.NF.releasePublicTheoremEmissionBlockerDigest.alg, 'SHA256');
  for (const entry of out.NF.remainingBlockers) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.ready, false);
  }
  for (const entry of out.NF.dischargedBlockers) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.ready, true);
  }
});
