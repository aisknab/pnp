import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from '../pcc-unrestricted-final-soundness-gate0.mjs';

import {
  CheckExternalReviewFindingsRegistry0,
  EXTERNAL_REVIEW_FINDING_KINDS0,
  EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0,
  makeExternalReviewFindingsRegistryInput0,
} from '../pcc-external-review-findings-registry0.mjs';

test('external review findings registry records pending signed findings without accepting the theorem', async () => {
  const out = await CheckExternalReviewFindingsRegistry0(
    makeExternalReviewFindingsRegistryInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckExternalReviewFindingsRegistry0');
  assert.equal(out.NF.externalReviewFindingsRegistryRepresentedReady, true);
  assert.equal(out.NF.externalReviewFindingsRegistryReady, true);
  assert.equal(out.NF.externalReviewSignedFindingsReady, false);
  assert.equal(out.NF.externalReviewAcceptanceReady, false);
  assert.equal(out.NF.externalReviewAcceptanceReleased, false);
  assert.equal(out.NF.externalReviewAcceptanceBlocked, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.unrestrictedFinalSoundnessBlocked, true);
  assert.deepEqual(out.NF.remainingBlockerCoordinates, [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ]);
  assert.equal(out.NF.signedFindingCount, 0);
  assert.equal(out.NF.acceptanceFindingCount, 0);
  assert.deepEqual(out.NF.acceptedFindingKinds, EXTERNAL_REVIEW_FINDING_KINDS0);
  assert.deepEqual(
    out.NF.requiredFindingFields,
    EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0,
  );
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.sourceAndArtifactAccessPublicWithoutRequest, true);
  assert.equal(out.NF.externalReviewAcceptanceNotClaimed, true);
  assert.equal(out.NF.findingsRegistryDigest.alg, 'SHA256');
  assert.equal(out.NF.gateBindingDigest.alg, 'SHA256');
  assert.equal(out.NF.releasePublicTheoremEmissionBlockerDigest.alg, 'SHA256');
});

test('external review findings registry rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeExternalReviewFindingsRegistryInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewFindingsRegistry0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewFindingsRegistry0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'external-review findings registry rejects caller-supplied readiness or truth assertions',
  );
});
