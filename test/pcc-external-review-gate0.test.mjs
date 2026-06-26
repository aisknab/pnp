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
  CheckExternalReviewGate0,
  EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0,
  makeExternalReviewGateInput0,
} from '../pcc-external-review-gate0.mjs';

test('external review gate represents review request but keeps acceptance blocked', async () => {
  const out = await CheckExternalReviewGate0(makeExternalReviewGateInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckExternalReviewGate0');
  assert.equal(out.NF.externalReviewGateRepresentedReady, true);
  assert.equal(out.NF.externalReviewRequestPacketReady, true);
  assert.equal(out.NF.externalReviewRequestRepresentedReady, true);
  assert.equal(out.NF.externalReviewAcceptanceReady, false);
  assert.equal(out.NF.externalReviewAcceptanceReleased, false);
  assert.equal(out.NF.externalReviewAcceptanceBlocked, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.unrestrictedFinalSoundnessBlocked, true);
  assert.deepEqual(out.NF.remainingBlockerCoordinates, [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ]);
  assert.equal(
    out.NF.reviewRequestObligationCount,
    EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0.length,
  );
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.sourceAndArtifactAccessPublicWithoutRequest, true);
  assert.equal(out.NF.externalReviewAcceptanceNotClaimed, true);
  assert.equal(out.NF.reviewRequestPacketDigest.alg, 'SHA256');
  assert.equal(out.NF.gateBindingDigest.alg, 'SHA256');
  assert.equal(out.NF.releasePublicTheoremEmissionBlockerDigest.alg, 'SHA256');
});

test('external review gate rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeExternalReviewGateInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewGate0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewGate0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'external-review gate rejects caller-supplied readiness or truth assertions',
  );
});
