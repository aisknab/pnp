import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckExternalReviewVerificationKeyFiles0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_DIRECTORY0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0,
  makeExternalReviewVerificationKeyFilesInput0,
  makeExternalReviewVerificationKeyFilesSuite0,
} from '../pcc-external-review-verification-key-files0.mjs';

test('verification-key file constructors bind empty key intake manifest', () => {
  const input = makeExternalReviewVerificationKeyFilesInput0();
  const suite = makeExternalReviewVerificationKeyFilesSuite0();

  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_DIRECTORY0, 'external-review/keys/');
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.registryStatus, 'pending-reviewer-key-files');
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.verificationKeyFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.trustedReviewerKeyFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.revokedReviewerKeyFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.externalReviewVerificationKeyFileIntakeReady, true);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.externalReviewVerificationKeyFilesReady, false);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.externalReviewVerificationKeysReady, false);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.externalReviewVerifiedSignaturesReady, false);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.externalReviewAcceptanceReady, false);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0.publicTheoremEmissionAllowed, false);
  assert.equal(input.KeyFileManifest.reviewerKeyFiles.length, 0);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.keyFileManifestDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('verification-key file checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeExternalReviewVerificationKeyFilesInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewVerificationKeyFiles0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewVerificationKeyFiles0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'verification-key file checker rejects caller-supplied readiness or truth assertions',
  );
});
