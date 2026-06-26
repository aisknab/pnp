import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckSignedExternalReviewFindings0,
  SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0,
  SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0,
  makeSignedExternalReviewFindingsInput0,
  makeSignedExternalReviewFindingsSuite0,
} from '../pcc-external-review-signed-findings0.mjs';

test('signed external review constructors bind schema and pending empty bundle', () => {
  const input = makeSignedExternalReviewFindingsInput0();
  const suite = makeSignedExternalReviewFindingsSuite0();

  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0.coordinate, 'ExternalReview.SignedFindings');
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.registryStatus, 'pending-signed-findings');
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.signedFindingCount, 0);
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.acceptanceFindingCount, 0);
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.signedExternalReviewFindingsReady, false);
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.externalReviewAcceptanceReady, false);
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.externalReviewAcceptanceReleased, false);
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.externalReviewAcceptanceNotClaimed, true);
  assert.equal(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.publicTheoremEmissionAllowed, false);
  assert.equal(input.SignedFindingsBundle.signedFindings.length, 0);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.signedFindingsBundleDigest.alg, 'SHA256');
  assert.equal(suite.binding.signedFindingSchemaDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('signed external review checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeSignedExternalReviewFindingsInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckSignedExternalReviewFindings0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSignedExternalReviewFindings0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'signed external-review findings checker rejects caller-supplied readiness or truth assertions',
  );
});
