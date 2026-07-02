import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckExternalReviewStatus0 } from '../pcc-external-review-status0.mjs';

test('external review status checker accepts current non-acceptance boundary', async () => {
  const out = await CheckExternalReviewStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01');
  assert.equal(out.externalReviewStatusReady, true);
  assert.equal(out.externalReviewAcceptanceClaimed, false);
  assert.equal(out.independentReviewAcceptanceConfirmed, false);
  assert.equal(out.noIndependentReviewerConfirmed, true);
  assert.equal(out.externalReviewBlockerStillActive, true);
  assert.equal(out.substantiveFeedbackRecorded, true);
  assert.equal(out.substantiveFeedbackIsAcceptance, false);
  assert.equal(out.publicTheoremEmissionAllowedByExternalReview, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
