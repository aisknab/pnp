import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewChecklist0 } from '../pcc-public-review-checklist0.mjs';

test('public review checklist accepts current non-activation reviewer checklist', async () => {
  const out = await CheckPublicReviewChecklist0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01');
  assert.equal(out.publicReviewChecklistReady, true);
  assert.equal(out.checklistDocReady, true);
  assert.equal(out.rootEntrypointBound, true);
  assert.equal(out.handoffBound, true);
  assert.equal(out.boundaryBound, true);
  assert.equal(out.externalReviewStatusBound, true);
  assert.equal(out.directTheoremEmissionAllowedByChecklist, false);
  assert.equal(out.reviewAcceptanceClaimed, false);
  assert.equal(out.checklistItemCount, 12);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
