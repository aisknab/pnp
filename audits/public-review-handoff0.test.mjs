import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewHandoff0 } from '../pcc-public-review-handoff0.mjs';

test('public review handoff accepts current non-activation entry surface', async () => {
  const out = await CheckPublicReviewHandoff0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-REVIEW-HANDOFF-2026-06-27-01');
  assert.equal(out.publicReviewHandoffReady, true);
  assert.equal(out.handoffDocReady, true);
  assert.equal(out.publicReviewBoundaryBound, true);
  assert.equal(out.oneCommandVerifierBound, true);
  assert.equal(out.historicalReportSanitized, true);
  assert.equal(out.publicSurfaceBaselineBound, true);
  assert.equal(out.section22DirectBindingSurfacesBound, true);
  assert.equal(out.directTheoremEmissionAllowedByHandoff, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
