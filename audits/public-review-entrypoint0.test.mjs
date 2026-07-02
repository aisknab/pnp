import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewEntrypoint0 } from '../pcc-public-review-entrypoint0.mjs';

test('public review entrypoint accepts current root reviewer navigation surface', async () => {
  const out = await CheckPublicReviewEntrypoint0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-REVIEW-ENTRYPOINT-2026-06-27-01');
  assert.equal(out.publicReviewEntrypointReady, true);
  assert.equal(out.rootEntryDocumentReady, true);
  assert.equal(out.handoffSurfaceBound, true);
  assert.equal(out.oneCommandVerifierVisible, true);
  assert.equal(out.directTheoremEmissionAllowedByEntrypoint, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
