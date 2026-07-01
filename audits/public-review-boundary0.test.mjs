import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewBoundary0 } from '../pcc-public-review-boundary0.mjs';

test('public review boundary checker accepts current non-activation perimeter', async () => {
  const out = await CheckPublicReviewBoundary0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01');
  assert.equal(out.publicReviewBoundaryReady, true);
  assert.equal(out.publicTheoremEmissionAllowedByBoundary, false);
  assert.equal(out.finalTheoremReadyByBoundary, false);
  assert.equal(out.publicSurfaceBaselineFrozen, true);
  assert.equal(out.historicalReportSanitized, true);
  assert.equal(out.historicalTheoremAnchorsNonEmitting, true);
  assert.equal(out.releaseLadderBlocked, true);
  assert.equal(out.gapLedgerBlocksPublicEmission, true);
  assert.equal(out.section22ExecutableSurfaceIndexed, true);
  assert.equal(out.section22RunnerBound, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
