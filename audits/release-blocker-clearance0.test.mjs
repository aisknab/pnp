import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckReleaseBlockerClearance0 } from '../pcc-release-blocker-clearance0.mjs';

test('release blocker clearance protocol accepts current non-clearing state', async () => {
  const out = await CheckReleaseBlockerClearance0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01');
  assert.equal(out.clearanceProtocolReady, true);
  assert.equal(out.releaseBlockersStillActive, true);
  assert.equal(out.releaseBlockerClearanceAccepted, false);
  assert.equal(out.unrestrictedFinalSoundnessClearanceAccepted, false);
  assert.equal(out.externalReviewClearanceAccepted, false);
  assert.equal(out.publicTheoremEmissionAllowedByClearance, false);
  assert.equal(out.finalTheoremReadyByClearance, false);
  assert.equal(out.blockedTransitionOnly, true);
  assert.equal(out.clearanceTransitionRequiresFuturePR, true);
  assert.equal(out.requiredBlockedLadderNodeCount, 3);
  assert.equal(out.requiredReleaseGapCount, 4);
  assert.equal(out.requiredProofObligationCount, 2);
  assert.equal(out.clearanceRuleCount, 2);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
