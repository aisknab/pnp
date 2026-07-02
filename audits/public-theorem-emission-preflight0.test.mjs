import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionPreflight0 } from '../pcc-public-theorem-emission-preflight0.mjs';

test('public theorem emission preflight accepts current denied non-activation state', async () => {
  const out = await CheckPublicTheoremEmissionPreflight0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01');
  assert.equal(out.publicTheoremEmissionPreflightReady, true);
  assert.equal(out.publicTheoremEmissionPreflightPassed, false);
  assert.equal(out.publicTheoremEmissionDenied, true);
  assert.equal(out.finalTheoremReadyByPreflight, false);
  assert.equal(out.releaseBlockerClearanceAccepted, false);
  assert.equal(out.externalReviewAcceptanceClaimed, false);
  assert.equal(out.unrestrictedFinalSoundnessClearanceAccepted, false);
  assert.equal(out.publicReviewBoundaryNonActivating, true);
  assert.equal(out.blockedByRemainingBlockers, true);
  assert.equal(out.preflightTransitionRequiresFuturePR, true);
  assert.equal(out.requiredBlockedLadderNodeCount, 3);
  assert.equal(out.requiredReleaseGapCount, 4);
  assert.equal(out.requiredProofObligationCount, 2);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
