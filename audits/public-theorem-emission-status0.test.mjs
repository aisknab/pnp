import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionStatus0 } from '../pcc-public-theorem-emission-status0.mjs';

test('public theorem-emission status summary accepts current denied non-activation state', async () => {
  const out = await CheckPublicTheoremEmissionStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-EMISSION-STATUS-2026-06-27-01');
  assert.equal(out.publicTheoremEmissionStatusReady, true);
  assert.equal(out.statusDocReady, true);
  assert.equal(out.statusBound, false);
  assert.equal(out.gateStatusBound, true);
  assert.equal(out.gatePassed, false);
  assert.equal(out.gateDenied, true);
  assert.equal(out.preflightPassed, false);
  assert.equal(out.denialCertificateReady, true);
  assert.equal(out.negativeTransitionsRejected, true);
  assert.equal(out.releaseBlockersStillActive, true);
  assert.equal(out.externalReviewAcceptanceClaimed, false);
  assert.equal(out.currentPublicEmissionState, 'denied');
  assert.equal(out.allActivationBlockersVisible, true);
  assert.equal(out.publicTheoremEmissionAllowedByStatus, false);
  assert.equal(out.finalTheoremReadyByStatus, false);
  assert.equal(out.statusSummaryIsActivationSurface, false);
  assert.equal(out.statusSummaryBindingRequiresFuturePR, true);
  assert.equal(out.deniedReasonCount, 8);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
