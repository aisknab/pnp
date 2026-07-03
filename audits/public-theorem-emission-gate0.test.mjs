import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionGate0 } from '../pcc-public-theorem-emission-gate0.mjs';

test('public theorem-emission gate accepts current denied non-activation state', async () => {
  const out = await CheckPublicTheoremEmissionGate0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-EMISSION-GATE-2026-06-27-01');
  assert.equal(out.publicTheoremEmissionGateReady, true);
  assert.equal(out.publicTheoremEmissionGatePassed, false);
  assert.equal(out.publicTheoremEmissionDenied, true);
  assert.equal(out.currentDeniedStateAccepted, true);
  assert.equal(out.denialCertificateBound, true);
  assert.equal(out.preflightBound, true);
  assert.equal(out.negativeTransitionsBound, true);
  assert.equal(out.allNegativeTransitionsRejected, true);
  assert.equal(out.prematureActivationRejected, true);
  assert.equal(out.releaseBlockersStillActive, true);
  assert.equal(out.publicTheoremEmissionAllowedByGate, false);
  assert.equal(out.finalTheoremReadyByGate, false);
  assert.equal(out.gateIsActivationSurface, false);
  assert.equal(out.gateBindingRequiresFuturePR, true);
  assert.equal(out.deniedReasonCount, 8);
  assert.equal(out.negativeTransitionCaseCount, 9);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
