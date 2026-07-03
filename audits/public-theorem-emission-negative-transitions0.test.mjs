import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionNegativeTransitions0 } from '../pcc-public-theorem-emission-negative-transitions0.mjs';

test('public theorem emission negative transition audit accepts rejected-transition matrix', async () => {
  const out = await CheckPublicTheoremEmissionNegativeTransitions0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-EMISSION-NEGATIVE-TRANSITIONS-2026-06-27-01');
  assert.equal(out.negativeTransitionAuditReady, true);
  assert.equal(out.currentDeniedStateAccepted, true);
  assert.equal(out.allNegativeTransitionsRejected, true);
  assert.equal(out.prematureActivationRejected, true);
  assert.equal(out.publicTheoremEmissionAllowedByNegativeTransitions, false);
  assert.equal(out.negativeTransitionAuditIsActivationSurface, false);
  assert.equal(out.negativeTransitionBindingRequiresFuturePR, false);
  assert.equal(out.negativeTransitionCaseCount, 9);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
  assert.deepEqual(out.negativeTransitionCases.map((row) => row.actualTag), Array(9).fill('reject'));
});
