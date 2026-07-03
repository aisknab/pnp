import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionDenial0 } from '../pcc-public-theorem-emission-denial0.mjs';

test('denial checker accepts current non-activation state', async () => {
  const out = await CheckPublicTheoremEmissionDenial0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-EMISSION-DENIAL-2026-06-27-01');
  assert.equal(out.denialCertificateReady, true);
  assert.equal(out.publicTheoremEmissionDenied, true);
  assert.equal(out.publicTheoremEmissionAllowedByDenial, false);
  assert.equal(out.publicTheoremEmissionPreflightPassed, false);
  assert.equal(out.finalTheoremReadyByDenial, false);
  assert.deepEqual(out.activeFinalNodeIdsByDenial, []);
  assert.equal(out.denialCertificateIsActivationSurface, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
