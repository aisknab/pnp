import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckFinalTheoremBoundarySeed0 } from '../pcc-direct-bind-final-theorem-boundary0.mjs';

test('Final theorem boundary seed accepts current linked ledgers', async () => {
  const out = await CheckFinalTheoremBoundarySeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-FINAL-THEOREM-BOUNDARY-SEED-2026-06-27-01');
  assert.equal(out.finalTheoremBoundarySeedReady, true);
  assert.equal(out.releaseBoundaryBlocked, true);
  assert.equal(out.coverageClass, 'release-critical-boundary-surface');
  assert.equal(out.closureStatus, 'release-boundary-blocked');
  assert.equal(out.boundInventoryEntryId, 'TL-026-Final');
  assert.equal(out.boundCoverageEntryId, 'COV-026-Final');
  assert.equal(out.boundClosureEntryId, 'DCC-026-Final');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-002-ExternalReviewAcceptance']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalFinalTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremActivationBySeed, false);
  assert.equal(out.releaseLadderTransitionActivated, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
