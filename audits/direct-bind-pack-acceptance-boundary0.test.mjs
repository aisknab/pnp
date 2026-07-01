import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPACKAcceptanceBoundarySeed0 } from '../pcc-direct-bind-pack-acceptance-boundary0.mjs';

test('PACK acceptance boundary seed accepts current linked ledgers', async () => {
  const out = await CheckPACKAcceptanceBoundarySeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-PACK-ACCEPTANCE-BOUNDARY-SEED-2026-06-27-01');
  assert.equal(out.packAcceptanceBoundarySeedReady, true);
  assert.equal(out.releaseBoundaryBlocked, true);
  assert.equal(out.coverageClass, 'release-critical-boundary-surface');
  assert.equal(out.closureStatus, 'release-boundary-blocked');
  assert.equal(out.boundInventoryEntryId, 'TL-027-PACK');
  assert.equal(out.boundCoverageEntryId, 'COV-027-PACK');
  assert.equal(out.boundClosureEntryId, 'DCC-027-PACK');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-002-ExternalReviewAcceptance']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalPACKTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.packAcceptanceActivationBySeed, false);
  assert.equal(out.reportProseActivationAllowed, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
