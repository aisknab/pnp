import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckBN3DirectBindingGapSeed0 } from '../pcc-direct-bind-bn3-request-envelope0.mjs';

test('BN3 direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckBN3DirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-BN3-REQUEST-ENVELOPE-GAP-SEED-2026-06-27-01');
  assert.equal(out.bn3DirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-016-BN3');
  assert.equal(out.boundCoverageEntryId, 'COV-016-BN3');
  assert.equal(out.boundClosureEntryId, 'DCC-016-BN3');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalBN3TheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
