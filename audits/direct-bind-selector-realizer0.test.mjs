import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckRDirectBindingGapSeed0 } from '../pcc-direct-bind-selector-realizer0.mjs';

test('R direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckRDirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-R-SELECTOR-REALIZER-GAP-SEED-2026-06-27-01');
  assert.equal(out.rDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-022-R');
  assert.equal(out.boundCoverageEntryId, 'COV-022-R');
  assert.equal(out.boundClosureEntryId, 'DCC-022-R');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalRTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
