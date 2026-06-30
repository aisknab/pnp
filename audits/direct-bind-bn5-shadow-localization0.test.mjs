import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckBN5DirectBindingGapSeed0 } from '../pcc-direct-bind-bn5-shadow-localization0.mjs';

test('BN5 direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckBN5DirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-BN5-SHADOW-LOCALIZATION-GAP-SEED-2026-06-27-01');
  assert.equal(out.bn5DirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-018-BN5');
  assert.equal(out.boundCoverageEntryId, 'COV-018-BN5');
  assert.equal(out.boundClosureEntryId, 'DCC-018-BN5');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalBN5TheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
