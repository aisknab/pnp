import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckBN4DirectBindingGapSeed0 } from '../pcc-direct-bind-bn4-activation0.mjs';

test('BN4 direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckBN4DirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-BN4-ACTIVATION-GAP-SEED-2026-06-27-01');
  assert.equal(out.bn4DirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-017-BN4');
  assert.equal(out.boundCoverageEntryId, 'COV-017-BN4');
  assert.equal(out.boundClosureEntryId, 'DCC-017-BN4');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalBN4TheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
