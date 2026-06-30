import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckBN2DirectBindingGapSeed0 } from '../pcc-direct-bind-bn2-side-tight0.mjs';

test('BN2 direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckBN2DirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-BN2-SIDE-TIGHT-GAP-SEED-2026-06-27-01');
  assert.equal(out.bn2DirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-015-BN2');
  assert.equal(out.boundCoverageEntryId, 'COV-015-BN2');
  assert.equal(out.boundClosureEntryId, 'DCC-015-BN2');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalBN2TheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
