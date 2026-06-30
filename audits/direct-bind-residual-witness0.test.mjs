import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckRWDirectBindingGapSeed0 } from '../pcc-direct-bind-residual-witness0.mjs';

test('RW direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckRWDirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-RW-RESIDUAL-WITNESS-GAP-SEED-2026-06-27-01');
  assert.equal(out.rwDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-014-RW');
  assert.equal(out.boundCoverageEntryId, 'COV-014-RW');
  assert.equal(out.boundClosureEntryId, 'DCC-014-RW');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalRWTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
