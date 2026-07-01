import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckHBDirectBindingGapSeed0 } from '../pcc-direct-bind-hb-negative-closure0.mjs';

test('HB direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckHBDirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-HB-NEGATIVE-CLOSURE-GAP-SEED-2026-06-27-01');
  assert.equal(out.hbDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-023-HB');
  assert.equal(out.boundCoverageEntryId, 'COV-023-HB');
  assert.equal(out.boundClosureEntryId, 'DCC-023-HB');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalHBTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
