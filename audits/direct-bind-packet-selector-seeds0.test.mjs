import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPacketDirectBindingGapSeed0 } from '../pcc-direct-bind-packet-selector-seeds0.mjs';

test('Packet direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckPacketDirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-PACKET-SELECTOR-SEEDS-GAP-SEED-2026-06-27-01');
  assert.equal(out.packetDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-021-Packet');
  assert.equal(out.boundCoverageEntryId, 'COV-021-Packet');
  assert.equal(out.boundClosureEntryId, 'DCC-021-Packet');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalPacketTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
