import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckBN6DirectBindingGapSeed0 } from '../pcc-direct-bind-bn6-hypergraph-packet0.mjs';

test('BN6 direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckBN6DirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-BN6-HYPERGRAPH-PACKET-GAP-SEED-2026-06-27-01');
  assert.equal(out.bn6DirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-020-BN6');
  assert.equal(out.boundCoverageEntryId, 'COV-020-BN6');
  assert.equal(out.boundClosureEntryId, 'DCC-020-BN6');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalBN6TheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
