import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckGDirectBindingSeed0 } from '../pcc-direct-bind-locked-nand-threshold0.mjs';

test('G direct-binding seed accepts current linked ledgers', async () => {
  const out = await CheckGDirectBindingSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-G-LOCKED-NAND-THRESHOLD-SEED-2026-06-27-01');
  assert.equal(out.gDirectBindingSeedReady, true);
  assert.equal(out.coverageClass, 'locked-nand-seed-surface');
  assert.equal(out.closureStatus, 'direct-binding-seed-upgrade-needed');
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-025-G');
  assert.equal(out.boundCoverageEntryId, 'COV-025-G');
  assert.equal(out.boundClosureEntryId, 'DCC-025-G');
  assert.deepEqual(out.blockingGaps, ['GAP-003-BoundedSmallModelsNotUniformProof', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalGTheoremDischarged, false);
  assert.equal(out.fullLockedNANDThresholdCoverageProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
