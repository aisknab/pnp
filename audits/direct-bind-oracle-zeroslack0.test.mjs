import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckODirectBindingGapSeed0 } from '../pcc-direct-bind-oracle-zeroslack0.mjs';

test('O direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckODirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-O-ORACLE-ZEROSLACK-GAP-SEED-2026-06-27-01');
  assert.equal(out.oDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-024-O');
  assert.equal(out.boundCoverageEntryId, 'COV-024-O');
  assert.equal(out.boundClosureEntryId, 'DCC-024-O');
  assert.equal(out.coverageClass, 'complexity-and-gap-surface');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalOTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.complexityImplicationActivated, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
