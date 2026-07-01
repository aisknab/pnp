import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPkgCDirectBindingGapSeed0 } from '../pcc-direct-bind-pkgc-separating-consumers0.mjs';

test('PkgC direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckPkgCDirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-PKGC-SEPARATING-CONSUMERS-GAP-SEED-2026-06-27-01');
  assert.equal(out.pkgcDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-019-PkgC');
  assert.equal(out.boundCoverageEntryId, 'COV-019-PkgC');
  assert.equal(out.boundClosureEntryId, 'DCC-019-PkgC');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalPkgCTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
