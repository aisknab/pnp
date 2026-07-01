import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckDirectBindingIndex0 } from '../pcc-direct-binding-index0.mjs';

test('Section 22 direct-binding index accepts current linked ledgers', async () => {
  const out = await CheckDirectBindingIndex0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01');
  assert.equal(out.section22RowsIndexed, true);
  assert.equal(out.indexedEntryCount, 27);
  assert.equal(out.allSection22RowsHaveExecutableSurface, true);
  assert.equal(out.allSection22RowsDirectCheckerComplete, false);
  assert.equal(out.directCheckerBindingCompleteCount, 0);
  assert.equal(out.releaseCriticalBoundaryRows, 2);
  assert.equal(out.publicTheoremEmissionAllowedByIndex, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
