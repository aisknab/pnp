import assert from 'node:assert/strict';
import { test } from 'node:test';

import { RunSection22DirectBindings0 } from '../scripts/verify-section22-direct-bindings.mjs';

test('Section 22 direct-binding runner accepts every indexed row checker', async () => {
  const out = await RunSection22DirectBindings0({ writeOutput: false, includeRowTests: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01');
  assert.equal(out.directBindingIndexCoordinate, 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01');
  assert.equal(out.section22RowsExecuted, true);
  assert.equal(out.section22RowCount, 27);
  assert.equal(out.checkerAcceptCount, 27);
  assert.equal(out.allSection22RowCheckersAccepted, true);
  assert.equal(out.allSection22RowsDirectCheckerComplete, undefined);
  assert.equal(out.directCheckerBindingCompleteCount, 0);
  assert.equal(out.publicTheoremEmissionAllowedByRunner, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
  assert.equal(out.rowResults.length, 27);
});
