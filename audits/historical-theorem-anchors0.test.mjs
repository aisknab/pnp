import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckHistoricalTheoremAnchors0 } from '../pcc-historical-theorem-anchors0.mjs';

test('historical theorem anchor checker accepts sanitized anchor index', async () => {
  const out = await CheckHistoricalTheoremAnchors0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01');
  assert.equal(out.anchorIndexReady, true);
  assert.equal(out.anchorIndexUsedForHistoricalBindingCompatibility, true);
  assert.equal(out.anchorIndexIsPublicTheoremEmissionSurface, false);
  assert.equal(out.publicTheoremEmissionAllowedByAnchorIndex, false);
  assert.equal(out.allReportBindingAnchorsRepresented, true);
  assert.equal(out.theoremBindingLedgerCoordinate, 'REPORT-THEOREM-BINDINGS-2026-06-27-01');
  assert.equal(out.theoremBindingCount, 20);
  assert.equal(out.anchorCount, 20);
  assert.equal(out.bindingAnchorCount, 20);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
