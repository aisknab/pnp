import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckHistoricalTheoremAnchors0 } from '../pcc-historical-theorem-anchors0.mjs';

test('historical theorem anchor index accepts current theorem binding anchors', async () => {
  const out = await CheckHistoricalTheoremAnchors0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01');
  assert.equal(out.anchorIndexReady, true);
  assert.equal(out.anchorIndexIsTheoremEmissionSurface, false);
  assert.equal(out.publicTheoremEmissionAllowedByAnchorIndex, false);
  assert.equal(out.anchorCount, 20);
  assert.equal(out.boundTheoremBindingCount, 20);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
