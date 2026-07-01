import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicSurfaceBaseline0 } from '../pcc-public-surface-baseline0.mjs';

test('public surface baseline checker accepts current public package surface', async () => {
  const out = await CheckPublicSurfaceBaseline0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01');
  assert.equal(out.publicSurfaceBaselineReady, true);
  assert.equal(out.publicSurfaceBaselineCoordinate, 'PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01');
  assert.equal(out.publicEntryReleaseSurfaceAccepted, true);
  assert.equal(out.publicSurfaceFrozen, true);
  assert.equal(out.underlyingChecker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.publicEntryExportCount > 0, true);
  assert.equal(out.packageExportCount > 0, true);
  assert.equal(out.packageBinCount > 0, true);
  assert.equal(out.packageScriptCount > 0, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
