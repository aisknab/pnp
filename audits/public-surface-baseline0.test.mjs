import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicSurfaceBaseline0 } from '../pcc-public-surface-baseline0.mjs';

test('legacy public surface baseline rejects after the formal reconstruction reset', async () => {
  const out = await CheckPublicSurfaceBaseline0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicSurfaceBaseline.BaselineShape');
  assert.deepEqual(out.path, ['PUBLIC_SURFACE_BASELINE0']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
