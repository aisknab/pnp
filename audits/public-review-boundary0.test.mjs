import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewBoundary0 } from '../pcc-public-review-boundary0.mjs';

test('legacy public review boundary rejects after the formal baseline reset', async () => {
  const out = await CheckPublicReviewBoundary0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicReviewBoundary.PublicSurfaceBaselineMismatch');
  assert.deepEqual(out.path, ['CheckPublicSurfaceBaseline0']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
