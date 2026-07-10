import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewEntrypoint0 } from '../pcc-public-review-entrypoint0.mjs';

test('legacy public review entrypoint rejects after the root review reset', async () => {
  const out = await CheckPublicReviewEntrypoint0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicReviewEntrypoint.DocFragmentMissing');
  assert.deepEqual(out.path, ['PUBLIC_REVIEW.md', 'not a theorem-activation surface']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
