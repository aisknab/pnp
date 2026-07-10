import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicReviewChecklist0 } from '../pcc-public-review-checklist0.mjs';

test('legacy public review checklist rejects after the formal reconstruction reset', async () => {
  const out = await CheckPublicReviewChecklist0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicReviewChecklist.DocFragmentMissing');
  assert.deepEqual(out.path, ['review/PUBLIC_REVIEW_CHECKLIST.md', 'not a theorem-activation surface']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
