import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckReleaseBlockerClearance0 } from '../pcc-release-blocker-clearance0.mjs';

test('legacy release-blocker protocol rejects after the formal reconstruction reset', async () => {
  const out = await CheckReleaseBlockerClearance0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReleaseBlockerClearance.DocFragmentMissing');
  assert.deepEqual(out.path, ['release/RELEASE_BLOCKER_CLEARANCE.md', 'not a theorem-activation surface']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
