import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionPreflight0 } from '../pcc-public-theorem-emission-preflight0.mjs';

test('legacy theorem-emission preflight rejects after the formal reconstruction reset', async () => {
  const out = await CheckPublicTheoremEmissionPreflight0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremEmissionPreflight.DocFragmentMissing');
  assert.deepEqual(out.path, ['release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.md', 'not a theorem-activation surface']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
