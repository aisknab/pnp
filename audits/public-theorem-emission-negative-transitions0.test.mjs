import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionNegativeTransitions0 } from '../pcc-public-theorem-emission-negative-transitions0.mjs';

test('legacy theorem-emission transition audit rejects after the formal reconstruction reset', async () => {
  const out = await CheckPublicTheoremEmissionNegativeTransitions0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremEmissionNegativeTransitions.CurrentPreflightMismatch');
  assert.deepEqual(out.path, ['CheckPublicTheoremEmissionPreflight0']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
