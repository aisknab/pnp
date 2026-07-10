import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionGate0 } from '../pcc-public-theorem-emission-gate0.mjs';

test('legacy theorem-emission gate rejects after the formal reconstruction reset', async () => {
  const out = await CheckPublicTheoremEmissionGate0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremEmissionGate.CurrentPreflightMismatch');
  assert.deepEqual(out.path, ['CheckPublicTheoremEmissionPreflight0']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
