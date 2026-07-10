import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckPublicTheoremEmissionDenial0 } from '../pcc-public-theorem-emission-denial0.mjs';

test('legacy theorem-emission denial chain rejects after the formal reconstruction reset', async () => {
  const out = await CheckPublicTheoremEmissionDenial0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremEmissionDenial.PreflightVerdictMismatch');
  assert.deepEqual(out.path, ['CheckPublicTheoremEmissionPreflight0']);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});
