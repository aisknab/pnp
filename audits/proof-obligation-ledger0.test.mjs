import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckProofObligationLedger0 } from '../pcc-proof-obligation-ledger0.mjs';

test('proof obligation ledger accepts current source ledger', async () => {
  const out = await CheckProofObligationLedger0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01');
  assert.equal(out.proofObligationLedgerReady, true);
  assert.equal(out.fullProofObligationDischargeProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByLedger, false);
  assert.equal(out.obligationCount, 28);
  assert.ok(out.obligationIds.includes('OBL-028-NORFFDirectBindingSeed'));
  assert.ok(out.sourceFileCount > 0);
  assert.ok(out.testFileCount > 0);
  assert.equal(out.obligationDigestLedgerSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
