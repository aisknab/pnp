import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckExternalReviewVerificationKeyFileHashLedger0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0,
  makeExternalReviewVerificationKeyFileHashLedgerInput0,
  makeExternalReviewVerificationKeyFileHashLedgerSuite0,
} from '../pcc-external-review-verification-key-file-hash-ledger0.mjs';

test('verification-key file hash ledger constructors bind current empty intake files', () => {
  const input = makeExternalReviewVerificationKeyFileHashLedgerInput0();
  const suite = makeExternalReviewVerificationKeyFileHashLedgerSuite0();

  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.entryCount, 2);
  assert.deepEqual(
    EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.entries,
    EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0,
  );
  assert.deepEqual(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0.map((entry) => entry.path), [
    'external-review/keys/MANIFEST.json',
    'external-review/keys/README.md',
  ]);
  for (const entry of EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0) {
    assert.equal(entry.sha256.length, 64);
  }
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.verificationKeyFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.trustedReviewerKeyFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.externalReviewVerificationKeyFileHashesReady, true);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.externalReviewVerificationKeyFilesReady, false);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.externalReviewAcceptanceReady, false);
  assert.equal(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0.publicTheoremEmissionAllowed, false);
  assert.equal(input.HashLedger.entryCount, 2);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.hashLedgerDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('verification-key file hash ledger checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeExternalReviewVerificationKeyFileHashLedgerInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewVerificationKeyFileHashLedger0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewVerificationKeyFileHashLedger0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'verification-key file hash-ledger checker rejects caller-supplied readiness or truth assertions',
  );
});
