import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckExternalReviewFindingFileHashLedger0,
  EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0,
  EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0,
  makeExternalReviewFindingFileHashLedgerInput0,
  makeExternalReviewFindingFileHashLedgerSuite0,
} from '../pcc-external-review-finding-file-hash-ledger0.mjs';

test('finding-file hash ledger constructors bind current empty intake files', () => {
  const input = makeExternalReviewFindingFileHashLedgerInput0();
  const suite = makeExternalReviewFindingFileHashLedgerSuite0();

  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.entryCount, 2);
  assert.deepEqual(
    EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.entries,
    EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0,
  );
  assert.deepEqual(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0.map((entry) => entry.path), [
    'external-review/findings/MANIFEST.json',
    'external-review/findings/README.md',
  ]);
  for (const entry of EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0) {
    assert.equal(entry.sha256.length, 64);
  }
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.signedFindingFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.acceptanceFindingFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.externalReviewSignedFindingFileHashesReady, true);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.externalReviewSignedFindingFilesReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.externalReviewAcceptanceReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.publicTheoremEmissionAllowed, false);
  assert.equal(input.HashLedger.entryCount, 2);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.hashLedgerDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('finding-file hash ledger checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeExternalReviewFindingFileHashLedgerInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewFindingFileHashLedger0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewFindingFileHashLedger0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'finding-file hash ledger checker rejects caller-supplied readiness or truth assertions',
  );
});
