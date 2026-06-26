import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckExternalReviewFindingFiles0,
  EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0,
  EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0,
  makeExternalReviewFindingFilesInput0,
  makeExternalReviewFindingFilesSuite0,
} from '../pcc-external-review-finding-files0.mjs';

test('finding-file constructors bind the empty signed finding-file manifest', () => {
  const input = makeExternalReviewFindingFilesInput0();
  const suite = makeExternalReviewFindingFilesSuite0();

  assert.equal(EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0, 'external-review/findings/');
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.signedFindingFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.acceptanceFindingFileCount, 0);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.externalReviewSignedFindingFilesReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.externalReviewSignedFindingsReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.externalReviewAcceptanceReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.externalReviewAcceptanceReleased, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.externalReviewAcceptanceNotClaimed, true);
  assert.equal(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.publicTheoremEmissionAllowed, false);
  assert.equal(input.FindingFileManifest.signedFindingFiles.length, 0);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.findingFileManifestDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('finding-file checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeExternalReviewFindingFilesInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewFindingFiles0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewFindingFiles0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'signed finding-file checker rejects caller-supplied readiness or truth assertions',
  );
});
