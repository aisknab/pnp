import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckSuccessorPublicReviewReportSeal0,
  SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0,
  SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_FILE_ENTRIES0,
  makeSuccessorPublicReviewReportSealInput0,
  makeSuccessorPublicReviewReportSealSuite0,
} from '../pcc-successor-report-seal0.mjs';

test('successor report seal constructors bind public-review payload hashes', () => {
  const input = makeSuccessorPublicReviewReportSealInput0();
  const suite = makeSuccessorPublicReviewReportSealSuite0();

  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.sealCoordinate, 'PNP-REPORT-SEAL-2026-06-27-01');
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.predecessorDocumentationCoordinate, 'PNP-DOC-CPR-2026-06-26-01');
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.reportTeXPayloadSha256.length, 64);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.reportPDFPayloadSha256.length, 64);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.historicalReleaseNotOverwritten, true);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.sourceAndArtifactAccessPublicWithoutRequest, true);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.directTheoremEmissionReframedAsReviewStatus, true);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.successorReportSealReady, true);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.successorReportArtifactReleaseReady, false);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.publicTheoremEmissionAllowed, false);
  assert.equal(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.finalTheoremReady, false);
  assert.deepEqual(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.activeFinalNodeIds, []);
  assert.deepEqual(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0.sealFileEntries, SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_FILE_ENTRIES0);
  for (const entry of SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_FILE_ENTRIES0) {
    assert.equal(entry.sha256.length, 64);
  }
  assert.equal(input.ReportSeal.sealFileEntryCount, 2);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.reportSealDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('successor report seal checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeSuccessorPublicReviewReportSealInput0(),
    publicTheoremEmissionAllowed: true,
  };
  const out = await CheckSuccessorPublicReviewReportSeal0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSuccessorPublicReviewReportSeal0.input');
  assert.deepEqual(out.Path, ['publicTheoremEmissionAllowed']);
  assert.equal(
    out.Witness.reason,
    'successor report seal checker rejects caller-supplied readiness or truth assertions',
  );
});
