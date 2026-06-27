import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckExternalReviewTemplateShape0,
  EXTERNAL_REVIEW_TEMPLATE_REQUIRED_DIGEST_FIELDS0,
  EXTERNAL_REVIEW_TEMPLATE_SHAPE_ENTRIES0,
  EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0,
  makeExternalReviewTemplateShapeInput0,
  makeExternalReviewTemplateShapeSuite0,
} from '../pcc-external-review-template-shape0.mjs';

test('template-shape constructors bind inert placeholder template semantics', () => {
  const input = makeExternalReviewTemplateShapeInput0();
  const suite = makeExternalReviewTemplateShapeSuite0();

  assert.equal(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0.entryCount, 3);
  assert.equal(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0.externalReviewSignedFindingTemplatesReady, true);
  assert.equal(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0.externalReviewSignedFindingTemplateShapesReady, true);
  assert.equal(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0.externalReviewSignedFindingFilesReady, false);
  assert.equal(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0.externalReviewAcceptanceReady, false);
  assert.equal(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0.publicTheoremEmissionAllowed, false);
  assert.deepEqual(EXTERNAL_REVIEW_TEMPLATE_SHAPE_ENTRIES0.map((entry) => entry.finding), [
    'accept',
    'reject',
    'revision-request',
  ]);
  for (const entry of EXTERNAL_REVIEW_TEMPLATE_SHAPE_ENTRIES0) {
    assert.equal(entry.inertTemplateOnly, true);
    assert.equal(entry.signedFindingSupplied, false);
    assert.deepEqual(entry.requiredDigestFields, EXTERNAL_REVIEW_TEMPLATE_REQUIRED_DIGEST_FIELDS0);
    assert.equal(entry.digestAlg, 'SHA256');
    assert.equal(entry.digestHexPlaceholder, '<64 lowercase hex characters>');
    assert.equal(entry.sha256.length, 64);
  }
  assert.equal(input.TemplateShapeLedger.entryCount, 3);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.templateShapeLedgerDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('template-shape checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeExternalReviewTemplateShapeInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewTemplateShape0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewTemplateShape0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'template-shape checker rejects caller-supplied readiness or truth assertions',
  );
});
