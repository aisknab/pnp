import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckExternalReviewFindingTemplateLedger0,
  EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0,
  EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0,
  makeExternalReviewFindingTemplateInput0,
  makeExternalReviewFindingTemplateSuite0,
} from '../pcc-external-review-finding-template-ledger0.mjs';

test('finding-template constructors bind all non-activating template hashes', () => {
  const input = makeExternalReviewFindingTemplateInput0();
  const suite = makeExternalReviewFindingTemplateSuite0();

  assert.equal(EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0.entryCount, 3);
  assert.deepEqual(
    EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0.entries,
    EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0,
  );
  assert.deepEqual(EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0.map((entry) => entry.finding), [
    'accept',
    'reject',
    'revision-request',
  ]);
  for (const entry of EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0) {
    assert.equal(entry.sha256.length, 64);
  }
  assert.equal(EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0.externalReviewSignedFindingTemplatesReady, true);
  assert.equal(EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0.externalReviewSignedFindingFilesReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0.externalReviewAcceptanceReady, false);
  assert.equal(EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0.publicTheoremEmissionAllowed, false);
  assert.equal(input.TemplateLedger.entryCount, 3);
  assert.equal(input.Policy.publicTheoremEmissionAllowed, false);
  assert.equal(suite.binding.templateLedgerDigest.alg, 'SHA256');
  assert.equal(suite.binding.bindingDigest.alg, 'SHA256');
});

test('finding-template checker rejects caller-supplied readiness assertions before predecessor replay', async () => {
  const input = {
    ...makeExternalReviewFindingTemplateInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckExternalReviewFindingTemplateLedger0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckExternalReviewFindingTemplateLedger0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'finding-template checker rejects caller-supplied readiness or truth assertions',
  );
});
