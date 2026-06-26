import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from '../pcc-unrestricted-final-soundness-gate0.mjs';

import {
  CheckSignedExternalReviewFindings0,
  SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0,
  makeSignedExternalReviewFindingsInput0,
  makeSignedExternalReviewFindingsSuite0,
} from '../pcc-external-review-signed-findings0.mjs';

test('signed external review findings gate binds pending empty bundle without accepting release', async () => {
  const out = await CheckSignedExternalReviewFindings0(
    makeSignedExternalReviewFindingsInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSignedExternalReviewFindings0');
  assert.equal(out.NF.signedExternalReviewFindingsGateReady, true);
  assert.equal(out.NF.signedExternalReviewFindingsSchemaReady, true);
  assert.equal(out.NF.signedExternalReviewFindingsBundleReady, true);
  assert.equal(out.NF.signedExternalReviewFindingsReady, false);
  assert.equal(out.NF.externalReviewSignedFindingsReady, false);
  assert.equal(out.NF.externalReviewAcceptanceReady, false);
  assert.equal(out.NF.externalReviewAcceptanceReleased, false);
  assert.equal(out.NF.externalReviewAcceptanceBlocked, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.unrestrictedFinalSoundnessBlocked, true);
  assert.deepEqual(out.NF.remainingBlockerCoordinates, [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ]);
  assert.equal(out.NF.signedFindingCount, 0);
  assert.equal(out.NF.acceptanceFindingCount, 0);
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.externalReviewAcceptanceNotClaimed, true);
  assert.equal(out.NF.signedFindingSchemaDigest.alg, 'SHA256');
  assert.equal(out.NF.signedFindingsBundleDigest.alg, 'SHA256');
  assert.equal(out.NF.gateBindingDigest.alg, 'SHA256');
  assert.equal(out.NF.releasePublicTheoremEmissionBlockerDigest.alg, 'SHA256');
});

test('signed external review findings gate rejects forged signed acceptance bundle', async () => {
  const badBundle = {
    ...SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0,
    registryStatus: 'accepted',
    signedFindingCount: 1,
    acceptanceFindingCount: 1,
    signedExternalReviewFindingsReady: true,
    externalReviewAcceptanceReady: true,
    externalReviewAcceptanceReleased: true,
    externalReviewAcceptanceNotClaimed: false,
    publicTheoremEmissionAllowed: true,
    signedFindings: [{
      kind: 'ExternalReviewAcceptanceFinding0',
      version: 0,
      reviewerIdentityDigest: { alg: 'SHA256', hex: '0'.repeat(64) },
      reviewScopeDigest: { alg: 'SHA256', hex: '1'.repeat(64) },
      documentationCoordinate: 'PNP-DOC-CPR-2026-06-26-01',
      sealedSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
      sealedArtifactTag:
        'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
      finding: 'accept',
      findingDigest: { alg: 'SHA256', hex: '2'.repeat(64) },
      signatureDigest: { alg: 'SHA256', hex: '3'.repeat(64) },
    }],
  };
  const out = await CheckSignedExternalReviewFindings0(
    makeSignedExternalReviewFindingsInput0({
      SignedFindingsBundle: badBundle,
      SignedFindingsGate: makeSignedExternalReviewFindingsSuite0({
        SignedFindingsBundle: badBundle,
      }),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSignedExternalReviewFindings0.signedFindingsBundle');
  assert.deepEqual(out.Path, ['SignedFindingsBundle']);
  assert.equal(
    out.Witness.reason,
    'signed external-review findings checker requires the exact pending empty signed-findings bundle',
  );
});

test('signed external review findings gate rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeSignedExternalReviewFindingsInput0(),
    externalReviewAcceptanceReady: true,
  };
  const out = await CheckSignedExternalReviewFindings0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSignedExternalReviewFindings0.input');
  assert.deepEqual(out.Path, ['externalReviewAcceptanceReady']);
  assert.equal(
    out.Witness.reason,
    'signed external-review findings checker rejects caller-supplied readiness or truth assertions',
  );
});
