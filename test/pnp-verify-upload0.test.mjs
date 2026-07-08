import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  BuildPNPLabsIssueBody0,
  BuildPNPLabsIssueTitle0,
  BuildPNPLabsIssueUrl0,
  BuildPNPLabsRecordId0,
  BuildPNPLabsRunRecord0,
  BuildProofScriptOutputs0,
  IsYesAnswer0,
  Sha256Text0,
  Slug0,
  UploadPNPLabsIssue0,
} from '../pnp-verify-upload0.mjs';

const STATUS_PAYLOAD0 = {
  kind: 'PNPActivatedStatus0',
  coordinate: 'PNP-ACTIVATED-STATUS-2026-07-05-01',
  claimStatus: 'public-theorem-emission-activated-under-checker-trust-model',
  publicTheoremActivationCoordinate: 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
  unrestrictedFinalSoundnessReleaseCoordinate: 'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01',
  publicTheoremEmissionAllowed: true,
  publicTheoremStatement: 'P = NP',
  publicTheoremConclusion: 'P = NP',
  finalTheoremReady: true,
  unrestrictedFinalSoundnessDischarged: true,
  externalReviewIsMathematicalPremise: false,
  remainingBlockers: [],
};

const VERDICT0 = {
  tag: 'accept',
  claimStatus: 'public-theorem-emission-activated-under-checker-trust-model',
  publicTheoremEmissionAllowed: true,
  publicTheoremStatement: 'P = NP',
  publicTheoremConclusion: 'P = NP',
  finalTheoremReady: true,
  unrestrictedFinalSoundnessDischarged: true,
  remainingBlockers: [],
};

const LEGACY_VERIFY_ALL_VERDICT0 = {
  tag: 'accept',
  claimStatus: 'internal-proof-certificate-stack-accepted-under-public-review-boundary',
  publicTheoremEmissionAllowed: false,
  publicTheoremStatement: undefined,
  publicTheoremConclusion: undefined,
  finalTheoremReady: false,
  unrestrictedFinalSoundnessDischarged: false,
  remainingBlockers: ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'],
};

test('yes/no parser accepts only explicit affirmative answers', () => {
  assert.equal(IsYesAnswer0('y'), true);
  assert.equal(IsYesAnswer0(' yes '), true);
  assert.equal(IsYesAnswer0('YES'), true);
  assert.equal(IsYesAnswer0(''), false);
  assert.equal(IsYesAnswer0('n'), false);
  assert.equal(IsYesAnswer0('yeah'), false);
});

test('run record id and slug are stable and upload-safe', () => {
  assert.equal(Slug0('Ada Example / @ada'), 'ada-example-ada');
  assert.equal(BuildPNPLabsRecordId0({ runnerNameOrHandle: 'Ada Example', dateUtc: '2026-07-06', pnpCommit: 'abcdef1234567890' }), 'ada-example-2026-07-06-abcdef123456');
});

test('BuildPNPLabsRunRecord0 produces an importable activated verifier run record', () => {
  const statusText = JSON.stringify(STATUS_PAYLOAD0, null, 2);
  const record = BuildPNPLabsRunRecord0({
    verdict: VERDICT0,
    statusPayload: STATUS_PAYLOAD0,
    statusPayloadText: statusText,
    pnpCommit: 'abcdef1234567890',
    runnerNameOrHandle: 'Ada Example',
    dateUtc: '2026-07-06',
    environment: { runner: 'test', node: 'v20.0.0', npm: '10.0.0' },
  });

  assert.equal(record.kind, 'PNPActivatedVerificationRunRecord0');
  assert.equal(record.recordClass, 'source-checker-verifier-run');
  assert.equal(record.recordId, 'ada-example-2026-07-06-abcdef123456');
  assert.equal(record.verdict.tag, 'accept');
  assert.equal(record.verdict.publicTheoremEmissionAllowed, true);
  assert.equal(record.verdict.publicTheoremStatement, 'P = NP');
  assert.deepEqual(record.verdict.remainingBlockers, []);
  assert.equal(record.activatedStatus.coordinate, 'PNP-ACTIVATED-STATUS-2026-07-05-01');
  assert.equal(record.activatedStatus.externalReviewIsMathematicalPremise, false);
  assert.equal(record.statusPayloadSha256, Sha256Text0(statusText));
  assert.match(record.statusPayloadSha256, /^[0-9a-f]{64}$/);
  assert.equal(record.proofScriptOutputs['proof:activated-pnp-status'].includes('npm run pnp:verify'), true);
  assert.equal(record.nonClaims.some((line) => line.includes('not an external-consensus claim')), true);
});

test('activated status payload wins over legacy pnp:verify public-review fields for upload', () => {
  const record = BuildPNPLabsRunRecord0({
    verdict: LEGACY_VERIFY_ALL_VERDICT0,
    statusPayload: STATUS_PAYLOAD0,
    statusPayloadText: JSON.stringify(STATUS_PAYLOAD0),
    pnpCommit: 'abcdef1234567890',
    runnerNameOrHandle: 'Ada Example',
    dateUtc: '2026-07-06',
  });

  assert.equal(record.verdict.tag, 'accept');
  assert.equal(record.verdict.claimStatus, 'public-theorem-emission-activated-under-checker-trust-model');
  assert.equal(record.verdict.publicTheoremEmissionAllowed, true);
  assert.equal(record.verdict.publicTheoremStatement, 'P = NP');
  assert.equal(record.verdict.publicTheoremConclusion, 'P = NP');
  assert.equal(record.verdict.finalTheoremReady, true);
  assert.equal(record.verdict.unrestrictedFinalSoundnessDischarged, true);
  assert.deepEqual(record.verdict.remainingBlockers, []);
});

test('issue body contains the importable record and activated boundary fields', () => {
  const record = BuildPNPLabsRunRecord0({
    verdict: VERDICT0,
    statusPayload: STATUS_PAYLOAD0,
    statusPayloadText: JSON.stringify(STATUS_PAYLOAD0),
    pnpCommit: 'abcdef1234567890',
    runnerNameOrHandle: 'Ada Example',
    dateUtc: '2026-07-06',
  });
  const title = BuildPNPLabsIssueTitle0(record);
  const body = BuildPNPLabsIssueBody0(record, { verdictText: JSON.stringify(VERDICT0), statusPayloadText: JSON.stringify(STATUS_PAYLOAD0) });

  assert.equal(title, 'PNP activated verification run: Ada Example 2026-07-06');
  for (const fragment of [
    'PNP activated verification run',
    'publicTheoremEmissionAllowed = true',
    'publicTheoremStatement = P = NP',
    'publicTheoremConclusion = P = NP',
    'remainingBlockers = []',
    'PNP-ACTIVATED-STATUS-2026-07-05-01',
    'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
    'Importable run record',
    'not an external-consensus claim or peer-review acceptance',
  ]) {
    assert.equal(body.includes(fragment), true, `missing issue body fragment: ${fragment}`);
  }
  assert.equal(BuildPNPLabsIssueUrl0(title).startsWith('https://github.com/aisknab/pnplabs/issues/new?'), true);
});

test('proof script output placeholders cover required activation scripts', () => {
  const outputs = BuildProofScriptOutputs0({ pnpCommit: 'abcdef1234567890' });
  assert.deepEqual(Object.keys(outputs).sort(), [
    'proof:activated-pnp-status',
    'proof:public-theorem-activation',
    'proof:uniform-complexity-conclusion',
    'proof:unrestricted-final-soundness-release',
  ]);
  for (const value of Object.values(outputs)) assert.equal(value.includes('abcdef1234567890'), true);
});

test('UploadPNPLabsIssue0 creates an issue with a token', async () => {
  const calls = [];
  const out = await UploadPNPLabsIssue0({
    title: 'PNP activated verification run: Ada 2026-07-06',
    body: 'body',
    token: 'test-token',
    fetchImpl: async (url, options) => {
      calls.push({ url, options });
      return {
        ok: true,
        status: 201,
        json: async () => ({ html_url: 'https://github.com/aisknab/pnplabs/issues/123', number: 123 }),
      };
    },
  });

  assert.equal(out.tag, 'uploaded');
  assert.equal(out.url, 'https://github.com/aisknab/pnplabs/issues/123');
  assert.equal(calls.length, 1);
  assert.equal(calls[0].url, 'https://api.github.com/repos/aisknab/pnplabs/issues');
  assert.equal(JSON.parse(calls[0].options.body).labels.includes('pnp-verification-run'), true);
});

test('UploadPNPLabsIssue0 falls back to manual issue URL without a token', async () => {
  const out = await UploadPNPLabsIssue0({
    title: 'PNP activated verification run: Ada 2026-07-06',
    body: 'body',
    token: '',
    fetchImpl: async () => {
      throw new Error('fetch must not be called without token');
    },
  });

  assert.equal(out.tag, 'manual');
  assert.equal(out.reason, 'missing-token');
  assert.equal(out.url.includes('template=pnp-verification-run.yml'), true);
});
