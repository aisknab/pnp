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

const BuildHistoricalPNPLabsRunRecord0 = (options = {}) => BuildPNPLabsRunRecord0({
  ...options,
  historicalReplay: true,
});

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

test('BuildPNPLabsRunRecord0 produces an importable historical checker replay record', () => {
  const statusText = JSON.stringify(STATUS_PAYLOAD0, null, 2);
  const record = BuildHistoricalPNPLabsRunRecord0({
    verdict: VERDICT0,
    statusPayload: STATUS_PAYLOAD0,
    statusPayloadText: statusText,
    pnpCommit: 'abcdef1234567890',
    runnerNameOrHandle: 'Ada Example',
    dateUtc: '2026-07-06',
    environment: { runner: 'test', node: 'v20.0.0', npm: '10.0.0' },
  });

  assert.equal(record.kind, 'PNPHistoricalCheckerReplayRecord0');
  assert.equal(record.recordClass, 'historical-assertion-checker-replay');
  assert.equal(record.recordId, 'ada-example-2026-07-06-abcdef123456');
  assert.equal(record.verdict.tag, 'accept');
  assert.equal(record.verdict.publicTheoremEmissionAllowed, true);
  assert.equal(record.verdict.publicTheoremStatement, 'P = NP');
  assert.deepEqual(record.verdict.remainingBlockers, []);
  assert.equal(record.statusSnapshot.coordinate, 'PNP-ACTIVATED-STATUS-2026-07-05-01');
  assert.equal(record.statusSnapshot.externalReviewIsMathematicalPremise, false);
  assert.equal(record.statusPayloadSha256, Sha256Text0(statusText));
  assert.match(record.statusPayloadSha256, /^[0-9a-f]{64}$/);
  assert.equal(record.proofScriptOutputs['proof:activated-pnp-status'].includes('npm run pnp:verify'), true);
  assert.equal(record.nonClaims.some((line) => line.includes('not an external-consensus claim')), true);
});

test('activated status payload wins over legacy pnp:verify public-review fields for upload', () => {
  const record = BuildHistoricalPNPLabsRunRecord0({
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

test('issue body labels the record as a historical checker replay', () => {
  const record = BuildHistoricalPNPLabsRunRecord0({
    verdict: VERDICT0,
    statusPayload: STATUS_PAYLOAD0,
    statusPayloadText: JSON.stringify(STATUS_PAYLOAD0),
    pnpCommit: 'abcdef1234567890',
    runnerNameOrHandle: 'Ada Example',
    dateUtc: '2026-07-06',
  });
  const title = BuildPNPLabsIssueTitle0(record);
  const body = BuildPNPLabsIssueBody0(record, { verdictText: JSON.stringify(VERDICT0), statusPayloadText: JSON.stringify(STATUS_PAYLOAD0) });

  assert.equal(title, 'PNP historical checker replay: Ada Example 2026-07-06');
  for (const fragment of [
    'PNP historical checker replay',
    'PNP Labs upload is frozen during formal reconstruction',
    'publicTheoremEmissionAllowed = true',
    'publicTheoremStatement = P = NP',
    'publicTheoremConclusion = P = NP',
    'remainingBlockers = []',
    'PNP-ACTIVATED-STATUS-2026-07-05-01',
    'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
    'Importable local replay record',
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

test('UploadPNPLabsIssue0 remains frozen even with a token and historical opt-in', async () => {
  const calls = [];
  const out = await UploadPNPLabsIssue0({
    title: 'PNP historical checker replay: Ada 2026-07-06',
    body: 'body',
    token: 'test-token',
    historicalReplay: true,
    fetchImpl: async (url, options) => {
      calls.push({ url, options });
      return {
        ok: true,
        status: 201,
        json: async () => ({ html_url: 'https://github.com/aisknab/pnplabs/issues/123', number: 123 }),
      };
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PNPLabsUpload.FrozenDuringFormalReconstruction');
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(calls.length, 0);
});

test('UploadPNPLabsIssue0 does not expose a manual upload fallback', async () => {
  const out = await UploadPNPLabsIssue0({
    title: 'PNP historical checker replay: Ada 2026-07-06',
    body: 'body',
    token: '',
    historicalReplay: true,
    fetchImpl: async () => {
      throw new Error('fetch must not be called without token');
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PNPLabsUpload.FrozenDuringFormalReconstruction');
  assert.equal(out.publicTheoremStatement, null);
});

test('formal reconstruction null theorem fields never fall back to the historical claim', () => {
  const status = {
    kind: 'PNPFormalReconstructionStatus0',
    coordinate: 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-10-01',
    claimStatus: 'formal-reconstruction-in-progress',
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    publicTheoremConclusion: null,
    finalTheoremReady: false,
    unrestrictedFinalSoundnessDischarged: false,
    externalReviewIsMathematicalPremise: false,
    remainingBlockers: ['Formal.RootTheoremAndAxiomAudit'],
  };
  const record = BuildHistoricalPNPLabsRunRecord0({
    verdict: VERDICT0,
    statusPayload: status,
    statusPayloadText: JSON.stringify(status),
  });

  assert.equal(record.verdict.claimStatus, 'formal-reconstruction-in-progress');
  assert.equal(record.verdict.publicTheoremEmissionAllowed, false);
  assert.equal(record.verdict.publicTheoremStatement, null);
  assert.equal(record.verdict.publicTheoremConclusion, null);
  assert.equal(record.verdict.finalTheoremReady, false);
  assert.equal(record.verdict.unrestrictedFinalSoundnessDischarged, false);
});

test('PNP Labs build and upload routes reject without historical replay opt-in', async () => {
  const built = BuildPNPLabsRunRecord0();
  const uploaded = await UploadPNPLabsIssue0();

  for (const out of [built, uploaded]) {
    assert.equal(out.tag, 'reject');
    assert.match(out.coord, /\.HistoricalReplayRequired$/);
    assert.equal(out.publicTheoremEmissionAllowed, false);
  }
});
