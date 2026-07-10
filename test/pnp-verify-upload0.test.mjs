import assert from 'node:assert/strict';
import { test } from 'node:test';
import { BuildPNPLabsIssueBody0, BuildPNPLabsIssueTitle0, BuildPNPLabsIssueUrl0, BuildPNPLabsRecordId0, BuildPNPLabsRunRecord0, BuildProofScriptOutputs0, IsYesAnswer0, Sha256Text0, Slug0, UploadPNPLabsIssue0 } from '../pnp-verify-upload0.mjs';

const STATUS_PAYLOAD0 = {
  kind: 'PNPFormalReconstructionStatus0',
  coordinate: 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01',
  claimStatus: 'target-theorem-not-formally-established',
  targetTheorem: 'P = NP',
  publicTheoremEmissionAllowed: false,
  publicTheoremStatement: null,
  publicTheoremConclusion: null,
  finalTheoremReady: false,
  rootLeanTheoremPresent: false,
  formalReleaseGatePassed: false,
  historicalActivationCoordinate: 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
  historicalActivationSuperseded: true,
  projectSpecificAxiomsRemaining: true,
  humanReviewRequiredForMathematicalValidity: false,
  remainingFormalObligations: ['Formal.ConcreteComplexityModel'],
};
const VERDICT0 = { tag: 'accept', claimStatus: 'formal-reconstruction-status-accepted', targetTheorem: 'P = NP', publicTheoremEmissionAllowed: false, publicTheoremStatement: null, publicTheoremConclusion: null, finalTheoremReady: false, rootLeanTheoremPresent: false, formalReleaseGatePassed: false, remainingFormalObligations: ['Formal.ConcreteComplexityModel'] };

test('yes/no parser accepts only explicit affirmative answers', () => {
  assert.equal(IsYesAnswer0('y'), true); assert.equal(IsYesAnswer0(' yes '), true); assert.equal(IsYesAnswer0('YES'), true); assert.equal(IsYesAnswer0(''), false); assert.equal(IsYesAnswer0('n'), false); assert.equal(IsYesAnswer0('yeah'), false);
});
test('run record id and slug are stable and upload-safe', () => {
  assert.equal(Slug0('Ada Example / @ada'), 'ada-example-ada');
  assert.equal(BuildPNPLabsRecordId0({ runnerNameOrHandle: 'Ada Example', dateUtc: '2026-07-09', pnpCommit: 'abcdef1234567890' }), 'ada-example-2026-07-09-abcdef123456');
});
test('BuildPNPLabsRunRecord0 produces a non-activation reconstruction record', () => {
  const statusText = JSON.stringify(STATUS_PAYLOAD0, null, 2);
  const record = BuildPNPLabsRunRecord0({ verdict: VERDICT0, statusPayload: STATUS_PAYLOAD0, statusPayloadText: statusText, pnpCommit: 'abcdef1234567890', runnerNameOrHandle: 'Ada Example', dateUtc: '2026-07-09', environment: { runner: 'test', node: 'v20.0.0', npm: '10.0.0' } });
  assert.equal(record.kind, 'PNPFormalReconstructionVerificationRunRecord0');
  assert.equal(record.recordClass, 'source-checker-formal-reconstruction-run');
  assert.equal(record.recordId, 'ada-example-2026-07-09-abcdef123456');
  assert.equal(record.verdict.publicTheoremEmissionAllowed, false);
  assert.equal(record.verdict.publicTheoremStatement, null);
  assert.equal(record.verdict.finalTheoremReady, false);
  assert.equal(record.verdict.rootLeanTheoremPresent, false);
  assert.equal(record.verdict.formalReleaseGatePassed, false);
  assert.deepEqual(record.verdict.remainingFormalObligations, ['Formal.ConcreteComplexityModel']);
  assert.equal(record.formalStatus.coordinate, 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01');
  assert.equal(record.formalStatus.historicalActivationSuperseded, true);
  assert.equal(record.formalStatus.humanReviewRequiredForMathematicalValidity, false);
  assert.equal(record.statusPayloadSha256, Sha256Text0(statusText));
  assert.equal(record.proofScriptOutputs['proof:formal-reconstruction-status'].includes('npm run pnp:verify'), true);
});
test('status payload false values override a stale historical verifier verdict', () => {
  const record = BuildPNPLabsRunRecord0({ verdict: { tag: 'accept', claimStatus: 'historical-activated', publicTheoremEmissionAllowed: true, publicTheoremStatement: 'P = NP', finalTheoremReady: true, formalReleaseGatePassed: true }, statusPayload: STATUS_PAYLOAD0, statusPayloadText: JSON.stringify(STATUS_PAYLOAD0), pnpCommit: 'abcdef1234567890', runnerNameOrHandle: 'Ada Example', dateUtc: '2026-07-09' });
  assert.equal(record.verdict.claimStatus, 'target-theorem-not-formally-established');
  assert.equal(record.verdict.publicTheoremEmissionAllowed, false);
  assert.equal(record.verdict.publicTheoremStatement, null);
  assert.equal(record.verdict.finalTheoremReady, false);
  assert.equal(record.verdict.formalReleaseGatePassed, false);
});
test('missing status fields fail closed rather than defaulting to activation', () => {
  const record = BuildPNPLabsRunRecord0({ verdict: {}, statusPayload: {}, statusPayloadText: '{}', pnpCommit: 'abcdef1234567890', runnerNameOrHandle: 'Ada Example', dateUtc: '2026-07-09' });
  assert.equal(record.verdict.publicTheoremEmissionAllowed, false);
  assert.equal(record.verdict.publicTheoremStatement, null);
  assert.equal(record.verdict.finalTheoremReady, false);
  assert.equal(record.verdict.formalReleaseGatePassed, false);
});
test('issue body contains the reconstruction boundary', () => {
  const record = BuildPNPLabsRunRecord0({ verdict: VERDICT0, statusPayload: STATUS_PAYLOAD0, statusPayloadText: JSON.stringify(STATUS_PAYLOAD0), pnpCommit: 'abcdef1234567890', runnerNameOrHandle: 'Ada Example', dateUtc: '2026-07-09' });
  const title = BuildPNPLabsIssueTitle0(record);
  const body = BuildPNPLabsIssueBody0(record, { verdictText: JSON.stringify(VERDICT0), statusPayloadText: JSON.stringify(STATUS_PAYLOAD0) });
  assert.equal(title, 'PNP formal reconstruction verification run: Ada Example 2026-07-09');
  for (const fragment of ['PNP formal reconstruction verification run', 'targetTheorem = P = NP', 'publicTheoremEmissionAllowed = false', 'publicTheoremStatement = null', 'finalTheoremReady = false', 'rootLeanTheoremPresent = false', 'formalReleaseGatePassed = false', 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01', 'historicalActivationSuperseded = true', 'does not establish `P = NP`']) assert.equal(body.includes(fragment), true, `missing issue body fragment: ${fragment}`);
  assert.equal(BuildPNPLabsIssueUrl0(title).startsWith('https://github.com/aisknab/pnplabs/issues/new?'), true);
});
test('proof script output placeholders cover the current status commands', () => {
  const outputs = BuildProofScriptOutputs0({ pnpCommit: 'abcdef1234567890' });
  assert.deepEqual(Object.keys(outputs).sort(), ['proof:formal-reconstruction-status', 'proof:public-theorem-withdrawal']);
});
test('UploadPNPLabsIssue0 creates an issue with a token', async () => {
  const calls = [];
  const out = await UploadPNPLabsIssue0({ title: 'PNP formal reconstruction verification run: Ada 2026-07-09', body: 'body', token: 'test-token', fetchImpl: async (url, options) => { calls.push({ url, options }); return { ok: true, status: 201, json: async () => ({ html_url: 'https://github.com/aisknab/pnplabs/issues/123', number: 123 }) }; } });
  assert.equal(out.tag, 'uploaded'); assert.equal(out.url, 'https://github.com/aisknab/pnplabs/issues/123'); assert.equal(calls.length, 1); assert.equal(JSON.parse(calls[0].options.body).labels.includes('pnp-verification-run'), true);
});
test('UploadPNPLabsIssue0 falls back to manual issue URL without a token', async () => {
  const out = await UploadPNPLabsIssue0({ title: 'PNP formal reconstruction verification run: Ada 2026-07-09', body: 'body', token: '', fetchImpl: async () => { throw new Error('fetch must not be called without token'); } });
  assert.equal(out.tag, 'manual'); assert.equal(out.reason, 'missing-token'); assert.equal(out.url.includes('template=pnp-verification-run.yml'), true);
});
