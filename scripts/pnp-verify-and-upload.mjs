#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

import {
  EnforceHistoricalReplayCli0,
  LegacyReplayRequiredReject0,
} from '../pcc-legacy-replay-gate0.mjs';

const PNPLABS_REPO0 = 'aisknab/pnplabs';
const UPLOAD_DIR0 = 'artifacts/pnplabs-upload';
const LATEST_VERDICT0 = 'artifacts/pnp-verify-all/latest-verdict.json';
const STATUS_PAYLOAD0 = 'public/pnp-status.json';
const ACTIVATED_STATUS_PAYLOAD0 = 'status/ACTIVATED_PNP_STATUS.json';
const FOCUSED_PROOF_SCRIPT_KEYS0 = Object.freeze([
  'proof:activated-pnp-status',
  'proof:public-theorem-activation',
  'proof:unrestricted-final-soundness-release',
  'proof:uniform-complexity-conclusion',
]);

export function IsYesAnswer0(answer) {
  return /^(y|yes)$/iu.test(String(answer ?? '').trim());
}

export function Sha256Text0(text) {
  return createHash('sha256').update(Buffer.from(String(text), 'utf8')).digest('hex');
}

export function Slug0(value) {
  const slug = String(value ?? 'anonymous')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '-')
    .replace(/^-+|-+$/gu, '');
  return slug || 'anonymous';
}

export function BuildPNPLabsRecordId0({ runnerNameOrHandle, dateUtc, pnpCommit }) {
  const date = String(dateUtc ?? '').slice(0, 10) || 'unknown-date';
  const shortSha = String(pnpCommit ?? 'unknown').slice(0, 12);
  return `${Slug0(runnerNameOrHandle)}-${date}-${shortSha}`;
}

export function BuildProofScriptOutputs0({ pnpCommit, verdictPath = LATEST_VERDICT0 } = {}) {
  return Object.fromEntries(FOCUSED_PROOF_SCRIPT_KEYS0.map((key) => [
    key,
    `covered by npm run pnp:verify for ${pnpCommit ?? 'unknown commit'}; see ${verdictPath}`,
  ]));
}

export function BuildPNPLabsRunRecord0({
  verdict,
  statusPayload,
  statusPayloadText,
  pnpCommit,
  runnerNameOrHandle,
  dateUtc = new Date().toISOString().slice(0, 10),
  environment,
  commandsRun,
  proofScriptOutputs,
  artifactsOrLogs,
  historicalReplay = false,
} = {}) {
  if (historicalReplay !== true) return LegacyReplayRequiredReject0('BuildPNPLabsRunRecord0');
  const status = statusPayload ?? {};
  const verdictObject = verdict ?? {};
  const runner = runnerNameOrHandle || 'local verifier runner';
  const commit = pnpCommit || 'unknown';
  const recordId = BuildPNPLabsRecordId0({ runnerNameOrHandle: runner, dateUtc, pnpCommit: commit });
  const statusSha = Sha256Text0(statusPayloadText ?? JSON.stringify(status));
  const activatedRemainingBlockers = Array.isArray(status.remainingBlockers) ? status.remainingBlockers : (Array.isArray(verdictObject.remainingBlockers) ? verdictObject.remainingBlockers : []);
  return {
    kind: 'PNPHistoricalCheckerReplayRecord0',
    recordId,
    recordClass: 'historical-assertion-checker-replay',
    runnerNameOrHandle: runner,
    dateUtc,
    pnpCommit: commit,
    environment: environment ?? {
      runner: 'local CLI',
      os: `${os.type()} ${os.release()}`,
      platform: process.platform,
      arch: process.arch,
      node: process.version,
      npm: 'unknown',
      scope: 'local historical assertion-checker replay; PNP Labs upload is frozen',
    },
    commandsRun: commandsRun ?? [
      'npm run verify',
      'npm run pnp:verify',
    ],
    verdict: {
      tag: field0(status, verdictObject, 'tag', 'accept'),
      claimStatus: field0(status, verdictObject, 'claimStatus', 'historical-assertion-checker-replay'),
      publicTheoremEmissionAllowed: field0(status, verdictObject, 'publicTheoremEmissionAllowed', false),
      publicTheoremStatement: field0(status, verdictObject, 'publicTheoremStatement', null),
      publicTheoremConclusion: field0(status, verdictObject, 'publicTheoremConclusion', null),
      finalTheoremReady: field0(status, verdictObject, 'finalTheoremReady', false),
      unrestrictedFinalSoundnessDischarged: field0(status, verdictObject, 'unrestrictedFinalSoundnessDischarged', false),
      remainingBlockers: activatedRemainingBlockers,
    },
    statusSnapshot: {
      kind: field0(status, {}, 'kind', null),
      coordinate: field0(status, {}, 'coordinate', null),
      historicalPublicTheoremActivationCoordinate: field0(status, {}, 'publicTheoremActivationCoordinate', null),
      historicalUnrestrictedFinalSoundnessReleaseCoordinate: field0(status, {}, 'unrestrictedFinalSoundnessReleaseCoordinate', null),
      externalReviewIsMathematicalPremise: field0(status, {}, 'externalReviewIsMathematicalPremise', false),
    },
    statusPayloadSha256: statusSha,
    proofScriptOutputs: proofScriptOutputs ?? BuildProofScriptOutputs0({ pnpCommit: commit }),
    artifactsOrLogs: artifactsOrLogs ?? [
      { kind: 'local-file', path: LATEST_VERDICT0, label: 'one-command verifier verdict' },
      { kind: 'local-file', path: STATUS_PAYLOAD0, sha256: statusSha, label: 'status payload snapshot' },
    ],
    nonClaims: [
      'This report records a local historical assertion-checker replay.',
      'PNP Labs upload is frozen while formal reconstruction is in progress.',
      'It is not an external-consensus claim or peer-review acceptance.',
      'External review remains audit and reproducibility evidence, not a mathematical premise for theorem emission.',
    ],
  };
}

export function BuildPNPLabsIssueTitle0(record) {
  return `PNP historical checker replay: ${record.runnerNameOrHandle} ${record.dateUtc}`;
}

export function BuildPNPLabsIssueBody0(record, { verdictText = '', statusPayloadText = '' } = {}) {
  const statusText = statusPayloadText ? `\n### Status payload snapshot\n\n\`\`\`json\n${statusPayloadText.slice(0, 6000)}\n\`\`\`\n` : '';
  const verdictBlock = verdictText ? `\n### Verifier verdict excerpt\n\n\`\`\`json\n${verdictText.slice(0, 6000)}\n\`\`\`\n` : '';
  return `## PNP historical checker replay\n\nThis local-only record was generated by the retired \`npm run verify\` surface in \`aisknab/pnp\`. PNP Labs upload is frozen during formal reconstruction.\n\n### Required summary\n\n\`\`\`text\nrecordId = ${record.recordId}\nrecordClass = ${record.recordClass}\npnpCommit = ${record.pnpCommit}\npublicTheoremEmissionAllowed = ${record.verdict.publicTheoremEmissionAllowed}\npublicTheoremStatement = ${record.verdict.publicTheoremStatement}\npublicTheoremConclusion = ${record.verdict.publicTheoremConclusion}\nfinalTheoremReady = ${record.verdict.finalTheoremReady}\nunrestrictedFinalSoundnessDischarged = ${record.verdict.unrestrictedFinalSoundnessDischarged}\nremainingBlockers = ${JSON.stringify(record.verdict.remainingBlockers)}\nstatusCoordinate = ${record.statusSnapshot.coordinate}\nhistoricalPublicTheoremActivationCoordinate = ${record.statusSnapshot.historicalPublicTheoremActivationCoordinate}\nstatusPayloadSha256 = ${record.statusPayloadSha256}\n\`\`\`\n\n### Commands run\n\n\`\`\`bash\n${record.commandsRun.join('\n')}\n\`\`\`\n\n### Environment\n\n\`\`\`json\n${JSON.stringify(record.environment, null, 2)}\n\`\`\`\n\n### Importable local replay record\n\n\`\`\`json\n${JSON.stringify(record, null, 2)}\n\`\`\`${statusText}${verdictBlock}\n### Attestation\n\n- I ran the historical assertion-checker replay shown above.\n- I understand this record is not current theorem-status authority, an external-consensus claim, or peer-review acceptance.\n- I understand external review is audit evidence and not a mathematical premise for theorem emission.\n`;
}

export function BuildPNPLabsIssueUrl0(title) {
  const params = new URLSearchParams({
    template: 'pnp-verification-run.yml',
    title,
  });
  return `https://github.com/${PNPLABS_REPO0}/issues/new?${params.toString()}`;
}

export async function UploadPNPLabsIssue0({
  historicalReplay = false,
} = {}) {
  if (historicalReplay !== true) return LegacyReplayRequiredReject0('UploadPNPLabsIssue0');
  return {
    tag: 'reject',
    kind: 'reject',
    checker: 'UploadPNPLabsIssue0',
    coord: 'PNPLabsUpload.FrozenDuringFormalReconstruction',
    path: ['upload'],
    witness: {
      reason: 'external PNP Labs issue creation is frozen while formal reconstruction is in progress',
      currentStatus: 'status/FORMAL_RECONSTRUCTION_STATUS.json',
    },
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    publicTheoremConclusion: null,
    finalTheoremReady: false,
  };
}

export async function WritePNPLabsUploadFiles0({
  record,
  issueBody,
  outputDir = UPLOAD_DIR0,
  historicalReplay = false,
} = {}) {
  if (historicalReplay !== true) return LegacyReplayRequiredReject0('WritePNPLabsUploadFiles0');
  await mkdir(outputDir, { recursive: true });
  const recordPath = path.join(outputDir, 'latest-run-record.json');
  const issuePath = path.join(outputDir, 'latest-issue-body.md');
  await writeFile(recordPath, `${JSON.stringify(record, null, 2)}\n`, 'utf8');
  await writeFile(issuePath, `${issueBody}\n`, 'utf8');
  return { recordPath, issuePath };
}

async function main0() {
  EnforceHistoricalReplayCli0({ entrypoint: 'scripts/pnp-verify-and-upload.mjs' });
  const args = process.argv.slice(2);
  const skipVerify = args.includes('--skip-verify');
  const forceUpload = args.includes('--upload') || args.includes('--yes');
  const json = args.includes('--json');

  if (!skipVerify) {
    console.log('Running npm run pnp:verify ...');
    await runCommand0(npmCommand0(), ['run', 'pnp:verify'], { stdio: 'inherit' });
  }

  const bundle = await BuildCurrentRunBundle0({ historicalReplay: true });
  const paths = await WritePNPLabsUploadFiles0({ ...bundle, historicalReplay: true });
  console.log('Verify complete.');
  console.log(`Run record written to ${paths.recordPath}`);
  console.log(`PNP Labs issue body written to ${paths.issuePath}`);

  if (forceUpload) {
    const uploadResult = await UploadPNPLabsIssue0({ historicalReplay: true });
    console.error('PNP Labs upload is frozen while formal reconstruction is in progress.');
    if (json) console.error(JSON.stringify({ ...uploadResult, uploaded: false, ...paths }, null, 2));
    process.exitCode = 1;
    return;
  }

  console.log('Local historical replay complete. PNP Labs upload is frozen during formal reconstruction.');
  if (json) console.log(JSON.stringify({ tag: 'accept', historicalReplay: true, uploaded: false, uploadFrozen: true, ...paths }, null, 2));
}

export async function BuildCurrentRunBundle0(options = {}) {
  if (options.historicalReplay !== true) return LegacyReplayRequiredReject0('BuildCurrentRunBundle0');
  const verdictText = await readOptionalText0(LATEST_VERDICT0, '{}');
  const verdict = JSON.parse(verdictText);
  const statusPayloadPath = existsSync(STATUS_PAYLOAD0) ? STATUS_PAYLOAD0 : ACTIVATED_STATUS_PAYLOAD0;
  const statusPayloadText = await readOptionalText0(statusPayloadPath, '{}');
  const statusPayload = JSON.parse(statusPayloadText);
  const pnpCommit = runText0('git', ['rev-parse', 'HEAD']) || 'unknown';
  const npmVersion = runText0(npmCommand0(), ['--version']) || 'unknown';
  const runnerNameOrHandle = process.env.PNP_RUNNER_HANDLE || runText0('git', ['config', 'user.name']) || os.userInfo().username || 'local verifier runner';
  const environment = {
    runner: 'local CLI',
    os: `${os.type()} ${os.release()}`,
    platform: process.platform,
    arch: process.arch,
    node: process.version,
    npm: npmVersion,
    scope: 'local historical assertion-checker replay; PNP Labs upload is frozen',
  };
  const record = BuildPNPLabsRunRecord0({
    verdict,
    statusPayload,
    statusPayloadText,
    pnpCommit,
    runnerNameOrHandle,
    environment,
    commandsRun: ['npm run verify -- --historical-replay --no-upload', 'npm run pnp:verify'],
    historicalReplay: true,
  });
  const title = BuildPNPLabsIssueTitle0(record);
  const issueBody = BuildPNPLabsIssueBody0({ ...record, artifactsOrLogs: [...record.artifactsOrLogs, { kind: 'local-file', path: statusPayloadPath, label: 'status payload source' }] }, { verdictText, statusPayloadText });
  return { record, title, issueBody };
}

async function runCommand0(command, args, options = {}) {
  await new Promise((resolve, reject) => {
    const child = spawn(command, args, options);
    child.on('error', reject);
    child.on('exit', (code) => code === 0 ? resolve() : reject(new Error(`${command} ${args.join(' ')} failed with exit code ${code}`)));
  });
}

function runText0(command, args) {
  const out = spawnSync(command, args, { encoding: 'utf8' });
  if (out.status !== 0) return '';
  return String(out.stdout ?? '').trim();
}

async function readOptionalText0(filePath, fallback) {
  try { return await readFile(filePath, 'utf8'); }
  catch { return fallback; }
}

function field0(primary, secondary, key, fallback) {
  if (Object.prototype.hasOwnProperty.call(primary, key)) return primary[key];
  if (Object.prototype.hasOwnProperty.call(secondary, key)) return secondary[key];
  return fallback;
}

function npmCommand0() {
  return process.platform === 'win32' ? 'npm.cmd' : 'npm';
}

if (import.meta.url === `file://${process.argv[1]}` || fileURLToPath(import.meta.url) === process.argv[1]) {
  main0().catch((error) => {
    console.error(error?.stack ?? error?.message ?? String(error));
    process.exit(1);
  });
}
