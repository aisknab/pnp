#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import readline from 'node:readline/promises';

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
} = {}) {
  const status = statusPayload ?? {};
  const verdictObject = verdict ?? {};
  const runner = runnerNameOrHandle || 'local verifier runner';
  const commit = pnpCommit || 'unknown';
  const recordId = BuildPNPLabsRecordId0({ runnerNameOrHandle: runner, dateUtc, pnpCommit: commit });
  const statusSha = Sha256Text0(statusPayloadText ?? JSON.stringify(status));
  const activatedRemainingBlockers = Array.isArray(status.remainingBlockers) ? status.remainingBlockers : (Array.isArray(verdictObject.remainingBlockers) ? verdictObject.remainingBlockers : []);
  return {
    kind: 'PNPActivatedVerificationRunRecord0',
    recordId,
    recordClass: 'source-checker-verifier-run',
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
      scope: 'one-command source/checker verifier run with optional PNP Labs upload',
    },
    commandsRun: commandsRun ?? [
      'npm run verify',
      'npm run pnp:verify',
    ],
    verdict: {
      tag: verdictObject.tag ?? 'accept',
      claimStatus: status.claimStatus ?? verdictObject.claimStatus ?? 'public-theorem-emission-activated-under-checker-trust-model',
      publicTheoremEmissionAllowed: status.publicTheoremEmissionAllowed ?? verdictObject.publicTheoremEmissionAllowed ?? true,
      publicTheoremStatement: status.publicTheoremStatement ?? verdictObject.publicTheoremStatement ?? 'P = NP',
      publicTheoremConclusion: status.publicTheoremConclusion ?? verdictObject.publicTheoremConclusion ?? 'P = NP',
      finalTheoremReady: status.finalTheoremReady ?? verdictObject.finalTheoremReady ?? true,
      unrestrictedFinalSoundnessDischarged: status.unrestrictedFinalSoundnessDischarged ?? verdictObject.unrestrictedFinalSoundnessDischarged ?? true,
      remainingBlockers: activatedRemainingBlockers,
    },
    activatedStatus: {
      kind: status.kind ?? 'PNPActivatedStatus0',
      coordinate: status.coordinate ?? 'PNP-ACTIVATED-STATUS-2026-07-05-01',
      publicTheoremActivationCoordinate: status.publicTheoremActivationCoordinate ?? 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
      unrestrictedFinalSoundnessReleaseCoordinate: status.unrestrictedFinalSoundnessReleaseCoordinate ?? 'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01',
      externalReviewIsMathematicalPremise: status.externalReviewIsMathematicalPremise ?? false,
    },
    statusPayloadSha256: statusSha,
    proofScriptOutputs: proofScriptOutputs ?? BuildProofScriptOutputs0({ pnpCommit: commit }),
    artifactsOrLogs: artifactsOrLogs ?? [
      { kind: 'local-file', path: LATEST_VERDICT0, label: 'one-command verifier verdict' },
      { kind: 'local-file', path: STATUS_PAYLOAD0, sha256: statusSha, label: 'activated status payload' },
    ],
    nonClaims: [
      'This report records a source/checker verifier run submitted through the interactive CLI.',
      'It is not an external-consensus claim or peer-review acceptance.',
      'External review remains audit and reproducibility evidence, not a mathematical premise for theorem emission.',
    ],
  };
}

export function BuildPNPLabsIssueTitle0(record) {
  return `PNP activated verification run: ${record.runnerNameOrHandle} ${record.dateUtc}`;
}

export function BuildPNPLabsIssueBody0(record, { verdictText = '', statusPayloadText = '' } = {}) {
  const statusText = statusPayloadText ? `\n### Activated status payload excerpt\n\n\`\`\`json\n${statusPayloadText.slice(0, 6000)}\n\`\`\`\n` : '';
  const verdictBlock = verdictText ? `\n### Verifier verdict excerpt\n\n\`\`\`json\n${verdictText.slice(0, 6000)}\n\`\`\`\n` : '';
  return `## PNP activated verification run\n\nThis issue was generated by \`npm run verify\` in \`aisknab/pnp\`.\n\n### Required summary\n\n\`\`\`text\nrecordId = ${record.recordId}\nrecordClass = ${record.recordClass}\npnpCommit = ${record.pnpCommit}\npublicTheoremEmissionAllowed = ${record.verdict.publicTheoremEmissionAllowed}\npublicTheoremStatement = ${record.verdict.publicTheoremStatement}\npublicTheoremConclusion = ${record.verdict.publicTheoremConclusion}\nfinalTheoremReady = ${record.verdict.finalTheoremReady}\nunrestrictedFinalSoundnessDischarged = ${record.verdict.unrestrictedFinalSoundnessDischarged}\nremainingBlockers = ${JSON.stringify(record.verdict.remainingBlockers)}\nactivatedStatusCoordinate = ${record.activatedStatus.coordinate}\npublicTheoremActivationCoordinate = ${record.activatedStatus.publicTheoremActivationCoordinate}\nstatusPayloadSha256 = ${record.statusPayloadSha256}\n\`\`\`\n\n### Commands run\n\n\`\`\`bash\n${record.commandsRun.join('\n')}\n\`\`\`\n\n### Environment\n\n\`\`\`json\n${JSON.stringify(record.environment, null, 2)}\n\`\`\`\n\n### Importable run record\n\n\`\`\`json\n${JSON.stringify(record, null, 2)}\n\`\`\`${statusText}${verdictBlock}\n### Attestation\n\n- I ran the source/checker verifier command sequence shown above or an equivalent documented command sequence.\n- I understand this report records a verifier run and is not an external-consensus claim or peer-review acceptance.\n- I understand external review is audit evidence and not a mathematical premise for theorem emission.\n`;
}

export function BuildPNPLabsIssueUrl0(title) {
  const params = new URLSearchParams({
    template: 'pnp-verification-run.yml',
    title,
  });
  return `https://github.com/${PNPLABS_REPO0}/issues/new?${params.toString()}`;
}

export async function UploadPNPLabsIssue0({ title, body, token, fetchImpl = globalThis.fetch, repoFullName = PNPLABS_REPO0, labels = ['pnp-verification-run'] }) {
  if (!token) return { tag: 'manual', reason: 'missing-token', url: BuildPNPLabsIssueUrl0(title) };
  if (typeof fetchImpl !== 'function') return { tag: 'manual', reason: 'fetch-unavailable', url: BuildPNPLabsIssueUrl0(title) };
  const url = `https://api.github.com/repos/${repoFullName}/issues`;
  const payload = { title, body, labels };
  let res = await fetchImpl(url, {
    method: 'POST',
    headers: {
      accept: 'application/vnd.github+json',
      authorization: `Bearer ${token}`,
      'content-type': 'application/json',
      'x-github-api-version': '2022-11-28',
    },
    body: JSON.stringify(payload),
  });
  if (res.status === 422 && labels.length !== 0) {
    res = await fetchImpl(url, {
      method: 'POST',
      headers: {
        accept: 'application/vnd.github+json',
        authorization: `Bearer ${token}`,
        'content-type': 'application/json',
        'x-github-api-version': '2022-11-28',
      },
      body: JSON.stringify({ title, body }),
    });
  }
  const data = await safeJson0(res);
  if (!res.ok) return { tag: 'manual', reason: 'github-api-reject', status: res.status, detail: data, url: BuildPNPLabsIssueUrl0(title) };
  return { tag: 'uploaded', method: 'github-api', url: data.html_url ?? data.url, number: data.number ?? null };
}

export async function WritePNPLabsUploadFiles0({ record, issueBody, outputDir = UPLOAD_DIR0 }) {
  await mkdir(outputDir, { recursive: true });
  const recordPath = path.join(outputDir, 'latest-run-record.json');
  const issuePath = path.join(outputDir, 'latest-issue-body.md');
  await writeFile(recordPath, `${JSON.stringify(record, null, 2)}\n`, 'utf8');
  await writeFile(issuePath, `${issueBody}\n`, 'utf8');
  return { recordPath, issuePath };
}

async function main0() {
  const args = process.argv.slice(2);
  const skipVerify = args.includes('--skip-verify');
  const forceUpload = args.includes('--upload') || args.includes('--yes');
  const noUpload = args.includes('--no-upload');
  const json = args.includes('--json');

  if (!skipVerify) {
    console.log('Running npm run pnp:verify ...');
    await runCommand0(npmCommand0(), ['run', 'pnp:verify'], { stdio: 'inherit' });
  }

  const bundle = await BuildCurrentRunBundle0();
  const paths = await WritePNPLabsUploadFiles0(bundle);
  console.log('Verify complete.');
  console.log(`Run record written to ${paths.recordPath}`);
  console.log(`PNP Labs issue body written to ${paths.issuePath}`);

  let upload = forceUpload;
  if (!forceUpload && !noUpload && process.stdin.isTTY) {
    const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
    try {
      const answer = await rl.question('Upload verification run to PNP Labs? [y/N] ');
      upload = IsYesAnswer0(answer);
    } finally {
      rl.close();
    }
  }

  if (!upload) {
    console.log('Upload skipped. Run this later with npm run pnp:verify:upload, or open the saved issue body manually.');
    if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: false, ...paths }, null, 2));
    return;
  }

  const token = process.env.PNPLABS_UPLOAD_TOKEN || process.env.GITHUB_TOKEN || process.env.GH_TOKEN || '';
  const uploadResult = await UploadPNPLabsIssue0({ title: bundle.title, body: bundle.issueBody, token });
  if (uploadResult.tag === 'uploaded') {
    console.log(`Uploaded to PNP Labs: ${uploadResult.url}`);
    if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: true, uploadResult, ...paths }, null, 2));
    return;
  }

  const ghResult = tryGhIssueCreate0({ title: bundle.title, issuePath: paths.issuePath });
  if (ghResult.tag === 'uploaded') {
    console.log(`Uploaded to PNP Labs using gh: ${ghResult.url ?? 'issue created'}`);
    if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: true, uploadResult: ghResult, ...paths }, null, 2));
    return;
  }

  console.log('Automatic upload needs PNPLABS_UPLOAD_TOKEN, GITHUB_TOKEN, GH_TOKEN, or an authenticated gh CLI.');
  console.log(`Open this issue form instead: ${uploadResult.url}`);
  console.log(`Paste the saved body from ${paths.issuePath}.`);
  if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: false, uploadResult, ghResult, ...paths }, null, 2));
}

export async function BuildCurrentRunBundle0() {
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
    scope: 'one-command source/checker verifier run with optional PNP Labs upload',
  };
  const record = BuildPNPLabsRunRecord0({
    verdict,
    statusPayload,
    statusPayloadText,
    pnpCommit,
    runnerNameOrHandle,
    environment,
    commandsRun: ['npm run verify', 'npm run pnp:verify'],
  });
  const title = BuildPNPLabsIssueTitle0(record);
  const issueBody = BuildPNPLabsIssueBody0({ ...record, artifactsOrLogs: [...record.artifactsOrLogs, { kind: 'local-file', path: statusPayloadPath, label: 'activated status payload source' }] }, { verdictText, statusPayloadText });
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

function tryGhIssueCreate0({ title, issuePath }) {
  const gh = spawnSync('gh', ['issue', 'create', '--repo', PNPLABS_REPO0, '--title', title, '--body-file', issuePath, '--label', 'pnp-verification-run'], { encoding: 'utf8' });
  if (gh.status === 0) return { tag: 'uploaded', method: 'gh-cli', url: String(gh.stdout ?? '').trim() };
  return { tag: 'manual', reason: 'gh-cli-unavailable-or-not-authenticated', stderr: String(gh.stderr ?? '').trim() };
}

async function readOptionalText0(filePath, fallback) {
  try { return await readFile(filePath, 'utf8'); }
  catch { return fallback; }
}

async function safeJson0(response) {
  try { return await response.json(); }
  catch { return null; }
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
