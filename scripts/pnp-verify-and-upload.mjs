#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import readline from 'node:readline/promises';

const PNPLABS_REPO0 = 'aisknab/pnplabs';
const UPLOAD_DIR0 = 'artifacts/pnplabs-upload';
const LATEST_VERDICT0 = 'artifacts/pnp-verify-all/latest-verdict.json';
const STATUS_PAYLOAD0 = 'public/pnp-status.json';
const FORMAL_STATUS_PAYLOAD0 = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const LEGACY_STATUS_PAYLOAD0 = 'status/ACTIVATED_PNP_STATUS.json';
const FOCUSED_PROOF_SCRIPT_KEYS0 = Object.freeze(['proof:formal-reconstruction-status', 'proof:public-theorem-withdrawal']);

export function IsYesAnswer0(answer) { return /^(y|yes)$/iu.test(String(answer ?? '').trim()); }
export function Sha256Text0(text) { return createHash('sha256').update(Buffer.from(String(text), 'utf8')).digest('hex'); }
export function Slug0(value) { const slug = String(value ?? 'anonymous').trim().toLowerCase().replace(/[^a-z0-9]+/gu, '-').replace(/^-+|-+$/gu, ''); return slug || 'anonymous'; }
export function BuildPNPLabsRecordId0({ runnerNameOrHandle, dateUtc, pnpCommit }) { const date = String(dateUtc ?? '').slice(0, 10) || 'unknown-date'; const shortSha = String(pnpCommit ?? 'unknown').slice(0, 12); return `${Slug0(runnerNameOrHandle)}-${date}-${shortSha}`; }
export function BuildProofScriptOutputs0({ pnpCommit, verdictPath = LATEST_VERDICT0 } = {}) { return Object.fromEntries(FOCUSED_PROOF_SCRIPT_KEYS0.map((key) => [key, `covered by npm run pnp:verify for ${pnpCommit ?? 'unknown commit'}; see ${verdictPath}`])); }

export function BuildPNPLabsRunRecord0({ verdict, statusPayload, statusPayloadText, pnpCommit, runnerNameOrHandle, dateUtc = new Date().toISOString().slice(0, 10), environment, commandsRun, proofScriptOutputs, artifactsOrLogs } = {}) {
  const status = statusPayload ?? {};
  const verdictObject = verdict ?? {};
  const runner = runnerNameOrHandle || 'local verifier runner';
  const commit = pnpCommit || 'unknown';
  const recordId = BuildPNPLabsRecordId0({ runnerNameOrHandle: runner, dateUtc, pnpCommit: commit });
  const statusSha = Sha256Text0(statusPayloadText ?? JSON.stringify(status));
  const remainingFormalObligations = Array.isArray(status.remainingFormalObligations) ? status.remainingFormalObligations : (Array.isArray(verdictObject.remainingFormalObligations) ? verdictObject.remainingFormalObligations : []);
  return {
    kind: 'PNPFormalReconstructionVerificationRunRecord0',
    recordId,
    recordClass: 'source-checker-formal-reconstruction-run',
    runnerNameOrHandle: runner,
    dateUtc,
    pnpCommit: commit,
    environment: environment ?? { runner: 'local CLI', os: `${os.type()} ${os.release()}`, platform: process.platform, arch: process.arch, node: process.version, npm: 'unknown', scope: 'one-command source/checker reconstruction-status run with optional PNP Labs upload' },
    commandsRun: commandsRun ?? ['npm run verify', 'npm run pnp:verify'],
    verdict: {
      tag: verdictObject.tag ?? 'accept',
      claimStatus: pickField0(status, verdictObject, 'claimStatus', 'target-theorem-not-formally-established'),
      targetTheorem: pickField0(status, verdictObject, 'targetTheorem', 'P = NP'),
      publicTheoremEmissionAllowed: pickField0(status, verdictObject, 'publicTheoremEmissionAllowed', false),
      publicTheoremStatement: pickField0(status, verdictObject, 'publicTheoremStatement', null),
      publicTheoremConclusion: pickField0(status, verdictObject, 'publicTheoremConclusion', null),
      finalTheoremReady: pickField0(status, verdictObject, 'finalTheoremReady', false),
      rootLeanTheoremPresent: pickField0(status, verdictObject, 'rootLeanTheoremPresent', false),
      formalReleaseGatePassed: pickField0(status, verdictObject, 'formalReleaseGatePassed', false),
      remainingFormalObligations,
    },
    formalStatus: {
      kind: status.kind ?? 'PNPFormalReconstructionStatus0',
      coordinate: status.coordinate ?? 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01',
      historicalActivationCoordinate: status.historicalActivationCoordinate ?? 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
      historicalActivationSuperseded: pickField0(status, {}, 'historicalActivationSuperseded', true),
      projectSpecificAxiomsRemaining: pickField0(status, {}, 'projectSpecificAxiomsRemaining', true),
      humanReviewRequiredForMathematicalValidity: pickField0(status, {}, 'humanReviewRequiredForMathematicalValidity', false),
    },
    statusPayloadSha256: statusSha,
    proofScriptOutputs: proofScriptOutputs ?? BuildProofScriptOutputs0({ pnpCommit: commit }),
    artifactsOrLogs: artifactsOrLogs ?? [
      { kind: 'local-file', path: LATEST_VERDICT0, label: 'one-command verifier verdict' },
      { kind: 'local-file', path: STATUS_PAYLOAD0, sha256: statusSha, label: 'formal reconstruction status payload' },
    ],
    nonClaims: [
      'This report records a source/checker and reconstruction-status verifier run.',
      'It does not establish P = NP and does not activate public theorem emission.',
      'Historical checker acceptance, hashes, replay records, and release gates are not theorem evidence.',
      'Human review is not a mathematical premise or formal-release requirement.',
    ],
  };
}

export function BuildPNPLabsIssueTitle0(record) { return `PNP formal reconstruction verification run: ${record.runnerNameOrHandle} ${record.dateUtc}`; }
export function BuildPNPLabsIssueBody0(record, { verdictText = '', statusPayloadText = '' } = {}) {
  const statusText = statusPayloadText ? `\n### Formal reconstruction status payload excerpt\n\n\`\`\`json\n${statusPayloadText.slice(0, 6000)}\n\`\`\`\n` : '';
  const verdictBlock = verdictText ? `\n### Verifier verdict excerpt\n\n\`\`\`json\n${verdictText.slice(0, 6000)}\n\`\`\`\n` : '';
  return `## PNP formal reconstruction verification run\n\nThis issue was generated by \`npm run verify\` in \`aisknab/pnp\`.\n\n### Required summary\n\n\`\`\`text\nrecordId = ${record.recordId}\nrecordClass = ${record.recordClass}\npnpCommit = ${record.pnpCommit}\ntargetTheorem = ${record.verdict.targetTheorem}\npublicTheoremEmissionAllowed = ${record.verdict.publicTheoremEmissionAllowed}\npublicTheoremStatement = ${record.verdict.publicTheoremStatement}\npublicTheoremConclusion = ${record.verdict.publicTheoremConclusion}\nfinalTheoremReady = ${record.verdict.finalTheoremReady}\nrootLeanTheoremPresent = ${record.verdict.rootLeanTheoremPresent}\nformalReleaseGatePassed = ${record.verdict.formalReleaseGatePassed}\nremainingFormalObligations = ${JSON.stringify(record.verdict.remainingFormalObligations)}\nformalStatusCoordinate = ${record.formalStatus.coordinate}\nhistoricalActivationSuperseded = ${record.formalStatus.historicalActivationSuperseded}\nstatusPayloadSha256 = ${record.statusPayloadSha256}\n\`\`\`\n\n### Commands run\n\n\`\`\`bash\n${record.commandsRun.join('\n')}\n\`\`\`\n\n### Environment\n\n\`\`\`json\n${JSON.stringify(record.environment, null, 2)}\n\`\`\`\n\n### Importable run record\n\n\`\`\`json\n${JSON.stringify(record, null, 2)}\n\`\`\`${statusText}${verdictBlock}\n### Attestation\n\n- I ran the source/checker verifier command sequence shown above or an equivalent documented command sequence.\n- I understand this report does not establish \`P = NP\` and does not activate public theorem emission.\n- I understand human review is not a mathematical premise or formal-release requirement.\n`;
}
export function BuildPNPLabsIssueUrl0(title) { const params = new URLSearchParams({ template: 'pnp-verification-run.yml', title }); return `https://github.com/${PNPLABS_REPO0}/issues/new?${params.toString()}`; }

export async function UploadPNPLabsIssue0({ title, body, token, fetchImpl = globalThis.fetch, repoFullName = PNPLABS_REPO0, labels = ['pnp-verification-run'] }) {
  if (!token) return { tag: 'manual', reason: 'missing-token', url: BuildPNPLabsIssueUrl0(title) };
  if (typeof fetchImpl !== 'function') return { tag: 'manual', reason: 'fetch-unavailable', url: BuildPNPLabsIssueUrl0(title) };
  const url = `https://api.github.com/repos/${repoFullName}/issues`;
  let response = await fetchImpl(url, { method: 'POST', headers: { accept: 'application/vnd.github+json', authorization: `Bearer ${token}`, 'content-type': 'application/json', 'x-github-api-version': '2022-11-28' }, body: JSON.stringify({ title, body, labels }) });
  if (response.status === 422 && labels.length !== 0) response = await fetchImpl(url, { method: 'POST', headers: { accept: 'application/vnd.github+json', authorization: `Bearer ${token}`, 'content-type': 'application/json', 'x-github-api-version': '2022-11-28' }, body: JSON.stringify({ title, body }) });
  const data = await safeJson0(response);
  if (!response.ok) return { tag: 'manual', reason: 'github-api-reject', status: response.status, detail: data, url: BuildPNPLabsIssueUrl0(title) };
  return { tag: 'uploaded', method: 'github-api', url: data.html_url ?? data.url, number: data.number ?? null };
}

export async function WritePNPLabsUploadFiles0({ record, issueBody, outputDir = UPLOAD_DIR0 }) { await mkdir(outputDir, { recursive: true }); const recordPath = path.join(outputDir, 'latest-run-record.json'); const issuePath = path.join(outputDir, 'latest-issue-body.md'); await writeFile(recordPath, `${JSON.stringify(record, null, 2)}\n`, 'utf8'); await writeFile(issuePath, `${issueBody}\n`, 'utf8'); return { recordPath, issuePath }; }

export async function BuildCurrentRunBundle0() {
  const verdictText = await readOptionalText0(LATEST_VERDICT0, '{}');
  const verdict = JSON.parse(verdictText);
  const statusPayloadPath = existsSync(STATUS_PAYLOAD0) ? STATUS_PAYLOAD0 : (existsSync(FORMAL_STATUS_PAYLOAD0) ? FORMAL_STATUS_PAYLOAD0 : LEGACY_STATUS_PAYLOAD0);
  const statusPayloadText = await readOptionalText0(statusPayloadPath, '{}');
  const statusPayload = JSON.parse(statusPayloadText);
  const pnpCommit = runText0('git', ['rev-parse', 'HEAD']) || 'unknown';
  const npmVersion = runText0(npmCommand0(), ['--version']) || 'unknown';
  const runnerNameOrHandle = process.env.PNP_RUNNER_HANDLE || runText0('git', ['config', 'user.name']) || os.userInfo().username || 'local verifier runner';
  const environment = { runner: 'local CLI', os: `${os.type()} ${os.release()}`, platform: process.platform, arch: process.arch, node: process.version, npm: npmVersion, scope: 'one-command source/checker reconstruction-status run with optional PNP Labs upload' };
  const record = BuildPNPLabsRunRecord0({ verdict, statusPayload, statusPayloadText, pnpCommit, runnerNameOrHandle, environment, commandsRun: ['npm run verify', 'npm run pnp:verify'] });
  const title = BuildPNPLabsIssueTitle0(record);
  const issueBody = BuildPNPLabsIssueBody0({ ...record, artifactsOrLogs: [...record.artifactsOrLogs, { kind: 'local-file', path: statusPayloadPath, label: 'formal reconstruction status payload source' }] }, { verdictText, statusPayloadText });
  return { record, title, issueBody };
}

async function main0() {
  const args = process.argv.slice(2);
  const skipVerify = args.includes('--skip-verify');
  const forceUpload = args.includes('--upload') || args.includes('--yes');
  const noUpload = args.includes('--no-upload');
  const json = args.includes('--json');
  if (!skipVerify) { console.log('Running npm run pnp:verify ...'); await runCommand0(npmCommand0(), ['run', 'pnp:verify'], { stdio: 'inherit' }); }
  const bundle = await BuildCurrentRunBundle0();
  const paths = await WritePNPLabsUploadFiles0(bundle);
  console.log('Verify complete.');
  console.log(`Run record written to ${paths.recordPath}`);
  console.log(`PNP Labs issue body written to ${paths.issuePath}`);
  let upload = forceUpload;
  if (!forceUpload && !noUpload && process.stdin.isTTY) { const rl = readline.createInterface({ input: process.stdin, output: process.stdout }); try { upload = IsYesAnswer0(await rl.question('Upload verification run to PNP Labs? [y/N] ')); } finally { rl.close(); } }
  if (!upload) { console.log('Upload skipped. Run this later with npm run pnp:verify:upload, or open the saved issue body manually.'); if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: false, ...paths }, null, 2)); return; }
  const token = process.env.PNPLABS_UPLOAD_TOKEN || process.env.GITHUB_TOKEN || process.env.GH_TOKEN || '';
  const uploadResult = await UploadPNPLabsIssue0({ title: bundle.title, body: bundle.issueBody, token });
  if (uploadResult.tag === 'uploaded') { console.log(`Uploaded to PNP Labs: ${uploadResult.url}`); if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: true, uploadResult, ...paths }, null, 2)); return; }
  const ghResult = tryGhIssueCreate0({ title: bundle.title, issuePath: paths.issuePath });
  if (ghResult.tag === 'uploaded') { console.log(`Uploaded to PNP Labs using gh: ${ghResult.url ?? 'issue created'}`); if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: true, uploadResult: ghResult, ...paths }, null, 2)); return; }
  console.log('Automatic upload needs PNPLABS_UPLOAD_TOKEN, GITHUB_TOKEN, GH_TOKEN, or an authenticated gh CLI.');
  console.log(`Open this issue form instead: ${uploadResult.url}`);
  console.log(`Paste the saved body from ${paths.issuePath}.`);
  if (json) console.log(JSON.stringify({ tag: 'accept', uploaded: false, uploadResult, ghResult, ...paths }, null, 2));
}

async function runCommand0(command, args, options = {}) { await new Promise((resolve, reject) => { const child = spawn(command, args, options); child.on('error', reject); child.on('exit', (code) => code === 0 ? resolve() : reject(new Error(`${command} ${args.join(' ')} failed with exit code ${code}`))); }); }
function runText0(command, args) { const out = spawnSync(command, args, { encoding: 'utf8' }); if (out.status !== 0) return ''; return String(out.stdout ?? '').trim(); }
function tryGhIssueCreate0({ title, issuePath }) { const gh = spawnSync('gh', ['issue', 'create', '--repo', PNPLABS_REPO0, '--title', title, '--body-file', issuePath, '--label', 'pnp-verification-run'], { encoding: 'utf8' }); if (gh.status === 0) return { tag: 'uploaded', method: 'gh-cli', url: String(gh.stdout ?? '').trim() }; return { tag: 'manual', reason: 'gh-cli-unavailable-or-not-authenticated', stderr: String(gh.stderr ?? '').trim() }; }
async function readOptionalText0(filePath, fallback) { try { return await readFile(filePath, 'utf8'); } catch { return fallback; } }
async function safeJson0(response) { try { return await response.json(); } catch { return null; } }
function pickField0(primary, secondary, key, fallback) { if (Object.prototype.hasOwnProperty.call(primary, key)) return primary[key]; if (Object.prototype.hasOwnProperty.call(secondary, key)) return secondary[key]; return fallback; }
function npmCommand0() { return process.platform === 'win32' ? 'npm.cmd' : 'npm'; }

if (import.meta.url === `file://${process.argv[1]}` || fileURLToPath(import.meta.url) === process.argv[1]) main0().catch((error) => { console.error(error?.stack ?? error?.message ?? String(error)); process.exit(1); });
