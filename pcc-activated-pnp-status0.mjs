#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckPublicTheoremActivation0 } from './pcc-public-theorem-activation0.mjs';
import { LegacyReplayRequiredReject0 } from './pcc-legacy-replay-gate0.mjs';

const CHECKER = 'CheckActivatedPNPStatus0';
const VERSION = 0;
const COORD = 'PNP-ACTIVATED-STATUS-2026-07-05-01';
const ACTIVATION_COORD = 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01';
const RELEASE_COORD = 'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01';
const STATUS_PATH = 'status/ACTIVATED_PNP_STATUS.json';
const SITE_PATH = 'public/pnp-status.json';
const OUT = 'artifacts/activated-pnp-status/latest-verdict.json';
const ACTIVE_FINAL_NODE_IDS = [
  'UFS-001-InputFamilyUniformity',
  'UFS-002-LockedNANDConstructionUniformPolynomial',
  'UFS-003-ThresholdEquivalenceAllInputs',
  'UFS-004-ResidualBandMinimizerUniformPolynomial',
  'UFS-005-ZeroSlackContradictionUniform',
  'UFS-006-NoHiddenOracleSemanticCompleteness',
  'UFS-007-ComplexityConclusionUniform',
  'UFS-008-ReleaseTransitionFromProofOnly',
  'PUBLIC-THEOREM-ACTIVATION',
];
const ACCEPTED_STACK = [
  'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01',
  'PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01',
  'PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01',
  'PNP-UNIFORM-RESIDUAL-BAND-MINIMIZER-2026-07-05-01',
  'PNP-UNIFORM-ZEROSLACK-CLOSURE-2026-07-05-01',
  'PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01',
  'PNP-UNIFORM-COMPLEXITY-CONCLUSION-2026-07-05-01',
  RELEASE_COORD,
  ACTIVATION_COORD,
];

export async function CheckActivatedPNPStatus0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  if (options.historicalReplay !== true) {
    return write0(root, outputPath, writeOutput, LegacyReplayRequiredReject0(CHECKER, ['Formal.RootTheoremAndAxiomAudit']));
  }
  try {
    const sitePath = options.sitePath ?? (options.siteOverride === undefined ? STATUS_PATH : SITE_PATH);
    const activation = await CheckPublicTheoremActivation0({ root, writeOutput: false, historicalReplay: true });
    if (activation.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('ActivatedPNPStatus.ActivationDependency', ['dependsOn', ACTIVATION_COORD], 'public theorem activation dependency must accept', { dependency: activation }));
    const activationCheck = validateActivation0(activation);
    if (activationCheck.tag === 'reject') return write0(root, outputPath, writeOutput, activationCheck);

    const statusRead = await readJson0({ root, filePath: options.statusPath ?? STATUS_PATH, override: options.statusOverride, label: 'activated status payload' });
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const siteRead = await readJson0({ root, filePath: sitePath, override: options.siteOverride, label: 'historical mirror payload' });
    if (siteRead.tag === 'reject') return write0(root, outputPath, writeOutput, siteRead);

    const statusCheck = validateStatus0(statusRead.value, STATUS_PATH);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);
    const siteCheck = validateStatus0(siteRead.value, sitePath);
    if (siteCheck.tag === 'reject') return write0(root, outputPath, writeOutput, siteCheck);
    const mirrorCheck = validateMirror0(statusRead.value, siteRead.value);
    if (mirrorCheck.tag === 'reject') return write0(root, outputPath, writeOutput, mirrorCheck);
    const evidence = await digestEvidence0({ root, paths: [...new Set([STATUS_PATH, sitePath]), 'proof-obligations/PUBLIC_THEOREM_ACTIVATION.json', 'pcc-public-theorem-activation0.mjs'] });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'activated-pnp-status-payload-accepted',
      activatedPNPStatusAccepted: true,
      publicTheoremEmissionAllowed: true,
      publicTheoremStatement: 'P = NP',
      publicTheoremConclusion: 'P = NP',
      publicTheoremUnderCheckerTrustModel: true,
      finalTheoremReady: true,
      internalFinalTheoremReady: true,
      unrestrictedFinalSoundnessDischarged: true,
      uniformFinalSoundnessProved: true,
      remainingBlockers: [],
      externalReviewAcceptanceRequiredForEmission: false,
      externalReviewIsMathematicalPremise: false,
      historicalReportProseIsMathematicalPremise: false,
      publicSiteWordingIsMathematicalPremise: false,
      statusPayload: STATUS_PATH,
      siteStatusPayload: sitePath,
      activationCoordinate: ACTIVATION_COORD,
      activationDigestSha256: sha256Text0(stableStringify0(activation)),
      statusSha256: sha256Hex0(statusRead.bytes),
      siteStatusSha256: sha256Hex0(siteRead.bytes),
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('ActivatedPNPStatus.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

function validateActivation0(activation) {
  const checks = {
    publicTheoremActivationAccepted: true,
    publicTheoremEmissionAllowed: true,
    publicTheoremStatement: 'P = NP',
    publicTheoremConclusion: 'P = NP',
    publicTheoremUnderCheckerTrustModel: true,
    finalTheoremReady: true,
    internalFinalTheoremReady: true,
    unrestrictedFinalSoundnessDischarged: true,
    uniformFinalSoundnessProved: true,
    externalReviewAcceptanceRequiredForEmission: false,
    externalReviewIsMathematicalPremise: false,
  };
  for (const [key, expected] of Object.entries(checks)) if (activation[key] !== expected) return reject0('ActivatedPNPStatus.ActivationField', ['activation', key], 'activation field mismatch', { expected, actual: activation[key] });
  if (!sameArray0(activation.remainingBlockers, [])) return reject0('ActivatedPNPStatus.ActivationBlockers', ['activation', 'remainingBlockers'], 'activation must have no remaining blockers', { actual: activation.remainingBlockers });
  return { tag: 'accept' };
}

function validateStatus0(status, label) {
  if (!plain0(status)) return reject0('ActivatedPNPStatus.Shape', [label], 'status payload must be an object');
  const exact = {
    kind: 'PNPActivatedStatus0',
    version: VERSION,
    project: 'PNP',
    coordinate: COORD,
    status: 'public-theorem-emission-activated',
    claimStatus: 'public-theorem-emission-activated-under-checker-trust-model',
    publicTheoremActivationCoordinate: ACTIVATION_COORD,
    unrestrictedFinalSoundnessReleaseCoordinate: RELEASE_COORD,
    publicTheoremEmissionAllowed: true,
    publicTheoremStatement: 'P = NP',
    publicTheoremConclusion: 'P = NP',
    publicTheoremUnderCheckerTrustModel: true,
    finalTheoremReady: true,
    internalFinalTheoremReady: true,
    unrestrictedFinalSoundnessDischarged: true,
    uniformFinalSoundnessProved: true,
    satInPConclusionAccepted: true,
    pEqualsNPConclusionAccepted: true,
    externalReviewAcceptanceRequiredForEmission: false,
    externalReviewIsMathematicalPremise: false,
    historicalReportProseIsMathematicalPremise: false,
    publicSiteWordingIsMathematicalPremise: false,
    activatedStatusPayload: STATUS_PATH,
    siteStatusPayload: SITE_PATH,
    legacyPublicReviewStatusPayload: 'PNP_STATUS.json',
  };
  for (const [key, expected] of Object.entries(exact)) if (status[key] !== expected) return reject0('ActivatedPNPStatus.Field', [label, key], 'status field mismatch', { expected, actual: status[key] });
  if (!sameArray0(status.clearedBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'])) return reject0('ActivatedPNPStatus.ClearedBlockers', [label, 'clearedBlockers'], 'cleared blockers mismatch', { actual: status.clearedBlockers });
  if (!sameArray0(status.remainingBlockers, [])) return reject0('ActivatedPNPStatus.RemainingBlockers', [label, 'remainingBlockers'], 'remaining blockers must be empty', { actual: status.remainingBlockers });
  if (!sameArray0(status.activeFinalNodeIds, ACTIVE_FINAL_NODE_IDS)) return reject0('ActivatedPNPStatus.ActiveFinalNodes', [label, 'activeFinalNodeIds'], 'active final node ids mismatch', { actual: status.activeFinalNodeIds });
  if (!sameArray0(status.acceptedProofStack, ACCEPTED_STACK)) return reject0('ActivatedPNPStatus.AcceptedStack', [label, 'acceptedProofStack'], 'accepted proof stack mismatch', { actual: status.acceptedProofStack });
  const commands = new Set(status.verificationCommands ?? []);
  for (const command of ['npm run proof:public-theorem-activation', 'npm run proof:unrestricted-final-soundness-release', 'npm run proof:uniform-complexity-conclusion']) if (!commands.has(command)) return reject0('ActivatedPNPStatus.CommandMissing', [label, 'verificationCommands'], 'verification command missing', { command });
  if (!Array.isArray(status.nonClaims) || status.nonClaims.length < 3) return reject0('ActivatedPNPStatus.NonClaims', [label, 'nonClaims'], 'nonClaims must document limits');
  return { tag: 'accept' };
}

function validateMirror0(a, b) {
  const left = stableStringify0(a);
  const right = stableStringify0(b);
  if (left !== right) return reject0('ActivatedPNPStatus.SiteMirrorMismatch', [SITE_PATH], 'site status payload must mirror activated status payload', { activatedSha256: sha256Text0(left), siteSha256: sha256Text0(right) });
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, label }) {
  if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; }
  try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('ActivatedPNPStatus.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); }
}
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('ActivatedPNPStatus.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('ActivatedPNPStatus.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, remainingBlockers: ['status-activation-failed'] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true, historicalReplay: false }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else if (arg === '--historical-replay') out.historicalReplay = true; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('ActivatedPNPStatus.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckActivatedPNPStatus0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
