#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckFormalReconstructionStatus0';
const VERSION = 0;
const COORD = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01';
const HISTORICAL_ACTIVATION_COORD = 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const SITE_PATH = 'public/pnp-status.json';
const LEGACY_STATUS_PATH = 'status/ACTIVATED_PNP_STATUS.json';
const WITHDRAWAL_MANIFEST_PATH = 'proof-obligations/PUBLIC_THEOREM_ACTIVATION.json';
const OUT = 'artifacts/formal-reconstruction-status/latest-verdict.json';

const REQUIRED_OBLIGATIONS = Object.freeze([
  'Formal.ConcreteComplexityModel',
  'Formal.ConcreteSATAndNPHardness',
  'Formal.DirectWireSemantics',
  'Formal.LockedNANDThreshold',
  'Formal.ResidualBandMinimizerCorrectness',
  'Formal.ZeroSlackCompleteness',
  'Formal.PolynomialRuntimeAndEncodingBounds',
  'Formal.ClosedRootTheoremAndAxiomAudit',
]);

export async function CheckFormalReconstructionStatus0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;

  try {
    const statusRead = await readJson0({ root, filePath: options.statusPath ?? STATUS_PATH, override: options.statusOverride, label: 'formal reconstruction status' });
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);

    const siteRead = await readJson0({ root, filePath: options.sitePath ?? SITE_PATH, override: options.siteOverride, label: 'public status mirror' });
    if (siteRead.tag === 'reject') return write0(root, outputPath, writeOutput, siteRead);

    const legacyRead = await readJson0({ root, filePath: options.legacyStatusPath ?? LEGACY_STATUS_PATH, override: options.legacyStatusOverride, label: 'legacy activated status tombstone' });
    if (legacyRead.tag === 'reject') return write0(root, outputPath, writeOutput, legacyRead);

    const withdrawalRead = await readJson0({ root, filePath: options.withdrawalManifestPath ?? WITHDRAWAL_MANIFEST_PATH, override: options.withdrawalManifestOverride, label: 'public theorem activation withdrawal manifest' });
    if (withdrawalRead.tag === 'reject') return write0(root, outputPath, writeOutput, withdrawalRead);

    const statusCheck = validateStatus0(statusRead.value, STATUS_PATH);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const siteCheck = validateStatus0(siteRead.value, SITE_PATH);
    if (siteCheck.tag === 'reject') return write0(root, outputPath, writeOutput, siteCheck);

    const mirrorCheck = validateMirror0(statusRead.value, siteRead.value);
    if (mirrorCheck.tag === 'reject') return write0(root, outputPath, writeOutput, mirrorCheck);

    const legacyCheck = validateLegacyTombstone0(legacyRead.value);
    if (legacyCheck.tag === 'reject') return write0(root, outputPath, writeOutput, legacyCheck);

    const withdrawalCheck = validateWithdrawalManifest0(withdrawalRead.value);
    if (withdrawalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, withdrawalCheck);

    const evidence = await digestEvidence0({
      root,
      paths: [STATUS_PATH, SITE_PATH, LEGACY_STATUS_PATH, WITHDRAWAL_MANIFEST_PATH, 'FORMAL_RECONSTRUCTION.md'],
    });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'formal-reconstruction-status-accepted',
      formalReconstructionStatusAccepted: true,
      targetTheorem: 'P = NP',
      publicTheoremEmissionAllowed: false,
      publicTheoremStatement: null,
      publicTheoremConclusion: null,
      finalTheoremReady: false,
      rootLeanTheoremPresent: false,
      closedLeanTheoremPresent: false,
      formalReleaseGatePassed: false,
      projectSpecificAxiomsRemaining: true,
      legacyActivationSuperseded: true,
      humanReviewRequiredForMathematicalValidity: false,
      remainingFormalObligations: [...REQUIRED_OBLIGATIONS],
      statusPayload: STATUS_PATH,
      siteStatusPayload: SITE_PATH,
      legacyActivatedStatusPayload: LEGACY_STATUS_PATH,
      statusSha256: sha256Hex0(statusRead.bytes),
      siteStatusSha256: sha256Hex0(siteRead.bytes),
      legacyStatusSha256: sha256Hex0(legacyRead.bytes),
      withdrawalManifestSha256: sha256Hex0(withdrawalRead.bytes),
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('FormalReconstructionStatus.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluateFormalReleaseGateExample0(input) {
  if (!plain0(input)) return reject0('FormalReconstructionStatus.ExampleShape', ['input'], 'example input must be an object');
  const requiredTrue = [
    'closedLeanRootTheorem',
    'concreteMachineSemantics',
    'noProjectSpecificAxioms',
    'noSorryOrAdmit',
    'formalPolynomialRuntimeProof',
    'paperTheoremInventoryMatch',
    'generatedSiteStatus',
  ];
  const missing = requiredTrue.filter((key) => input[key] !== true);
  const forbidden = [
    'usesJsonBooleanActivation',
    'usesJavaScriptCheckerAcceptanceAsTheoremEvidence',
    'requiresHumanReview',
  ].filter((key) => input[key] !== false);
  const requirementsDeclaredComplete = missing.length === 0 && forbidden.length === 0;
  return {
    tag: 'accept',
    requirementsDeclaredComplete,
    formalReleaseGatePassed: false,
    publicTheoremEmissionAllowed: false,
    requiresLeanArtifactVerification: true,
    missing,
    forbidden,
  };
}

function validateStatus0(status, label) {
  if (!plain0(status)) return reject0('FormalReconstructionStatus.Shape', [label], 'status payload must be an object');
  const exact = {
    kind: 'PNPFormalReconstructionStatus0',
    version: VERSION,
    project: 'PNP',
    coordinate: COORD,
    status: 'formal-reconstruction-in-progress',
    claimStatus: 'target-theorem-not-formally-established',
    targetTheorem: 'P = NP',
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    publicTheoremConclusion: null,
    publicTheoremUnderCheckerTrustModel: false,
    finalTheoremReady: false,
    internalFinalTheoremReady: false,
    unrestrictedFinalSoundnessDischarged: false,
    uniformFinalSoundnessProved: false,
    satInPConclusionAccepted: false,
    pEqualsNPConclusionAccepted: false,
    rootLeanTheoremPresent: false,
    closedLeanTheoremPresent: false,
    formalReleaseGatePassed: false,
    projectSpecificAxiomsRemaining: true,
    legacyCheckerAcceptanceIsTheoremEvidence: false,
    humanReviewRequiredForMathematicalValidity: false,
    historicalActivationCoordinate: HISTORICAL_ACTIVATION_COORD,
    historicalActivationSuperseded: true,
    historicalReportRetained: true,
    currentStatusPayload: STATUS_PATH,
    siteStatusPayload: SITE_PATH,
    legacyActivatedStatusPayload: LEGACY_STATUS_PATH,
  };
  for (const [key, expected] of Object.entries(exact)) {
    if (status[key] !== expected) return reject0('FormalReconstructionStatus.Field', [label, key], 'status field mismatch', { expected, actual: status[key] });
  }
  if (!sameArray0(status.activeFinalNodeIds, [])) return reject0('FormalReconstructionStatus.ActiveFinalNodes', [label, 'activeFinalNodeIds'], 'active final node ids must be empty', { actual: status.activeFinalNodeIds });
  if (!sameArray0(status.clearedBlockers, [])) return reject0('FormalReconstructionStatus.ClearedBlockers', [label, 'clearedBlockers'], 'cleared blockers must be empty', { actual: status.clearedBlockers });
  if (!sameArray0(status.remainingFormalObligations, REQUIRED_OBLIGATIONS)) return reject0('FormalReconstructionStatus.Obligations', [label, 'remainingFormalObligations'], 'remaining formal obligations mismatch', { expected: REQUIRED_OBLIGATIONS, actual: status.remainingFormalObligations });
  const gate = status.releaseGate;
  if (!plain0(gate)) return reject0('FormalReconstructionStatus.ReleaseGateShape', [label, 'releaseGate'], 'release gate must be an object');
  const gateTrue = ['requiresClosedLeanRootTheorem', 'requiresConcreteMachineSemantics', 'requiresNoProjectSpecificAxioms', 'requiresNoSorryOrAdmit', 'requiresFormalPolynomialRuntimeProof', 'requiresPaperTheoremInventoryMatch', 'requiresGeneratedSiteStatus'];
  for (const key of gateTrue) if (gate[key] !== true) return reject0('FormalReconstructionStatus.ReleaseGateField', [label, 'releaseGate', key], 'release gate required field must be true', { actual: gate[key] });
  const gateFalse = ['allowsJsonBooleanActivation', 'allowsJavaScriptCheckerAcceptanceAsTheoremEvidence', 'requiresHumanReview', 'passed'];
  for (const key of gateFalse) if (gate[key] !== false) return reject0('FormalReconstructionStatus.ReleaseGateField', [label, 'releaseGate', key], 'release gate forbidden or incomplete field must be false', { actual: gate[key] });
  const commands = new Set(status.verificationCommands ?? []);
  for (const command of ['npm run proof:formal-reconstruction-status', 'lake build', 'npm run validate']) if (!commands.has(command)) return reject0('FormalReconstructionStatus.CommandMissing', [label, 'verificationCommands'], 'verification command missing', { command });
  if (!Array.isArray(status.nonClaims) || status.nonClaims.length < 4) return reject0('FormalReconstructionStatus.NonClaims', [label, 'nonClaims'], 'nonClaims must document the boundary');
  return { tag: 'accept' };
}

function validateLegacyTombstone0(status) {
  if (!plain0(status)) return reject0('FormalReconstructionStatus.LegacyShape', [LEGACY_STATUS_PATH], 'legacy status tombstone must be an object');
  const exact = {
    kind: 'PNPActivationSupersession0',
    version: VERSION,
    project: 'PNP',
    coordinate: 'PNP-ACTIVATED-STATUS-2026-07-05-01',
    status: 'superseded',
    claimStatus: 'historical-activation-withdrawn',
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    superseded: true,
    supersededByCoordinate: COORD,
    supersededByPath: STATUS_PATH,
    siteStatusPath: SITE_PATH,
    historicalRecordRetainedInGit: true,
  };
  for (const [key, expected] of Object.entries(exact)) if (status[key] !== expected) return reject0('FormalReconstructionStatus.LegacyField', [LEGACY_STATUS_PATH, key], 'legacy activation tombstone field mismatch', { expected, actual: status[key] });
  if (typeof status.reason !== 'string' || status.reason.length < 40) return reject0('FormalReconstructionStatus.LegacyReason', [LEGACY_STATUS_PATH, 'reason'], 'legacy activation tombstone must explain the withdrawal');
  return { tag: 'accept' };
}

function validateWithdrawalManifest0(manifest) {
  if (!plain0(manifest)) return reject0('FormalReconstructionStatus.WithdrawalShape', [WITHDRAWAL_MANIFEST_PATH], 'withdrawal manifest must be an object');
  const exact = {
    kind: 'PNPPublicTheoremActivationWithdrawal0',
    version: VERSION,
    coordinate: 'PNP-PUBLIC-THEOREM-ACTIVATION-WITHDRAWAL-2026-07-09-01',
    status: 'public-theorem-activation-withdrawn',
    publicTheoremActivationAccepted: false,
    publicTheoremActivationWithdrawn: true,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    formalReleaseGatePassed: false,
    supersedesCoordinate: HISTORICAL_ACTIVATION_COORD,
    supersededByStatusCoordinate: COORD,
  };
  for (const [key, expected] of Object.entries(exact)) if (manifest[key] !== expected) return reject0('FormalReconstructionStatus.WithdrawalField', [WITHDRAWAL_MANIFEST_PATH, key], 'withdrawal manifest field mismatch', { expected, actual: manifest[key] });
  return { tag: 'accept' };
}

function validateMirror0(a, b) {
  const left = stableStringify0(a);
  const right = stableStringify0(b);
  if (left !== right) return reject0('FormalReconstructionStatus.SiteMirrorMismatch', [SITE_PATH], 'site status payload must mirror formal reconstruction status payload', { statusSha256: sha256Text0(left), siteSha256: sha256Text0(right) });
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, label }) {
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, filePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('FormalReconstructionStatus.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const rel of paths) {
    try {
      const abs = path.join(root, rel);
      const st = await stat(abs);
      if (!st.isFile()) return reject0('FormalReconstructionStatus.EvidenceNotFile', ['evidence', rel], 'evidence path is not a file');
      const bytes = await readFile(abs);
      evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length });
    } catch (error) {
      return reject0('FormalReconstructionStatus.EvidenceMissing', ['evidence', rel], 'evidence file missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', evidence };
}

async function write0(root, outputPath, writeOutput, verdict) {
  const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null };
  if (writeOutput) {
    const target = path.join(root, outputPath);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
}

function reject0(coord, pathArray, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER,
    version: VERSION,
    coord,
    path: pathArray,
    witness: { reason, ...witness },
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    formalReleaseGatePassed: false,
  };
}

function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && a.length === b.length && a.every((value, index) => value === b[index]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('FormalReconstructionStatus.CliBadArgument', [], 'bad CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckFormalReconstructionStatus0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
