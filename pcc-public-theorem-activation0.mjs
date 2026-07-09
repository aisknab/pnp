#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckFormalReconstructionStatus0, EvaluateFormalReleaseGateExample0 } from './pcc-formal-reconstruction-status0.mjs';

const CHECKER = 'CheckPublicTheoremActivation0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-ACTIVATION-WITHDRAWAL-2026-07-09-01';
const HISTORICAL_COORD = 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01';
const STATUS_COORD = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01';
const MANIFEST_PATH = 'proof-obligations/PUBLIC_THEOREM_ACTIVATION.json';
const OUT = 'artifacts/public-theorem-activation/latest-verdict.json';

const REQUIRED_OBLIGATIONS = Object.freeze([
  'PTW-001-CurrentEmissionDisabled',
  'PTW-002-LegacyActivationSuperseded',
  'PTW-003-FormalGateRequired',
  'PTW-004-AssertionRecordsNonAuthoritative',
  'PTW-005-NoHumanPremise',
]);

export async function CheckPublicTheoremActivation0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;

  try {
    const status = await CheckFormalReconstructionStatus0({
      root,
      writeOutput: false,
      statusOverride: options.statusOverride,
      siteOverride: options.siteOverride,
      legacyStatusOverride: options.legacyStatusOverride,
      withdrawalManifestOverride: options.manifestOverride,
    });
    if (status.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('PublicTheoremActivation.StatusDependency', ['dependsOn', STATUS_COORD], 'formal reconstruction status dependency must accept', { dependency: status }));

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'public theorem activation withdrawal manifest' });
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);

    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const examplesCheck = validateExamples0(manifestRead.value);
    if (examplesCheck.tag === 'reject') return write0(root, outputPath, writeOutput, examplesCheck);

    const evidence = await digestEvidence0({ root, paths: manifestRead.value.evidenceSurfaces });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-theorem-activation-withdrawal-accepted',
      publicTheoremActivationAccepted: false,
      publicTheoremActivationWithdrawn: true,
      publicTheoremEmissionAllowed: false,
      publicTheoremStatement: null,
      publicTheoremConclusion: null,
      publicTheoremUnderCheckerTrustModel: false,
      finalTheoremReady: false,
      internalFinalTheoremReady: false,
      formalReleaseGatePassed: false,
      externalReviewAcceptanceRequiredForEmission: false,
      externalReviewIsMathematicalPremise: false,
      humanReviewRequiredForMathematicalValidity: false,
      supersedesCoordinate: HISTORICAL_COORD,
      formalStatusCoordinate: STATUS_COORD,
      remainingFormalObligations: status.remainingFormalObligations,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      formalStatusDigestSha256: sha256Text0(stableStringify0(status)),
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremActivation.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluatePublicTheoremActivationExample0(input) {
  const gate = EvaluateFormalReleaseGateExample0(input);
  if (gate.tag === 'reject') return gate;
  return {
    tag: 'accept',
    requirementsDeclaredComplete: gate.requirementsDeclaredComplete,
    formalReleaseGatePassed: false,
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    requiresLeanArtifactVerification: true,
    remainingFormalRequirements: [...gate.missing, ...gate.forbidden],
  };
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('PublicTheoremActivation.ManifestShape', [], 'withdrawal manifest must be an object');
  const exact = {
    kind: 'PNPPublicTheoremActivationWithdrawal0',
    version: VERSION,
    coordinate: COORD,
    status: 'public-theorem-activation-withdrawn',
    supersedesCoordinate: HISTORICAL_COORD,
    supersededByStatusCoordinate: STATUS_COORD,
    publicTheoremActivationAccepted: false,
    publicTheoremActivationWithdrawn: true,
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    publicTheoremConclusion: null,
    publicTheoremUnderCheckerTrustModel: false,
    finalTheoremReady: false,
    internalFinalTheoremReady: false,
    formalReleaseGatePassed: false,
    externalReviewAcceptanceRequiredForEmission: false,
    externalReviewIsMathematicalPremise: false,
    humanReviewRequiredForMathematicalValidity: false,
  };
  for (const [key, expected] of Object.entries(exact)) {
    if (manifest[key] !== expected) return reject0('PublicTheoremActivation.WithdrawalBoolean', [key], 'withdrawal field mismatch', { expected, actual: manifest[key] });
  }
  if (!sameArray0(manifest.dependsOn, [STATUS_COORD])) return reject0('PublicTheoremActivation.DependsOn', ['dependsOn'], 'withdrawal dependency mismatch', { actual: manifest.dependsOn });

  const policy = manifest.withdrawalPolicy;
  if (!plain0(policy)) return reject0('PublicTheoremActivation.PolicyShape', ['withdrawalPolicy'], 'withdrawal policy must be an object');
  const trueFields = ['requiresClosedLeanRootTheoremForFutureActivation', 'requiresConcreteMachineSemantics', 'requiresNoProjectSpecificAxioms', 'requiresNoSorryOrAdmit', 'requiresFormalPolynomialRuntimeProof'];
  for (const key of trueFields) if (policy[key] !== true) return reject0('PublicTheoremActivation.PolicyBoolean', ['withdrawalPolicy', key], 'withdrawal policy required field must be true', { actual: policy[key] });
  const falseFields = ['allowsJsonBooleanActivation', 'allowsJavaScriptCheckerAcceptanceAsTheoremEvidence', 'usesExternalReviewAsPremise', 'usesHistoricalReportProseAsPremise', 'usesPublicSiteWordingAsPremise', 'allowsPublicTheoremEmissionNow'];
  for (const key of falseFields) if (policy[key] !== false) return reject0('PublicTheoremActivation.PolicyBoolean', ['withdrawalPolicy', key], 'withdrawal policy forbidden field must be false', { actual: policy[key] });

  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((item) => item?.id), REQUIRED_OBLIGATIONS)) return reject0('PublicTheoremActivation.ProofObligations', ['proofObligations'], 'withdrawal proof obligations mismatch');
  for (const item of manifest.proofObligations) if (!plain0(item) || item.requiredForWithdrawal !== true || typeof item.statement !== 'string' || item.statement.length === 0) return reject0('PublicTheoremActivation.ProofObligationEntry', ['proofObligations'], 'withdrawal proof obligation entry incomplete');
  for (const key of ['evidenceSurfaces', 'nonClaims']) if (!Array.isArray(manifest[key]) || manifest[key].length === 0 || manifest[key].some((value) => typeof value !== 'string' || value.length === 0)) return reject0('PublicTheoremActivation.ArrayField', [key], 'field must be a non-empty string array');
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length === 0) return reject0('PublicTheoremActivation.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length === 0) return reject0('PublicTheoremActivation.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-public-theorem-activation0.mjs' || manifest.audit.test !== 'audits/public-theorem-activation0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('PublicTheoremActivation.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateExamples0(manifest) {
  for (let index = 0; index < manifest.positiveExamples.length; index += 1) {
    const example = manifest.positiveExamples[index];
    const out = EvaluatePublicTheoremActivationExample0(example.input);
    if (out.tag !== 'accept') return reject0('PublicTheoremActivation.PositiveExampleRejected', ['positiveExamples', index], 'positive example rejected', { exampleId: example.id, reject: out });
    for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('PublicTheoremActivation.PositiveExampleMismatch', ['positiveExamples', index, 'expected', key], 'positive example mismatch', { expected, actual: out[key] });
  }
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
    return reject0('PublicTheoremActivation.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const rel of paths) {
    try {
      const abs = path.join(root, rel);
      const st = await stat(abs);
      if (!st.isFile()) return reject0('PublicTheoremActivation.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(abs);
      evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length });
    } catch (error) {
      return reject0('PublicTheoremActivation.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error));
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
  return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, formalReleaseGatePassed: false };
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
    const verdict = reject0('PublicTheoremActivation.CliBadArgument', [], 'bad CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckPublicTheoremActivation0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
