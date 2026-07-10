#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckUnrestrictedFinalSoundnessRelease0 } from './pcc-unrestricted-final-soundness-release0.mjs';
import { LegacyReplayRequiredReject0 } from './pcc-legacy-replay-gate0.mjs';

const CHECKER = 'CheckPublicTheoremActivation0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01';
const RELEASE_COORD = 'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01';
const MANIFEST_PATH = 'proof-obligations/PUBLIC_THEOREM_ACTIVATION.json';
const OUT = 'artifacts/public-theorem-activation/latest-verdict.json';
const BEFORE_BLOCKERS = ['ExternalReview.Acceptance'];
const REQUIRED_OBLIGATIONS = [
  'PTA-001-UnrestrictedReleaseAccepted',
  'PTA-002-InternalFinalTheoremReady',
  'PTA-003-ExternalReviewNotPremise',
  'PTA-004-HistoricalProseNotPremise',
  'PTA-005-TheoremStatementBound',
  'PTA-006-RemainingBlockersEmpty',
];

export async function CheckPublicTheoremActivation0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  if (options.historicalReplay !== true) {
    return write0(root, outputPath, writeOutput, LegacyReplayRequiredReject0(CHECKER, BEFORE_BLOCKERS));
  }
  try {
    const release = await CheckUnrestrictedFinalSoundnessRelease0({ root, writeOutput: false, historicalReplay: true });
    if (release.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('PublicTheoremActivation.ReleaseDependency', ['dependsOn', RELEASE_COORD], 'unrestricted final soundness release must accept', { dependency: release }));
    const releaseCheck = validateReleaseDependency0(release);
    if (releaseCheck.tag === 'reject') return write0(root, outputPath, writeOutput, releaseCheck);

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'public theorem activation manifest' });
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);
    const exampleCheck = validateExamples0(manifestRead.value);
    if (exampleCheck.tag === 'reject') return write0(root, outputPath, writeOutput, exampleCheck);
    const evidence = await digestEvidence0({ root, paths: manifestRead.value.evidenceSurfaces });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    const dependencyDigest = sha256Text0(stableStringify0(release));
    return write0(root, outputPath, writeOutput, {
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD,
      claimStatus: 'public-theorem-emission-activated-under-checker-trust-model',
      publicTheoremActivationAccepted: true,
      publicTheoremEmissionAllowed: true,
      publicTheoremStatement: 'P = NP',
      publicTheoremAntecedent: 'accepted UFS-001 through UFS-008 proof stack in the current checkout',
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
      clearedBlockers: ['ExternalReview.Acceptance'],
      remainingBlockers: [],
      activeFinalNodeIds: manifestRead.value.claimBoundaryAfterActivation.activeFinalNodeIds,
      dependency: { coordinate: RELEASE_COORD, sha256: dependencyDigest },
      proofObligationCount: REQUIRED_OBLIGATIONS.length,
      positiveExampleCount: manifestRead.value.positiveExamples.length,
      negativeExampleCount: manifestRead.value.negativeExamples.length,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremActivation.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluatePublicTheoremActivationExample0(input, options = {}) {
  if (options.historicalReplay !== true) return LegacyReplayRequiredReject0('EvaluatePublicTheoremActivationExample0', BEFORE_BLOCKERS);
  if (!plain0(input)) return reject0('PublicTheoremActivation.ExampleShape', ['input'], 'example input must be an object');
  const trueFields = ['unrestrictedFinalSoundnessDischarged', 'internalFinalTheoremReady', 'pEqualsNPConclusionAccepted'];
  const falseFields = ['usesExternalReviewAsPremise', 'usesHistoricalReportProseAsPremise'];
  for (const key of trueFields) if (input[key] !== true) return reject0('PublicTheoremActivation.ExamplePremise', ['input', key], 'activation example true premise mismatch', { expected: true, actual: input[key] });
  for (const key of falseFields) if (input[key] !== false) return reject0('PublicTheoremActivation.ExamplePremise', ['input', key], 'activation example false premise mismatch', { expected: false, actual: input[key] });
  return { tag: 'accept', publicTheoremEmissionAllowed: true, publicTheoremStatement: 'P = NP', remainingBlockers: [] };
}

function validateReleaseDependency0(release) {
  const checks = {
    releaseUnrestrictedFinalSoundnessCleared: true,
    unrestrictedFinalSoundnessDischarged: true,
    uniformFinalSoundnessProved: true,
    internalFinalTheoremReady: true,
    satInPConclusionAccepted: true,
    pEqualsNPConclusionAccepted: true,
    publicTheoremEmissionAllowed: false,
  };
  for (const [key, expected] of Object.entries(checks)) if (release[key] !== expected) return reject0('PublicTheoremActivation.ReleaseField', ['dependency', key], 'release dependency field mismatch', { expected, actual: release[key] });
  if (!sameArray0(release.remainingBlockers, BEFORE_BLOCKERS)) return reject0('PublicTheoremActivation.ReleaseBlockers', ['dependency', 'remainingBlockers'], 'release dependency must leave only external review before activation', { actual: release.remainingBlockers });
  return { tag: 'accept' };
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('PublicTheoremActivation.ManifestShape', [], 'manifest must be an object');
  const exact = [['kind', 'PNPPublicTheoremActivation0'], ['version', VERSION], ['coordinate', COORD], ['status', 'public-theorem-activation-accepted'], ['publicTheoremStatement', 'P = NP'], ['publicTheoremConclusion', 'P = NP']];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('PublicTheoremActivation.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  if (!sameArray0(manifest.dependsOn, [RELEASE_COORD])) return reject0('PublicTheoremActivation.DependsOn', ['dependsOn'], 'dependency list mismatch', { expected: [RELEASE_COORD], actual: manifest.dependsOn });
  const before = validateBeforeBoundary0(manifest.claimBoundaryBefore); if (before.tag === 'reject') return before;
  const after = validateAfterBoundary0(manifest.claimBoundaryAfterActivation); if (after.tag === 'reject') return after;
  const bools = {
    publicTheoremActivationAccepted: true,
    publicTheoremEmissionAllowed: true,
    publicTheoremUnderCheckerTrustModel: true,
    externalReviewAcceptanceRequiredForEmission: false,
    externalReviewIsMathematicalPremise: false,
    historicalReportProseIsMathematicalPremise: false,
    publicSiteWordingIsMathematicalPremise: false,
    unrestrictedFinalSoundnessRequired: true,
    unrestrictedFinalSoundnessDischarged: true,
  };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('PublicTheoremActivation.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  const policy = manifest.activationPolicy;
  if (!plain0(policy)) return reject0('PublicTheoremActivation.PolicyShape', ['activationPolicy'], 'activation policy must be an object');
  const policyTrue = ['requiresUnrestrictedFinalSoundnessRelease', 'requiresInternalFinalTheoremReady', 'requiresPEqualsNPConclusionAccepted', 'requiresSATInPConclusionAccepted', 'clearsExternalReviewPublicationBlocker', 'externalReviewRemainsAuditLayer', 'allowsPublicTheoremEmission'];
  const policyFalse = ['requiresExternalReviewAcceptance', 'usesExternalReviewAsPremise', 'usesHistoricalReportProseAsPremise', 'usesPublicSiteWordingAsPremise'];
  for (const key of policyTrue) if (policy[key] !== true) return reject0('PublicTheoremActivation.PolicyBoolean', ['activationPolicy', key], 'activation policy true field mismatch', { expected: true, actual: policy[key] });
  for (const key of policyFalse) if (policy[key] !== false) return reject0('PublicTheoremActivation.PolicyBoolean', ['activationPolicy', key], 'activation policy false field mismatch', { expected: false, actual: policy[key] });
  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((x) => x?.id), REQUIRED_OBLIGATIONS)) return reject0('PublicTheoremActivation.ProofObligations', ['proofObligations'], 'proof obligations mismatch', { expected: REQUIRED_OBLIGATIONS, actual: manifest.proofObligations?.map?.((x) => x?.id) });
  for (const entry of manifest.proofObligations) if (!plain0(entry) || entry.requiredForActivation !== true || typeof entry.statement !== 'string' || entry.statement.length === 0) return reject0('PublicTheoremActivation.ProofObligationEntry', ['proofObligations'], 'proof obligation entry incomplete');
  if (!plain0(manifest.uniformityClaims)) return reject0('PublicTheoremActivation.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(manifest.uniformityClaims)) if (value !== true) return reject0('PublicTheoremActivation.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('PublicTheoremActivation.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('PublicTheoremActivation.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-public-theorem-activation0.mjs' || manifest.audit.test !== 'audits/public-theorem-activation0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('PublicTheoremActivation.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateBeforeBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('PublicTheoremActivation.BeforeBoundaryShape', ['claimBoundaryBefore'], 'before boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false || boundary.finalTheoremReady !== true || boundary.internalFinalTheoremReady !== true || !sameArray0(boundary.remainingBlockers, BEFORE_BLOCKERS)) return reject0('PublicTheoremActivation.BeforeBoundary', ['claimBoundaryBefore'], 'before boundary mismatch', { actual: boundary });
  return { tag: 'accept' };
}

function validateAfterBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('PublicTheoremActivation.AfterBoundaryShape', ['claimBoundaryAfterActivation'], 'after boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== true || boundary.finalTheoremReady !== true || boundary.internalFinalTheoremReady !== true || !sameArray0(boundary.clearedBlockers, BEFORE_BLOCKERS) || !sameArray0(boundary.remainingBlockers, [])) return reject0('PublicTheoremActivation.AfterBoundary', ['claimBoundaryAfterActivation'], 'after boundary mismatch', { actual: boundary });
  if (!Array.isArray(boundary.activeFinalNodeIds) || boundary.activeFinalNodeIds.length !== 9) return reject0('PublicTheoremActivation.AfterBoundaryNodes', ['claimBoundaryAfterActivation', 'activeFinalNodeIds'], 'after boundary must bind eight UFS nodes plus activation node');
  return { tag: 'accept' };
}

function validateExamples0(manifest) {
  for (let i = 0; i < manifest.positiveExamples.length; i += 1) {
    const example = manifest.positiveExamples[i];
    const out = EvaluatePublicTheoremActivationExample0(example.input, { historicalReplay: true });
    if (out.tag !== 'accept') return reject0('PublicTheoremActivation.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out });
    for (const [key, expected] of Object.entries(example.expected)) {
      const actual = out[key];
      if (Array.isArray(expected) ? !sameArray0(actual, expected) : actual !== expected) return reject0('PublicTheoremActivation.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual });
    }
  }
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, label }) { if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; } try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('PublicTheoremActivation.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); } }
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('PublicTheoremActivation.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('PublicTheoremActivation.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('PublicTheoremActivation.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('PublicTheoremActivation.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('PublicTheoremActivation.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BEFORE_BLOCKERS] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true, historicalReplay: false }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else if (arg === '--historical-replay') out.historicalReplay = true; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('PublicTheoremActivation.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckPublicTheoremActivation0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
