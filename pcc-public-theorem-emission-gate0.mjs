#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckPublicTheoremEmissionPreflight0 } from './pcc-public-theorem-emission-preflight0.mjs';
import { CheckPublicTheoremEmissionDenial0 } from './pcc-public-theorem-emission-denial0.mjs';
import { CheckPublicTheoremEmissionNegativeTransitions0 } from './pcc-public-theorem-emission-negative-transitions0.mjs';

const CHECKER = 'CheckPublicTheoremEmissionGate0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-EMISSION-GATE-2026-06-27-01';
const OUT = 'artifacts/public-theorem-emission-gate/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  publicTheoremEmissionGateCoordinate: COORD,
  publicTheoremEmissionNegativeTransitionsCoordinate: 'PNP-PUBLIC-THEOREM-EMISSION-NEGATIVE-TRANSITIONS-2026-06-27-01',
  publicTheoremEmissionDenialCoordinate: 'PNP-PUBLIC-THEOREM-EMISSION-DENIAL-2026-06-27-01',
  publicTheoremEmissionPreflightCoordinate: 'PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01',
  releaseBlockerClearanceCoordinate: 'PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01',
  externalReviewStatusCoordinate: 'PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01',
  publicReviewChecklistCoordinate: 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01',
  publicReviewBoundaryCoordinate: 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const FILES = {
  manifest: 'release/PUBLIC_THEOREM_EMISSION_GATE.json',
  status: 'PNP_STATUS.json',
  preflight: 'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  denial: 'release/PUBLIC_THEOREM_EMISSION_DENIAL.json',
  negativeTransitions: 'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json',
  releaseBlockerClearance: 'release/RELEASE_BLOCKER_CLEARANCE.json',
  externalReviewStatus: 'review/EXTERNAL_REVIEW_STATUS.json',
  publicReviewBoundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  gateDoc: 'release/PUBLIC_THEOREM_EMISSION_GATE.md'
};
const EXPECTED_NEGATIVE_CASES = [
  'NEG-001-status-public-emission-true',
  'NEG-002-status-final-theorem-ready',
  'NEG-003-status-active-final-node',
  'NEG-004-status-blockers-cleared',
  'NEG-005-clearance-accepted',
  'NEG-006-external-review-accepted',
  'NEG-007-boundary-activating',
  'NEG-008-preflight-passed',
  'NEG-009-denial-activation-surface'
];

export async function CheckPublicTheoremEmissionGate0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? FILES.manifest, options.manifestOverride);
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifest = manifestRead.value;
    const manifestCheck = validateManifest0(manifest);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const statusRead = await readJson0(root, manifest.sourceFiles.status, options.statusOverride);
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const statusCheck = validateStatus0(statusRead.value, manifest);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const preflightRead = await readJson0(root, manifest.sourceFiles.preflight, options.preflightOverride);
    if (preflightRead.tag === 'reject') return write0(root, outputPath, writeOutput, preflightRead);
    const preflightCheck = validatePreflightManifest0(preflightRead.value, manifest);
    if (preflightCheck.tag === 'reject') return write0(root, outputPath, writeOutput, preflightCheck);

    const denialRead = await readJson0(root, manifest.sourceFiles.denial, options.denialOverride);
    if (denialRead.tag === 'reject') return write0(root, outputPath, writeOutput, denialRead);
    const denialCheck = validateDenialManifest0(denialRead.value, manifest);
    if (denialCheck.tag === 'reject') return write0(root, outputPath, writeOutput, denialCheck);

    const negativeRead = await readJson0(root, manifest.sourceFiles.negativeTransitions, options.negativeTransitionsOverride);
    if (negativeRead.tag === 'reject') return write0(root, outputPath, writeOutput, negativeRead);
    const negativeCheck = validateNegativeTransitionsManifest0(negativeRead.value, manifest);
    if (negativeCheck.tag === 'reject') return write0(root, outputPath, writeOutput, negativeCheck);

    const clearanceRead = await readJson0(root, manifest.sourceFiles.releaseBlockerClearance, options.clearanceOverride);
    if (clearanceRead.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceRead);
    const clearanceCheck = validateClearance0(clearanceRead.value);
    if (clearanceCheck.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceCheck);

    const externalRead = await readJson0(root, manifest.sourceFiles.externalReviewStatus, options.externalReviewOverride);
    if (externalRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalRead);
    const externalCheck = validateExternalReview0(externalRead.value);
    if (externalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalCheck);

    const boundaryRead = await readJson0(root, manifest.sourceFiles.publicReviewBoundary, options.boundaryOverride);
    if (boundaryRead.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryRead);
    const boundaryCheck = validateBoundaryManifest0(boundaryRead.value);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const docRead = await readText0(root, manifest.sourceFiles.gateDoc);
    if (docRead.tag === 'reject') return write0(root, outputPath, writeOutput, docRead);
    const docCheck = validateDoc0(docRead.text, manifest);
    if (docCheck.tag === 'reject') return write0(root, outputPath, writeOutput, docCheck);

    const current = await validateCurrentGateInputs0(root);
    if (current.tag === 'reject') return write0(root, outputPath, writeOutput, current);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-theorem-emission-gate-accepted-denied-status-bound-non-activating',
      publicTheoremEmissionGateReady: true,
      publicTheoremEmissionGatePassed: false,
      publicTheoremEmissionDenied: true,
      currentDeniedStateAccepted: true,
      denialCertificateBound: true,
      preflightBound: true,
      negativeTransitionsBound: true,
      statusBound: true,
      allNegativeTransitionsRejected: true,
      prematureActivationRejected: true,
      releaseBlockersStillActive: true,
      publicTheoremEmissionAllowedByGate: false,
      finalTheoremReadyByGate: false,
      gateIsActivationSurface: false,
      gateBindingRequiresFuturePR: false,
      deniedReasonCount: manifest.requiredDeniedReasons.length,
      negativeTransitionCaseCount: manifest.requiredNegativeTransitionCaseIds.length,
      currentPreflightDigest: current.preflight.evidenceDigestSha256 ?? null,
      currentDenialDigest: current.denial.evidenceDigestSha256 ?? null,
      currentNegativeTransitionsDigest: current.negative.evidenceDigestSha256 ?? null,
      requiredCoordinates: { ...EXPECTED_COORDINATES },
      evidenceFileCount: evidence.files.length,
      evidenceDigestSha256: shaText0(stable0(evidence.files)),
      evidenceFiles: evidence.files,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremEmissionGate.UnhandledException', [], 'public theorem-emission gate checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicTheoremEmissionGate0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-theorem-emission-gate-denied') return reject0('PublicTheoremEmissionGate.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    publicTheoremEmissionGateReady: true,
    publicTheoremEmissionGatePassed: false,
    publicTheoremEmissionDenied: true,
    currentDeniedStateAccepted: true,
    denialCertificateBound: true,
    preflightBound: true,
    negativeTransitionsBound: true,
    statusBound: true,
    allNegativeTransitionsRejected: true,
    prematureActivationRejected: true,
    releaseBlockersStillActive: true,
    publicTheoremEmissionAllowedByGate: false,
    finalTheoremReadyByGate: false,
    gateIsActivationSurface: false,
    gateBindingRequiresFuturePR: false
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicTheoremEmissionGate.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.sourceFiles)) return reject0('PublicTheoremEmissionGate.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [field, expected] of Object.entries(FILES)) if (field !== 'manifest' && m.sourceFiles[field] !== expected) return reject0('PublicTheoremEmissionGate.SourceFileMismatch', [FILES.manifest, 'sourceFiles', field], 'source file path mismatch', { expected, actual: m.sourceFiles[field] });
  if (!plain0(m.requiredCoordinates)) return reject0('PublicTheoremEmissionGate.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicTheoremEmissionGate.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredStatusVerificationSurfaceIds', 'requiredDeniedReasons', 'requiredNegativeTransitionCaseIds', 'requiredDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('PublicTheoremEmissionGate.ArrayMissing', [FILES.manifest, field], 'manifest string array missing or invalid');
  if (!sameArray0(m.requiredNegativeTransitionCaseIds, EXPECTED_NEGATIVE_CASES)) return reject0('PublicTheoremEmissionGate.NegativeCaseIds', [FILES.manifest, 'requiredNegativeTransitionCaseIds'], 'negative case ids mismatch', { expected: EXPECTED_NEGATIVE_CASES, actual: m.requiredNegativeTransitionCaseIds });
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicTheoremEmissionGate.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('PublicTheoremEmissionGate.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicTheoremEmissionGate.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  return { tag: 'accept' };
}

function validatePreflightManifest0(preflight, manifest) {
  if (!plain0(preflight) || preflight.kind !== 'PNPPublicTheoremEmissionPreflight0' || preflight.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionPreflightCoordinate || preflight.publicTheoremEmissionPreflightReady !== true || preflight.publicTheoremEmissionPreflightPassed !== false || preflight.publicTheoremEmissionDenied !== true || preflight.publicTheoremEmissionAllowed !== undefined || preflight.finalTheoremReadyByPreflight !== false || preflight.preflightTransitionRequiresFuturePR !== true) return reject0('PublicTheoremEmissionGate.PreflightMismatch', [FILES.preflight], 'preflight manifest mismatch or overclaim');
  const boundary = boundary0(preflight.claimBoundary, [FILES.preflight, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const reason of manifest.requiredDeniedReasons) if (!preflight.requiredDeniedReasons?.includes?.(reason)) return reject0('PublicTheoremEmissionGate.PreflightDeniedReasonMissing', [FILES.preflight, 'requiredDeniedReasons'], 'preflight denied reason missing', { reason });
  return { tag: 'accept' };
}

function validateDenialManifest0(denial, manifest) {
  if (!plain0(denial) || denial.kind !== 'PNPPublicTheoremEmissionDenial0' || denial.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionDenialCoordinate || denial.denialCertificateReady !== true || denial.publicTheoremEmissionDenied !== true || denial.publicTheoremEmissionAllowedByDenial !== false || denial.publicTheoremEmissionPreflightPassed !== false || denial.finalTheoremReadyByDenial !== false || !sameArray0(denial.activeFinalNodeIdsByDenial, []) || denial.denialCertificateIsActivationSurface !== false || denial.denialTransitionRequiresFuturePR !== true) return reject0('PublicTheoremEmissionGate.DenialMismatch', [FILES.denial], 'denial manifest mismatch or overclaim');
  const boundary = boundary0(denial.claimBoundary, [FILES.denial, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const reason of manifest.requiredDeniedReasons) if (!denial.requiredDeniedReasons?.includes?.(reason)) return reject0('PublicTheoremEmissionGate.DenialReasonMissing', [FILES.denial, 'requiredDeniedReasons'], 'denial reason missing', { reason });
  return { tag: 'accept' };
}

function validateNegativeTransitionsManifest0(negative, manifest) {
  if (!plain0(negative) || negative.kind !== 'PNPPublicTheoremEmissionNegativeTransitions0' || negative.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionNegativeTransitionsCoordinate || negative.negativeTransitionAuditReady !== true || negative.currentDeniedStateAccepted !== true || negative.allNegativeTransitionsRejected !== true || negative.prematureActivationRejected !== true || negative.publicTheoremEmissionAllowedByNegativeTransitions !== false || negative.negativeTransitionAuditIsActivationSurface !== false || negative.negativeTransitionBindingRequiresFuturePR !== false) return reject0('PublicTheoremEmissionGate.NegativeTransitionsMismatch', [FILES.negativeTransitions], 'negative-transition manifest mismatch or overclaim');
  const boundary = boundary0(negative.claimBoundary, [FILES.negativeTransitions, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  const ids = (negative.negativeTransitionCases ?? []).map((x) => x.id);
  if (!sameArray0(ids, manifest.requiredNegativeTransitionCaseIds)) return reject0('PublicTheoremEmissionGate.NegativeTransitionCaseMismatch', [FILES.negativeTransitions, 'negativeTransitionCases'], 'negative transition case ids mismatch', { expected: manifest.requiredNegativeTransitionCaseIds, actual: ids });
  return { tag: 'accept' };
}

function validateClearance0(clearance) {
  if (!plain0(clearance) || clearance.kind !== 'PNPReleaseBlockerClearance0' || clearance.coordinate !== EXPECTED_COORDINATES.releaseBlockerClearanceCoordinate || clearance.releaseBlockersStillActive !== true || clearance.releaseBlockerClearanceAccepted !== false || clearance.publicTheoremEmissionAllowedByClearance !== false || clearance.finalTheoremReadyByClearance !== false) return reject0('PublicTheoremEmissionGate.ClearanceMismatch', [FILES.releaseBlockerClearance], 'release blocker clearance mismatch or overclaim');
  return boundary0(clearance.claimBoundary, [FILES.releaseBlockerClearance, 'claimBoundary']);
}

function validateExternalReview0(external) {
  if (!plain0(external) || external.kind !== 'PNPExternalReviewStatus0' || external.coordinate !== EXPECTED_COORDINATES.externalReviewStatusCoordinate || external.externalReviewAcceptanceClaimed !== false || external.independentReviewAcceptanceConfirmed !== false || external.externalReviewBlockerStillActive !== true || external.publicTheoremEmissionAllowedByExternalReview !== false) return reject0('PublicTheoremEmissionGate.ExternalReviewMismatch', [FILES.externalReviewStatus], 'external review status mismatch or overclaim');
  return boundary0(external.claimBoundary, [FILES.externalReviewStatus, 'claimBoundary']);
}

function validateBoundaryManifest0(boundary) {
  if (!plain0(boundary) || boundary.kind !== 'PNPPublicReviewBoundary0' || boundary.coordinate !== EXPECTED_COORDINATES.publicReviewBoundaryCoordinate || boundary.publicReviewBoundaryReady !== true || boundary.publicTheoremEmissionAllowedByBoundary !== false || boundary.finalTheoremReadyByBoundary !== false) return reject0('PublicTheoremEmissionGate.BoundaryMismatch', [FILES.publicReviewBoundary], 'public review boundary mismatch or overclaim');
  return boundary0(boundary.claimBoundary, [FILES.publicReviewBoundary, 'claimBoundary']);
}

function validateDoc0(text, manifest) {
  for (const fragment of manifest.requiredDocFragments) if (!text.includes(fragment)) return reject0('PublicTheoremEmissionGate.DocFragmentMissing', [FILES.gateDoc, fragment], 'gate doc required fragment missing');
  for (const expected of Object.values(EXPECTED_COORDINATES)) if (!text.includes(expected)) return reject0('PublicTheoremEmissionGate.DocCoordinateMissing', [FILES.gateDoc, expected], 'gate doc required coordinate missing');
  return { tag: 'accept' };
}

async function validateCurrentGateInputs0(root) {
  const preflight = await CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false });
  if (!plain0(preflight) || preflight.tag !== 'accept' || preflight.publicTheoremEmissionPreflightPassed !== false || preflight.publicTheoremEmissionDenied !== true || preflight.publicTheoremEmissionAllowed !== false || preflight.finalTheoremReady !== false) return reject0('PublicTheoremEmissionGate.CurrentPreflightMismatch', ['CheckPublicTheoremEmissionPreflight0'], 'current preflight did not accept denied state', { actualTag: preflight?.tag ?? null });
  const denial = await CheckPublicTheoremEmissionDenial0({ root, writeOutput: false });
  if (!plain0(denial) || denial.tag !== 'accept' || denial.denialCertificateReady !== true || denial.publicTheoremEmissionDenied !== true || denial.publicTheoremEmissionAllowedByDenial !== false || denial.publicTheoremEmissionAllowed !== false || denial.finalTheoremReady !== false) return reject0('PublicTheoremEmissionGate.CurrentDenialMismatch', ['CheckPublicTheoremEmissionDenial0'], 'current denial did not accept denied state', { actualTag: denial?.tag ?? null });
  const negative = await CheckPublicTheoremEmissionNegativeTransitions0({ root, writeOutput: false });
  if (!plain0(negative) || negative.tag !== 'accept' || negative.allNegativeTransitionsRejected !== true || negative.prematureActivationRejected !== true || negative.publicTheoremEmissionAllowedByNegativeTransitions !== false || negative.publicTheoremEmissionAllowed !== false || negative.finalTheoremReady !== false) return reject0('PublicTheoremEmissionGate.CurrentNegativeTransitionsMismatch', ['CheckPublicTheoremEmissionNegativeTransitions0'], 'current negative-transition audit did not accept denied state', { actualTag: negative?.tag ?? null });
  return { tag: 'accept', preflight, denial, negative };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionGate.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionGate.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicTheoremEmissionGate.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicTheoremEmissionGate.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicTheoremEmissionGate.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicTheoremEmissionGate.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionGate.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function safeJoinRequired0(root, rel) { const p = safeJoin0(root, rel); if (p === null) throw new Error(`unsafe path: ${rel}`); return p; }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function shaBytes0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return createHash('sha256').update(String(text), 'utf8').digest('hex'); }
function normErr0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-theorem-emission-gate0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public theorem-emission gate CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicTheoremEmissionGate0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
