#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckPublicTheoremEmissionStatus0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-EMISSION-STATUS-2026-06-27-01';
const OUT = 'artifacts/public-theorem-emission-status/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  publicTheoremEmissionGateCoordinate: 'PNP-PUBLIC-THEOREM-EMISSION-GATE-2026-06-27-01',
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
const EXPECTED_DENIED_REASONS = [
  'Status.PublicTheoremEmissionAllowedFalse',
  'Status.FinalTheoremReadyFalse',
  'Status.RemainingBlockersActive',
  'ReleaseBlockerClearance.NotAccepted',
  'ExternalReview.AcceptanceNotClaimed',
  'ReleaseLadder.PublicTheoremEmissionCandidateBlocked',
  'GapLedger.ActivationBlockingGapsOpen',
  'ProofObligationLedger.ReleaseObligationsBlocked'
];
const FILES = {
  manifest: 'release/PUBLIC_THEOREM_EMISSION_STATUS.json',
  status: 'PNP_STATUS.json',
  gate: 'release/PUBLIC_THEOREM_EMISSION_GATE.json',
  preflight: 'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  denial: 'release/PUBLIC_THEOREM_EMISSION_DENIAL.json',
  negativeTransitions: 'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json',
  releaseBlockerClearance: 'release/RELEASE_BLOCKER_CLEARANCE.json',
  externalReviewStatus: 'review/EXTERNAL_REVIEW_STATUS.json',
  publicReviewBoundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  statusDoc: 'release/PUBLIC_THEOREM_EMISSION_STATUS.md'
};

export async function CheckPublicTheoremEmissionStatus0(options = {}) {
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

    const gateRead = await readJson0(root, manifest.sourceFiles.gate, options.gateOverride);
    if (gateRead.tag === 'reject') return write0(root, outputPath, writeOutput, gateRead);
    const gateCheck = validateGate0(gateRead.value, manifest);
    if (gateCheck.tag === 'reject') return write0(root, outputPath, writeOutput, gateCheck);

    const preflightRead = await readJson0(root, manifest.sourceFiles.preflight, options.preflightOverride);
    if (preflightRead.tag === 'reject') return write0(root, outputPath, writeOutput, preflightRead);
    const preflightCheck = validatePreflight0(preflightRead.value, manifest);
    if (preflightCheck.tag === 'reject') return write0(root, outputPath, writeOutput, preflightCheck);

    const denialRead = await readJson0(root, manifest.sourceFiles.denial, options.denialOverride);
    if (denialRead.tag === 'reject') return write0(root, outputPath, writeOutput, denialRead);
    const denialCheck = validateDenial0(denialRead.value, manifest);
    if (denialCheck.tag === 'reject') return write0(root, outputPath, writeOutput, denialCheck);

    const negativeRead = await readJson0(root, manifest.sourceFiles.negativeTransitions, options.negativeOverride);
    if (negativeRead.tag === 'reject') return write0(root, outputPath, writeOutput, negativeRead);
    const negativeCheck = validateNegativeTransitions0(negativeRead.value);
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
    const boundaryCheck = validatePublicReviewBoundary0(boundaryRead.value);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const docRead = await readText0(root, manifest.sourceFiles.statusDoc);
    if (docRead.tag === 'reject') return write0(root, outputPath, writeOutput, docRead);
    const docCheck = validateDoc0(docRead.text, manifest);
    if (docCheck.tag === 'reject') return write0(root, outputPath, writeOutput, docCheck);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-theorem-emission-status-accepted-denied-non-activating',
      publicTheoremEmissionStatusReady: true,
      statusDocReady: true,
      statusBound: false,
      gateStatusBound: true,
      gatePassed: false,
      gateDenied: true,
      preflightPassed: false,
      denialCertificateReady: true,
      negativeTransitionsRejected: true,
      releaseBlockersStillActive: true,
      externalReviewAcceptanceClaimed: false,
      currentPublicEmissionState: 'denied',
      allActivationBlockersVisible: true,
      publicTheoremEmissionAllowedByStatus: false,
      finalTheoremReadyByStatus: false,
      statusSummaryIsActivationSurface: false,
      statusSummaryBindingRequiresFuturePR: true,
      deniedReasonCount: manifest.requiredDeniedReasons.length,
      requiredStatusVerificationSurfaceCount: manifest.requiredStatusVerificationSurfaceIds.length,
      requiredCoordinates: { ...EXPECTED_COORDINATES },
      statusDocSha256: shaBytes0(docRead.bytes),
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
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremEmissionStatus.UnhandledException', [], 'public theorem-emission status checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicTheoremEmissionStatus0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-theorem-emission-status-denied') return reject0('PublicTheoremEmissionStatus.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    publicTheoremEmissionStatusReady: true,
    statusDocReady: true,
    statusBound: false,
    gateStatusBound: true,
    gatePassed: false,
    gateDenied: true,
    preflightPassed: false,
    denialCertificateReady: true,
    negativeTransitionsRejected: true,
    releaseBlockersStillActive: true,
    externalReviewAcceptanceClaimed: false,
    currentPublicEmissionState: 'denied',
    allActivationBlockersVisible: true,
    publicTheoremEmissionAllowedByStatus: false,
    finalTheoremReadyByStatus: false,
    statusSummaryIsActivationSurface: false,
    statusSummaryBindingRequiresFuturePR: true
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicTheoremEmissionStatus.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.sourceFiles)) return reject0('PublicTheoremEmissionStatus.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [field, expected] of Object.entries(FILES)) if (field !== 'manifest' && m.sourceFiles[field] !== expected) return reject0('PublicTheoremEmissionStatus.SourceFileMismatch', [FILES.manifest, 'sourceFiles', field], 'source file path mismatch', { expected, actual: m.sourceFiles[field] });
  if (!plain0(m.requiredCoordinates)) return reject0('PublicTheoremEmissionStatus.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicTheoremEmissionStatus.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  if (!sameArray0(m.requiredDeniedReasons, EXPECTED_DENIED_REASONS)) return reject0('PublicTheoremEmissionStatus.DeniedReasons', [FILES.manifest, 'requiredDeniedReasons'], 'denied reasons mismatch', { expected: EXPECTED_DENIED_REASONS, actual: m.requiredDeniedReasons });
  for (const field of ['requiredStatusVerificationSurfaceIds', 'requiredStatusDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('PublicTheoremEmissionStatus.ArrayMissing', [FILES.manifest, field], 'manifest string array missing or invalid');
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicTheoremEmissionStatus.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('PublicTheoremEmissionStatus.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicTheoremEmissionStatus.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  if (status.publicTheoremEmissionStatusCoordinate !== undefined) return reject0('PublicTheoremEmissionStatus.StatusAlreadyBound', [FILES.status, 'publicTheoremEmissionStatusCoordinate'], 'status summary must remain unbound until a future binding PR');
  return { tag: 'accept' };
}

function validateGate0(gate, manifest) {
  if (!plain0(gate) || gate.kind !== 'PNPPublicTheoremEmissionGate0' || gate.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionGateCoordinate || gate.publicTheoremEmissionGatePassed !== false || gate.publicTheoremEmissionDenied !== true || gate.statusBound !== true || gate.publicTheoremEmissionAllowedByGate !== false || gate.finalTheoremReadyByGate !== false || gate.gateIsActivationSurface !== false) return reject0('PublicTheoremEmissionStatus.GateMismatch', [FILES.gate], 'gate mismatch or overclaim');
  const boundary = boundary0(gate.claimBoundary, [FILES.gate, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const reason of manifest.requiredDeniedReasons) if (!gate.requiredDeniedReasons?.includes?.(reason)) return reject0('PublicTheoremEmissionStatus.GateDeniedReasonMissing', [FILES.gate, 'requiredDeniedReasons'], 'gate denied reason missing', { reason });
  return { tag: 'accept' };
}

function validatePreflight0(preflight, manifest) {
  if (!plain0(preflight) || preflight.kind !== 'PNPPublicTheoremEmissionPreflight0' || preflight.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionPreflightCoordinate || preflight.publicTheoremEmissionPreflightPassed !== false || preflight.publicTheoremEmissionDenied !== true || preflight.preflightTransitionRequiresFuturePR !== true || preflight.finalTheoremReadyByPreflight !== false) return reject0('PublicTheoremEmissionStatus.PreflightMismatch', [FILES.preflight], 'preflight mismatch or overclaim');
  const boundary = boundary0(preflight.claimBoundary, [FILES.preflight, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const reason of manifest.requiredDeniedReasons) if (!preflight.requiredDeniedReasons?.includes?.(reason)) return reject0('PublicTheoremEmissionStatus.PreflightDeniedReasonMissing', [FILES.preflight, 'requiredDeniedReasons'], 'preflight denied reason missing', { reason });
  return { tag: 'accept' };
}

function validateDenial0(denial, manifest) {
  if (!plain0(denial) || denial.kind !== 'PNPPublicTheoremEmissionDenial0' || denial.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionDenialCoordinate || denial.denialCertificateReady !== true || denial.publicTheoremEmissionDenied !== true || denial.publicTheoremEmissionAllowedByDenial !== false || denial.publicTheoremEmissionPreflightPassed !== false || denial.finalTheoremReadyByDenial !== false || denial.denialCertificateIsActivationSurface !== false) return reject0('PublicTheoremEmissionStatus.DenialMismatch', [FILES.denial], 'denial mismatch or overclaim');
  const boundary = boundary0(denial.claimBoundary, [FILES.denial, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const reason of manifest.requiredDeniedReasons) if (!denial.requiredDeniedReasons?.includes?.(reason)) return reject0('PublicTheoremEmissionStatus.DenialReasonMissing', [FILES.denial, 'requiredDeniedReasons'], 'denial reason missing', { reason });
  return { tag: 'accept' };
}

function validateNegativeTransitions0(negative) {
  if (!plain0(negative) || negative.kind !== 'PNPPublicTheoremEmissionNegativeTransitions0' || negative.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionNegativeTransitionsCoordinate || negative.negativeTransitionAuditReady !== true || negative.allNegativeTransitionsRejected !== true || negative.prematureActivationRejected !== true || negative.publicTheoremEmissionAllowedByNegativeTransitions !== false || negative.negativeTransitionAuditIsActivationSurface !== false) return reject0('PublicTheoremEmissionStatus.NegativeTransitionsMismatch', [FILES.negativeTransitions], 'negative transition audit mismatch or overclaim');
  const boundary = boundary0(negative.claimBoundary, [FILES.negativeTransitions, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!Array.isArray(negative.negativeTransitionCases) || negative.negativeTransitionCases.length !== 9 || negative.negativeTransitionCases.some((x) => x.expectedOutcome !== 'reject')) return reject0('PublicTheoremEmissionStatus.NegativeTransitionCases', [FILES.negativeTransitions, 'negativeTransitionCases'], 'negative transition cases mismatch');
  return { tag: 'accept' };
}

function validateClearance0(clearance) {
  if (!plain0(clearance) || clearance.kind !== 'PNPReleaseBlockerClearance0' || clearance.coordinate !== EXPECTED_COORDINATES.releaseBlockerClearanceCoordinate || clearance.releaseBlockersStillActive !== true || clearance.releaseBlockerClearanceAccepted !== false || clearance.publicTheoremEmissionAllowedByClearance !== false || clearance.finalTheoremReadyByClearance !== false) return reject0('PublicTheoremEmissionStatus.ClearanceMismatch', [FILES.releaseBlockerClearance], 'release blocker clearance mismatch or overclaim');
  return boundary0(clearance.claimBoundary, [FILES.releaseBlockerClearance, 'claimBoundary']);
}

function validateExternalReview0(external) {
  if (!plain0(external) || external.kind !== 'PNPExternalReviewStatus0' || external.coordinate !== EXPECTED_COORDINATES.externalReviewStatusCoordinate || external.externalReviewAcceptanceClaimed !== false || external.independentReviewAcceptanceConfirmed !== false || external.externalReviewBlockerStillActive !== true || external.publicTheoremEmissionAllowedByExternalReview !== false) return reject0('PublicTheoremEmissionStatus.ExternalReviewMismatch', [FILES.externalReviewStatus], 'external review status mismatch or overclaim');
  return boundary0(external.claimBoundary, [FILES.externalReviewStatus, 'claimBoundary']);
}

function validatePublicReviewBoundary0(boundary) {
  if (!plain0(boundary) || boundary.kind !== 'PNPPublicReviewBoundary0' || boundary.coordinate !== EXPECTED_COORDINATES.publicReviewBoundaryCoordinate || boundary.publicReviewBoundaryReady !== true || boundary.publicTheoremEmissionAllowedByBoundary !== false || boundary.finalTheoremReadyByBoundary !== false) return reject0('PublicTheoremEmissionStatus.BoundaryMismatch', [FILES.publicReviewBoundary], 'public review boundary mismatch or overclaim');
  return boundary0(boundary.claimBoundary, [FILES.publicReviewBoundary, 'claimBoundary']);
}

function validateDoc0(text, manifest) {
  for (const fragment of manifest.requiredStatusDocFragments) if (!text.includes(fragment)) return reject0('PublicTheoremEmissionStatus.DocFragmentMissing', [FILES.statusDoc, fragment], 'status doc required fragment missing');
  for (const expected of Object.values(EXPECTED_COORDINATES)) if (!text.includes(expected)) return reject0('PublicTheoremEmissionStatus.DocCoordinateMissing', [FILES.statusDoc, expected], 'status doc required coordinate missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionStatus.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionStatus.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicTheoremEmissionStatus.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicTheoremEmissionStatus.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicTheoremEmissionStatus.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicTheoremEmissionStatus.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionStatus.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-theorem-emission-status0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public theorem-emission status CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicTheoremEmissionStatus0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
