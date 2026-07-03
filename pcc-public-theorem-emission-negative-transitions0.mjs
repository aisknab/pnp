#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckPublicTheoremEmissionPreflight0 } from './pcc-public-theorem-emission-preflight0.mjs';
import { CheckPublicTheoremEmissionDenial0 } from './pcc-public-theorem-emission-denial0.mjs';

const CHECKER = 'CheckPublicTheoremEmissionNegativeTransitions0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-EMISSION-NEGATIVE-TRANSITIONS-2026-06-27-01';
const OUT = 'artifacts/public-theorem-emission-negative-transitions/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  publicTheoremEmissionNegativeTransitionsCoordinate: COORD,
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
  manifest: 'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json',
  status: 'PNP_STATUS.json',
  preflight: 'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  denial: 'release/PUBLIC_THEOREM_EMISSION_DENIAL.json',
  releaseBlockerClearance: 'release/RELEASE_BLOCKER_CLEARANCE.json',
  externalReviewStatus: 'review/EXTERNAL_REVIEW_STATUS.json',
  publicReviewBoundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  negativeTransitionsDoc: 'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.md'
};
const EXPECTED_CASE_IDS = [
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

export async function CheckPublicTheoremEmissionNegativeTransitions0(options = {}) {
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
    const status = statusRead.value;
    const statusCheck = validateStatus0(status, manifest);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const preflightRead = await readJson0(root, manifest.sourceFiles.preflight, options.preflightOverride);
    if (preflightRead.tag === 'reject') return write0(root, outputPath, writeOutput, preflightRead);
    const preflight = preflightRead.value;
    const preflightCheck = validatePreflight0(preflight);
    if (preflightCheck.tag === 'reject') return write0(root, outputPath, writeOutput, preflightCheck);

    const denialRead = await readJson0(root, manifest.sourceFiles.denial, options.denialOverride);
    if (denialRead.tag === 'reject') return write0(root, outputPath, writeOutput, denialRead);
    const denial = denialRead.value;
    const denialCheck = validateDenial0(denial);
    if (denialCheck.tag === 'reject') return write0(root, outputPath, writeOutput, denialCheck);

    const clearanceRead = await readJson0(root, manifest.sourceFiles.releaseBlockerClearance, options.clearanceOverride);
    if (clearanceRead.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceRead);
    const clearance = clearanceRead.value;
    const clearanceCheck = validateClearance0(clearance);
    if (clearanceCheck.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceCheck);

    const externalRead = await readJson0(root, manifest.sourceFiles.externalReviewStatus, options.externalReviewOverride);
    if (externalRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalRead);
    const external = externalRead.value;
    const externalCheck = validateExternalReview0(external);
    if (externalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalCheck);

    const boundaryRead = await readJson0(root, manifest.sourceFiles.publicReviewBoundary, options.boundaryOverride);
    if (boundaryRead.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryRead);
    const boundary = boundaryRead.value;
    const boundaryCheck = validatePublicReviewBoundary0(boundary);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const docRead = await readText0(root, manifest.sourceFiles.negativeTransitionsDoc);
    if (docRead.tag === 'reject') return write0(root, outputPath, writeOutput, docRead);
    const docCheck = validateDoc0(docRead.text, manifest);
    if (docCheck.tag === 'reject') return write0(root, outputPath, writeOutput, docCheck);

    const current = await validateCurrentDeniedState0(root);
    if (current.tag === 'reject') return write0(root, outputPath, writeOutput, current);

    const negative = await runNegativeCases0(root, { status, preflight, denial, clearance, external, boundary });
    if (negative.tag === 'reject') return write0(root, outputPath, writeOutput, negative);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-theorem-emission-negative-transitions-accepted-non-activating',
      negativeTransitionAuditReady: true,
      currentDeniedStateAccepted: true,
      allNegativeTransitionsRejected: true,
      prematureActivationRejected: true,
      publicTheoremEmissionAllowedByNegativeTransitions: false,
      negativeTransitionAuditIsActivationSurface: false,
      negativeTransitionBindingRequiresFuturePR: false,
      negativeTransitionCaseCount: negative.cases.length,
      negativeTransitionCases: negative.cases,
      currentPreflightDigest: current.preflight.evidenceDigestSha256 ?? null,
      currentDenialDigest: current.denial.evidenceDigestSha256 ?? null,
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
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremEmissionNegativeTransitions.UnhandledException', [], 'negative transition checker threw unexpectedly', normErr0(error)));
  }
}

async function validateCurrentDeniedState0(root) {
  const preflight = await CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false });
  if (!plain0(preflight) || preflight.tag !== 'accept' || preflight.publicTheoremEmissionPreflightPassed !== false || preflight.publicTheoremEmissionDenied !== true || preflight.publicTheoremEmissionAllowed !== false || preflight.finalTheoremReady !== false) return reject0('PublicTheoremEmissionNegativeTransitions.CurrentPreflightMismatch', ['CheckPublicTheoremEmissionPreflight0'], 'current preflight is not accepted denied state', { actualTag: preflight?.tag ?? null });
  const denial = await CheckPublicTheoremEmissionDenial0({ root, writeOutput: false });
  if (!plain0(denial) || denial.tag !== 'accept' || denial.denialCertificateReady !== true || denial.publicTheoremEmissionDenied !== true || denial.publicTheoremEmissionAllowedByDenial !== false || denial.publicTheoremEmissionAllowed !== false || denial.finalTheoremReady !== false) return reject0('PublicTheoremEmissionNegativeTransitions.CurrentDenialMismatch', ['CheckPublicTheoremEmissionDenial0'], 'current denial certificate is not accepted denied state', { actualTag: denial?.tag ?? null });
  return { tag: 'accept', preflight, denial };
}

async function runNegativeCases0(root, data) {
  const cases = [];
  const pushReject = async (id, description, promise) => {
    const verdict = await promise;
    if (!plain0(verdict) || verdict.tag !== 'reject') return reject0('PublicTheoremEmissionNegativeTransitions.NegativeCaseAccepted', [id], 'negative transition was not rejected', { description, actualTag: verdict?.tag ?? null, actualCoordinate: verdict?.coordinate ?? null });
    cases.push({ id, description, expectedTag: 'reject', actualTag: verdict.tag, rejectionCoord: verdict.coord ?? null, rejectionPath: verdict.path ?? [] });
    return { tag: 'accept' };
  };
  const mutations = [
    ['NEG-001-status-public-emission-true', 'status publicTheoremEmissionAllowed=true', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, statusOverride: mutate0(data.status, { publicTheoremEmissionAllowed: true }) })],
    ['NEG-002-status-final-theorem-ready', 'status finalTheoremReady=true', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, statusOverride: mutate0(data.status, { finalTheoremReady: true }) })],
    ['NEG-003-status-active-final-node', 'status activeFinalNodeIds non-empty', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, statusOverride: mutate0(data.status, { activeFinalNodeIds: ['FinalPNPProofReport0'] }) })],
    ['NEG-004-status-blockers-cleared', 'status remainingBlockers=[]', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, statusOverride: mutate0(data.status, { remainingBlockers: [] }) })],
    ['NEG-005-clearance-accepted', 'release blocker clearance accepted', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, clearanceOverride: mutate0(data.clearance, { releaseBlockersStillActive: false, releaseBlockerClearanceAccepted: true, unrestrictedFinalSoundnessClearanceAccepted: true, externalReviewClearanceAccepted: true, publicTheoremEmissionAllowedByClearance: true, finalTheoremReadyByClearance: true }) })],
    ['NEG-006-external-review-accepted', 'external review accepted', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, externalReviewOverride: mutate0(data.external, { externalReviewAcceptanceClaimed: true, independentReviewAcceptanceConfirmed: true, externalReviewBlockerStillActive: false, substantiveFeedbackIsAcceptance: true, publicTheoremEmissionAllowedByExternalReview: true }) })],
    ['NEG-007-boundary-activating', 'public review boundary activating', CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false, boundaryOverride: mutate0(data.boundary, { publicTheoremEmissionAllowedByBoundary: true, finalTheoremReadyByBoundary: true, claimBoundary: mutate0(data.boundary.claimBoundary, { publicTheoremEmissionAllowed: true, finalTheoremReady: true }) }) })],
    ['NEG-008-preflight-passed', 'preflight manifest passed', CheckPublicTheoremEmissionDenial0({ root, writeOutput: false, preflightOverride: mutate0(data.preflight, { status: 'public-theorem-emission-preflight-passed', publicTheoremEmissionPreflightPassed: true, publicTheoremEmissionDenied: false, finalTheoremReadyByPreflight: true, blockedByRemainingBlockers: false }) })],
    ['NEG-009-denial-activation-surface', 'denial manifest activation surface', CheckPublicTheoremEmissionDenial0({ root, writeOutput: false, manifestOverride: mutate0(data.denial, { publicTheoremEmissionAllowedByDenial: true, finalTheoremReadyByDenial: true, denialCertificateIsActivationSurface: true, denialTransitionRequiresFuturePR: false, claimBoundary: mutate0(data.denial.claimBoundary, { publicTheoremEmissionAllowed: true, finalTheoremReady: true }) }) })]
  ];
  for (const [id, description, promise] of mutations) {
    const result = await pushReject(id, description, promise);
    if (result.tag === 'reject') return result;
  }
  if (!sameArray0(cases.map((x) => x.id), EXPECTED_CASE_IDS)) return reject0('PublicTheoremEmissionNegativeTransitions.CaseOrderMismatch', ['negativeTransitionCases'], 'negative case order mismatch', { actual: cases.map((x) => x.id), expected: EXPECTED_CASE_IDS });
  return { tag: 'accept', cases };
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicTheoremEmissionNegativeTransitions0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-theorem-emission-negative-transitions-ready') return reject0('PublicTheoremEmissionNegativeTransitions.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    negativeTransitionAuditReady: true,
    currentDeniedStateAccepted: true,
    allNegativeTransitionsRejected: true,
    prematureActivationRejected: true,
    publicTheoremEmissionAllowedByNegativeTransitions: false,
    negativeTransitionAuditIsActivationSurface: false,
    negativeTransitionBindingRequiresFuturePR: false
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicTheoremEmissionNegativeTransitions.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.sourceFiles)) return reject0('PublicTheoremEmissionNegativeTransitions.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [field, expected] of Object.entries(FILES)) if (field !== 'manifest' && m.sourceFiles[field] !== expected) return reject0('PublicTheoremEmissionNegativeTransitions.SourceFileMismatch', [FILES.manifest, 'sourceFiles', field], 'source file path mismatch', { expected, actual: m.sourceFiles[field] });
  if (!plain0(m.requiredCoordinates)) return reject0('PublicTheoremEmissionNegativeTransitions.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicTheoremEmissionNegativeTransitions.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredStatusVerificationSurfaceIds', 'negativeTransitionCases', 'requiredDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0) return reject0('PublicTheoremEmissionNegativeTransitions.ArrayMissing', [FILES.manifest, field], 'required manifest array missing');
  if (!sameArray0(m.negativeTransitionCases.map((x) => x.id), EXPECTED_CASE_IDS)) return reject0('PublicTheoremEmissionNegativeTransitions.CaseIds', [FILES.manifest, 'negativeTransitionCases'], 'negative transition case ids mismatch');
  for (const row of m.negativeTransitionCases) if (!plain0(row) || row.expectedOutcome !== 'reject' || typeof row.target !== 'string' || typeof row.mutation !== 'string') return reject0('PublicTheoremEmissionNegativeTransitions.CaseShape', [FILES.manifest, 'negativeTransitionCases'], 'negative transition case shape mismatch', { row });
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicTheoremEmissionNegativeTransitions.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionNegativeTransitions.StatusOverclaim', [FILES.status], 'status is not theorem-emission-denied');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('PublicTheoremEmissionNegativeTransitions.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicTheoremEmissionNegativeTransitions.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  return { tag: 'accept' };
}

function validatePreflight0(preflight) {
  if (!plain0(preflight) || preflight.kind !== 'PNPPublicTheoremEmissionPreflight0' || preflight.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionPreflightCoordinate || preflight.publicTheoremEmissionPreflightReady !== true || preflight.publicTheoremEmissionPreflightPassed !== false || preflight.publicTheoremEmissionDenied !== true || preflight.finalTheoremReadyByPreflight !== false) return reject0('PublicTheoremEmissionNegativeTransitions.PreflightMismatch', [FILES.preflight], 'preflight manifest mismatch or overclaim');
  return boundary0(preflight.claimBoundary, [FILES.preflight, 'claimBoundary']);
}
function validateDenial0(denial) {
  if (!plain0(denial) || denial.kind !== 'PNPPublicTheoremEmissionDenial0' || denial.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionDenialCoordinate || denial.denialCertificateReady !== true || denial.publicTheoremEmissionDenied !== true || denial.publicTheoremEmissionAllowedByDenial !== false || denial.publicTheoremEmissionPreflightPassed !== false || denial.denialCertificateIsActivationSurface !== false) return reject0('PublicTheoremEmissionNegativeTransitions.DenialMismatch', [FILES.denial], 'denial manifest mismatch or overclaim');
  return boundary0(denial.claimBoundary, [FILES.denial, 'claimBoundary']);
}
function validateClearance0(clearance) {
  if (!plain0(clearance) || clearance.kind !== 'PNPReleaseBlockerClearance0' || clearance.coordinate !== EXPECTED_COORDINATES.releaseBlockerClearanceCoordinate || clearance.releaseBlockersStillActive !== true || clearance.releaseBlockerClearanceAccepted !== false || clearance.publicTheoremEmissionAllowedByClearance !== false || clearance.finalTheoremReadyByClearance !== false) return reject0('PublicTheoremEmissionNegativeTransitions.ClearanceMismatch', [FILES.releaseBlockerClearance], 'clearance manifest mismatch or overclaim');
  return boundary0(clearance.claimBoundary, [FILES.releaseBlockerClearance, 'claimBoundary']);
}
function validateExternalReview0(external) {
  if (!plain0(external) || external.kind !== 'PNPExternalReviewStatus0' || external.coordinate !== EXPECTED_COORDINATES.externalReviewStatusCoordinate || external.externalReviewAcceptanceClaimed !== false || external.independentReviewAcceptanceConfirmed !== false || external.publicTheoremEmissionAllowedByExternalReview !== false) return reject0('PublicTheoremEmissionNegativeTransitions.ExternalReviewMismatch', [FILES.externalReviewStatus], 'external review manifest mismatch or overclaim');
  return boundary0(external.claimBoundary, [FILES.externalReviewStatus, 'claimBoundary']);
}
function validatePublicReviewBoundary0(boundaryManifest) {
  if (!plain0(boundaryManifest) || boundaryManifest.kind !== 'PNPPublicReviewBoundary0' || boundaryManifest.coordinate !== EXPECTED_COORDINATES.publicReviewBoundaryCoordinate || boundaryManifest.publicReviewBoundaryReady !== true || boundaryManifest.publicTheoremEmissionAllowedByBoundary !== false || boundaryManifest.finalTheoremReadyByBoundary !== false) return reject0('PublicTheoremEmissionNegativeTransitions.PublicReviewBoundaryMismatch', [FILES.publicReviewBoundary], 'public review boundary mismatch or overclaim');
  return boundary0(boundaryManifest.claimBoundary, [FILES.publicReviewBoundary, 'claimBoundary']);
}
function validateDoc0(text, manifest) {
  for (const fragment of manifest.requiredDocFragments) if (!text.includes(fragment)) return reject0('PublicTheoremEmissionNegativeTransitions.DocFragmentMissing', [FILES.negativeTransitionsDoc, fragment], 'negative transition doc required fragment missing');
  for (const row of manifest.negativeTransitionCases) if (!text.includes(row.id)) return reject0('PublicTheoremEmissionNegativeTransitions.DocCaseMissing', [FILES.negativeTransitionsDoc, row.id], 'negative transition doc case missing');
  return { tag: 'accept' };
}

function mutate0(value, patch) { return { ...deepCopy0(value), ...patch }; }
function deepCopy0(value) { return JSON.parse(JSON.stringify(value)); }
async function readJson0(root, rel, override) { if (override !== undefined) return { tag: 'accept', value: override }; try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('PublicTheoremEmissionNegativeTransitions.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); } }
async function readText0(root, rel) { try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; } catch (error) { return reject0('PublicTheoremEmissionNegativeTransitions.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); } }
async function digestEvidence0(root, paths) { const files = []; for (const rel of [...new Set(paths)]) { const safe = safeJoin0(root, rel); if (safe === null) return reject0('PublicTheoremEmissionNegativeTransitions.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path'); try { const info = await stat(safe); if (!info.isFile()) return reject0('PublicTheoremEmissionNegativeTransitions.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(safe); files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) }); } catch (error) { return reject0('PublicTheoremEmissionNegativeTransitions.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error)); } } return { tag: 'accept', files }; }
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicTheoremEmissionNegativeTransitions.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionNegativeTransitions.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-theorem-emission-negative-transitions0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public theorem emission negative transitions CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicTheoremEmissionNegativeTransitions0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
