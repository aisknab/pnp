#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckPublicTheoremEmissionPreflight0 } from './pcc-public-theorem-emission-preflight0.mjs';

const CHECKER = 'CheckPublicTheoremEmissionDenial0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-EMISSION-DENIAL-2026-06-27-01';
const OUT = 'artifacts/public-theorem-emission-denial/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  publicTheoremEmissionDenialCoordinate: COORD,
  publicTheoremEmissionPreflightCoordinate: 'PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01',
  releaseBlockerClearanceCoordinate: 'PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01',
  externalReviewStatusCoordinate: 'PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01',
  publicReviewChecklistCoordinate: 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01',
  publicReviewBoundaryCoordinate: 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const FILES = {
  manifest: 'release/PUBLIC_THEOREM_EMISSION_DENIAL.json',
  status: 'PNP_STATUS.json',
  preflight: 'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  releaseBlockerClearance: 'release/RELEASE_BLOCKER_CLEARANCE.json',
  externalReviewStatus: 'review/EXTERNAL_REVIEW_STATUS.json',
  publicReviewBoundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  denialDoc: 'release/PUBLIC_THEOREM_EMISSION_DENIAL.md'
};

export async function CheckPublicTheoremEmissionDenial0(options = {}) {
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

    const preflightVerdict = await CheckPublicTheoremEmissionPreflight0({ root, writeOutput: false });
    const preflightVerdictCheck = validatePreflightVerdict0(preflightVerdict, manifest);
    if (preflightVerdictCheck.tag === 'reject') return write0(root, outputPath, writeOutput, preflightVerdictCheck);

    const clearanceRead = await readJson0(root, manifest.sourceFiles.releaseBlockerClearance, options.clearanceOverride);
    if (clearanceRead.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceRead);
    const clearanceCheck = validateReleaseBlockerClearance0(clearanceRead.value);
    if (clearanceCheck.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceCheck);

    const externalRead = await readJson0(root, manifest.sourceFiles.externalReviewStatus, options.externalReviewOverride);
    if (externalRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalRead);
    const externalCheck = validateExternalReviewStatus0(externalRead.value);
    if (externalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalCheck);

    const boundaryRead = await readJson0(root, manifest.sourceFiles.publicReviewBoundary, options.boundaryOverride);
    if (boundaryRead.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryRead);
    const boundaryCheck = validatePublicReviewBoundary0(boundaryRead.value);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const docRead = await readText0(root, manifest.sourceFiles.denialDoc);
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
      claimStatus: 'public-theorem-emission-denial-certified-non-activating',
      denialCertificateReady: true,
      publicTheoremEmissionDenied: true,
      publicTheoremEmissionAllowedByDenial: false,
      publicTheoremEmissionPreflightPassed: false,
      finalTheoremReadyByDenial: false,
      activeFinalNodeIdsByDenial: [],
      blockedByRemainingBlockers: true,
      releaseBlockerClearanceAccepted: false,
      externalReviewAcceptanceClaimed: false,
      unrestrictedFinalSoundnessClearanceAccepted: false,
      denialCertificateIsActivationSurface: false,
      denialTransitionRequiresFuturePR: true,
      deniedReasons: manifest.requiredDeniedReasons,
      requiredCoordinates: { ...EXPECTED_COORDINATES },
      preflightVerdictDigest: preflightVerdict.evidenceDigestSha256 ?? null,
      denialDocSha256: shaBytes0(docRead.bytes),
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
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremEmissionDenial.UnhandledException', [], 'public theorem-emission denial checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicTheoremEmissionDenial0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-theorem-emission-denial-certified') return reject0('PublicTheoremEmissionDenial.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    denialCertificateReady: true,
    publicTheoremEmissionDenied: true,
    publicTheoremEmissionAllowedByDenial: false,
    publicTheoremEmissionPreflightPassed: false,
    finalTheoremReadyByDenial: false,
    blockedByRemainingBlockers: true,
    releaseBlockerClearanceAccepted: false,
    externalReviewAcceptanceClaimed: false,
    unrestrictedFinalSoundnessClearanceAccepted: false,
    denialCertificateIsActivationSurface: false,
    denialTransitionRequiresFuturePR: true
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicTheoremEmissionDenial.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  if (!sameArray0(m.activeFinalNodeIdsByDenial, [])) return reject0('PublicTheoremEmissionDenial.ActiveNodes', [FILES.manifest, 'activeFinalNodeIdsByDenial'], 'active final nodes must be empty');
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.sourceFiles)) return reject0('PublicTheoremEmissionDenial.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [field, expected] of Object.entries(FILES)) if (field !== 'manifest' && m.sourceFiles[field] !== expected) return reject0('PublicTheoremEmissionDenial.SourceFileMismatch', [FILES.manifest, 'sourceFiles', field], 'source file path mismatch', { expected, actual: m.sourceFiles[field] });
  if (!plain0(m.requiredCoordinates)) return reject0('PublicTheoremEmissionDenial.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicTheoremEmissionDenial.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredStatusVerificationSurfaceIds', 'requiredDeniedReasons', 'requiredDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('PublicTheoremEmissionDenial.ArrayMissing', [FILES.manifest, field], 'manifest string array missing or invalid');
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicTheoremEmissionDenial.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionDenial.StatusOverclaim', [FILES.status], 'status is not theorem-emission-denied');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('PublicTheoremEmissionDenial.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicTheoremEmissionDenial.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  return { tag: 'accept' };
}

function validatePreflightManifest0(preflight, manifest) {
  if (!plain0(preflight) || preflight.kind !== 'PNPPublicTheoremEmissionPreflight0' || preflight.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionPreflightCoordinate || preflight.publicTheoremEmissionPreflightReady !== true || preflight.publicTheoremEmissionPreflightPassed !== false || preflight.publicTheoremEmissionDenied !== true || preflight.finalTheoremReadyByPreflight !== false || preflight.blockedByRemainingBlockers !== true) return reject0('PublicTheoremEmissionDenial.PreflightMismatch', [FILES.preflight], 'public theorem-emission preflight mismatch or overclaim');
  const boundary = boundary0(preflight.claimBoundary, [FILES.preflight, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!sameArray0(preflight.requiredDeniedReasons, manifest.requiredDeniedReasons)) return reject0('PublicTheoremEmissionDenial.PreflightDeniedReasons', [FILES.preflight, 'requiredDeniedReasons'], 'preflight denied reasons mismatch', { expected: manifest.requiredDeniedReasons, actual: preflight.requiredDeniedReasons });
  return { tag: 'accept' };
}

function validatePreflightVerdict0(verdict, manifest) {
  if (!plain0(verdict) || verdict.tag !== 'accept' || verdict.coordinate !== EXPECTED_COORDINATES.publicTheoremEmissionPreflightCoordinate || verdict.publicTheoremEmissionPreflightReady !== true || verdict.publicTheoremEmissionPreflightPassed !== false || verdict.publicTheoremEmissionDenied !== true || verdict.finalTheoremReadyByPreflight !== false || verdict.publicTheoremEmissionAllowed !== false || verdict.finalTheoremReady !== false) return reject0('PublicTheoremEmissionDenial.PreflightVerdictMismatch', ['CheckPublicTheoremEmissionPreflight0'], 'public theorem-emission preflight verdict mismatch or overclaim', { actualTag: verdict?.tag ?? null, actualCoordinate: verdict?.coordinate ?? null });
  if (!sameArray0(verdict.deniedReasons, manifest.requiredDeniedReasons)) return reject0('PublicTheoremEmissionDenial.PreflightVerdictDeniedReasons', ['CheckPublicTheoremEmissionPreflight0', 'deniedReasons'], 'preflight verdict denied reasons mismatch');
  return boundary0(verdict, ['CheckPublicTheoremEmissionPreflight0', 'boundary']);
}

function validateReleaseBlockerClearance0(clearance) {
  if (!plain0(clearance) || clearance.kind !== 'PNPReleaseBlockerClearance0' || clearance.coordinate !== EXPECTED_COORDINATES.releaseBlockerClearanceCoordinate || clearance.releaseBlockersStillActive !== true || clearance.releaseBlockerClearanceAccepted !== false || clearance.unrestrictedFinalSoundnessClearanceAccepted !== false || clearance.externalReviewClearanceAccepted !== false || clearance.publicTheoremEmissionAllowedByClearance !== false || clearance.finalTheoremReadyByClearance !== false) return reject0('PublicTheoremEmissionDenial.ReleaseBlockerClearanceMismatch', [FILES.releaseBlockerClearance], 'release blocker clearance mismatch or overclaim');
  return boundary0(clearance.claimBoundary, [FILES.releaseBlockerClearance, 'claimBoundary']);
}

function validateExternalReviewStatus0(external) {
  if (!plain0(external) || external.kind !== 'PNPExternalReviewStatus0' || external.coordinate !== EXPECTED_COORDINATES.externalReviewStatusCoordinate || external.externalReviewAcceptanceClaimed !== false || external.independentReviewAcceptanceConfirmed !== false || external.externalReviewBlockerStillActive !== true || external.publicTheoremEmissionAllowedByExternalReview !== false) return reject0('PublicTheoremEmissionDenial.ExternalReviewMismatch', [FILES.externalReviewStatus], 'external review status mismatch or overclaim');
  return boundary0(external.claimBoundary, [FILES.externalReviewStatus, 'claimBoundary']);
}

function validatePublicReviewBoundary0(boundaryManifest) {
  if (!plain0(boundaryManifest) || boundaryManifest.kind !== 'PNPPublicReviewBoundary0' || boundaryManifest.coordinate !== EXPECTED_COORDINATES.publicReviewBoundaryCoordinate || boundaryManifest.publicReviewBoundaryReady !== true || boundaryManifest.publicTheoremEmissionAllowedByBoundary !== false || boundaryManifest.finalTheoremReadyByBoundary !== false) return reject0('PublicTheoremEmissionDenial.PublicReviewBoundaryMismatch', [FILES.publicReviewBoundary], 'public review boundary mismatch or overclaim');
  return boundary0(boundaryManifest.claimBoundary, [FILES.publicReviewBoundary, 'claimBoundary']);
}

function validateDoc0(text, manifest) {
  for (const fragment of manifest.requiredDocFragments) if (!text.includes(fragment)) return reject0('PublicTheoremEmissionDenial.DocFragmentMissing', [FILES.denialDoc, fragment], 'denial doc required fragment missing');
  for (const reason of manifest.requiredDeniedReasons) if (!text.includes(reason)) return reject0('PublicTheoremEmissionDenial.DocReasonMissing', [FILES.denialDoc, reason], 'denial doc required reason missing');
  for (const expected of Object.values(EXPECTED_COORDINATES)) if (!text.includes(expected)) return reject0('PublicTheoremEmissionDenial.DocCoordinateMissing', [FILES.denialDoc, expected], 'denial doc required coordinate missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionDenial.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionDenial.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicTheoremEmissionDenial.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicTheoremEmissionDenial.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicTheoremEmissionDenial.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicTheoremEmissionDenial.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionDenial.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-theorem-emission-denial0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public theorem-emission denial CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicTheoremEmissionDenial0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
