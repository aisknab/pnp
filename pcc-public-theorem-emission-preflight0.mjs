#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckPublicTheoremEmissionPreflight0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01';
const OUT = 'artifacts/public-theorem-emission-preflight/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  releaseBlockerClearanceCoordinate: 'PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01',
  externalReviewStatusCoordinate: 'PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01',
  publicReviewChecklistCoordinate: 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01',
  publicReviewBoundaryCoordinate: 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01',
  proofObligationLedgerCoordinate: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const FILES = {
  manifest: 'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  status: 'PNP_STATUS.json',
  publicReviewBoundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  releaseBlockerClearance: 'release/RELEASE_BLOCKER_CLEARANCE.json',
  externalReviewStatus: 'review/EXTERNAL_REVIEW_STATUS.json',
  releaseLadder: 'release/RELEASE_LADDER.json',
  gapLedger: 'proof-obligations/GAP_LEDGER.json',
  proofObligationLedger: 'proof-obligations/OBLIGATION_LEDGER.json',
  preflightDoc: 'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.md'
};

export async function CheckPublicTheoremEmissionPreflight0(options = {}) {
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

    const boundaryRead = await readJson0(root, manifest.sourceFiles.publicReviewBoundary, options.boundaryOverride);
    if (boundaryRead.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryRead);
    const boundaryCheck = validatePublicReviewBoundary0(boundaryRead.value);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const clearanceRead = await readJson0(root, manifest.sourceFiles.releaseBlockerClearance, options.clearanceOverride);
    if (clearanceRead.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceRead);
    const clearanceCheck = validateReleaseBlockerClearance0(clearanceRead.value);
    if (clearanceCheck.tag === 'reject') return write0(root, outputPath, writeOutput, clearanceCheck);

    const externalRead = await readJson0(root, manifest.sourceFiles.externalReviewStatus, options.externalReviewOverride);
    if (externalRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalRead);
    const externalCheck = validateExternalReviewStatus0(externalRead.value);
    if (externalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalCheck);

    const ladderRead = await readJson0(root, manifest.sourceFiles.releaseLadder, options.ladderOverride);
    if (ladderRead.tag === 'reject') return write0(root, outputPath, writeOutput, ladderRead);
    const ladderCheck = validateReleaseLadder0(ladderRead.value, manifest.requiredBlockedLadderNodes);
    if (ladderCheck.tag === 'reject') return write0(root, outputPath, writeOutput, ladderCheck);

    const gapsRead = await readJson0(root, manifest.sourceFiles.gapLedger, options.gapLedgerOverride);
    if (gapsRead.tag === 'reject') return write0(root, outputPath, writeOutput, gapsRead);
    const gapsCheck = validateGapLedger0(gapsRead.value, manifest.requiredReleaseGaps);
    if (gapsCheck.tag === 'reject') return write0(root, outputPath, writeOutput, gapsCheck);

    const obligationsRead = await readJson0(root, manifest.sourceFiles.proofObligationLedger, options.obligationOverride);
    if (obligationsRead.tag === 'reject') return write0(root, outputPath, writeOutput, obligationsRead);
    const obligationsCheck = validateObligations0(obligationsRead.value, manifest.requiredProofObligations);
    if (obligationsCheck.tag === 'reject') return write0(root, outputPath, writeOutput, obligationsCheck);

    const docRead = await readText0(root, manifest.sourceFiles.preflightDoc);
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
      claimStatus: 'public-theorem-emission-preflight-accepted-denied-non-activating',
      publicTheoremEmissionPreflightReady: true,
      publicTheoremEmissionPreflightPassed: false,
      publicTheoremEmissionDenied: true,
      finalTheoremReadyByPreflight: false,
      releaseBlockerClearanceAccepted: false,
      externalReviewAcceptanceClaimed: false,
      unrestrictedFinalSoundnessClearanceAccepted: false,
      publicReviewBoundaryNonActivating: true,
      blockedByRemainingBlockers: true,
      preflightTransitionRequiresFuturePR: true,
      deniedReasons: manifest.requiredDeniedReasons,
      requiredBlockedLadderNodeCount: manifest.requiredBlockedLadderNodes.length,
      requiredReleaseGapCount: manifest.requiredReleaseGaps.length,
      requiredProofObligationCount: manifest.requiredProofObligations.length,
      requiredCoordinates: { ...EXPECTED_COORDINATES },
      preflightDocSha256: shaBytes0(docRead.bytes),
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
    return write0(root, outputPath, writeOutput, reject0('PublicTheoremEmissionPreflight.UnhandledException', [], 'public theorem emission preflight checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicTheoremEmissionPreflight0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-theorem-emission-preflight-denied') return reject0('PublicTheoremEmissionPreflight.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    publicTheoremEmissionPreflightReady: true,
    publicTheoremEmissionPreflightPassed: false,
    publicTheoremEmissionDenied: true,
    finalTheoremReadyByPreflight: false,
    releaseBlockerClearanceAccepted: false,
    externalReviewAcceptanceClaimed: false,
    unrestrictedFinalSoundnessClearanceAccepted: false,
    publicReviewBoundaryNonActivating: true,
    blockedByRemainingBlockers: true,
    preflightTransitionRequiresFuturePR: true
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicTheoremEmissionPreflight.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.sourceFiles)) return reject0('PublicTheoremEmissionPreflight.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [field, expected] of Object.entries(FILES)) if (field !== 'manifest' && m.sourceFiles[field] !== expected) return reject0('PublicTheoremEmissionPreflight.SourceFileMismatch', [FILES.manifest, 'sourceFiles', field], 'source file path mismatch', { expected, actual: m.sourceFiles[field] });
  if (!plain0(m.requiredCoordinates)) return reject0('PublicTheoremEmissionPreflight.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicTheoremEmissionPreflight.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredStatusVerificationSurfaceIds', 'requiredDeniedReasons', 'requiredBlockedLadderNodes', 'requiredReleaseGaps', 'requiredProofObligations', 'requiredDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0) return reject0('PublicTheoremEmissionPreflight.ArrayMissing', [FILES.manifest, field], 'required manifest array missing');
  if (!sameArray0((m.requiredBlockers ?? BLOCKERS), BLOCKERS)) return reject0('PublicTheoremEmissionPreflight.RequiredBlockers', [FILES.manifest, 'requiredBlockers'], 'required blockers mismatch');
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicTheoremEmissionPreflight.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionPreflight.StatusOverclaim', [FILES.status], 'status is not theorem-emission-denied');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('PublicTheoremEmissionPreflight.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicTheoremEmissionPreflight.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  return { tag: 'accept' };
}

function validatePublicReviewBoundary0(boundaryManifest) {
  if (!plain0(boundaryManifest) || boundaryManifest.kind !== 'PNPPublicReviewBoundary0' || boundaryManifest.coordinate !== EXPECTED_COORDINATES.publicReviewBoundaryCoordinate || boundaryManifest.publicReviewBoundaryReady !== true || boundaryManifest.publicTheoremEmissionAllowedByBoundary !== false || boundaryManifest.finalTheoremReadyByBoundary !== false) return reject0('PublicTheoremEmissionPreflight.PublicReviewBoundaryMismatch', [FILES.publicReviewBoundary], 'public review boundary mismatch or overclaim');
  return boundary0(boundaryManifest.claimBoundary, [FILES.publicReviewBoundary, 'claimBoundary']);
}

function validateReleaseBlockerClearance0(clearance) {
  if (!plain0(clearance) || clearance.kind !== 'PNPReleaseBlockerClearance0' || clearance.coordinate !== EXPECTED_COORDINATES.releaseBlockerClearanceCoordinate || clearance.releaseBlockersStillActive !== true || clearance.releaseBlockerClearanceAccepted !== false || clearance.unrestrictedFinalSoundnessClearanceAccepted !== false || clearance.externalReviewClearanceAccepted !== false || clearance.publicTheoremEmissionAllowedByClearance !== false || clearance.finalTheoremReadyByClearance !== false) return reject0('PublicTheoremEmissionPreflight.ReleaseBlockerClearanceMismatch', [FILES.releaseBlockerClearance], 'release blocker clearance mismatch or overclaim');
  return boundary0(clearance.claimBoundary, [FILES.releaseBlockerClearance, 'claimBoundary']);
}

function validateExternalReviewStatus0(external) {
  if (!plain0(external) || external.kind !== 'PNPExternalReviewStatus0' || external.coordinate !== EXPECTED_COORDINATES.externalReviewStatusCoordinate || external.externalReviewAcceptanceClaimed !== false || external.independentReviewAcceptanceConfirmed !== false || external.externalReviewBlockerStillActive !== true || external.publicTheoremEmissionAllowedByExternalReview !== false) return reject0('PublicTheoremEmissionPreflight.ExternalReviewMismatch', [FILES.externalReviewStatus], 'external review status mismatch or overclaim');
  return boundary0(external.claimBoundary, [FILES.externalReviewStatus, 'claimBoundary']);
}

function validateReleaseLadder0(ladder, requiredNodes) {
  if (!plain0(ladder) || ladder.kind !== 'PNPReleaseLadder0' || ladder.coordinate !== EXPECTED_COORDINATES.releaseLadderCoordinate || ladder.releaseLadderReady !== true || ladder.publicTheoremEmissionAllowedByLadder !== false || ladder.finalTheoremReadyByLadder !== false || !sameArray0(ladder.activeFinalNodeIdsByLadder, [])) return reject0('PublicTheoremEmissionPreflight.ReleaseLadderMismatch', [FILES.releaseLadder], 'release ladder mismatch or overclaim');
  const boundary = boundary0(ladder.claimBoundary, [FILES.releaseLadder, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const required of requiredNodes) {
    const row = ladder.ladder?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.state !== required.state || row.blocker !== required.blocker) return reject0('PublicTheoremEmissionPreflight.ReleaseNodeMismatch', [FILES.releaseLadder, required.id], 'required release ladder node mismatch', { expected: required, actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateGapLedger0(gaps, requiredGaps) {
  if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0' || gaps.coordinate !== EXPECTED_COORDINATES.gapLedgerCoordinate || gaps.fullGapClosureProved !== false || gaps.publicTheoremEmissionAllowedByLedger !== false) return reject0('PublicTheoremEmissionPreflight.GapLedgerMismatch', [FILES.gapLedger], 'gap ledger mismatch or overclaim');
  const boundary = boundary0(gaps.claimBoundary, [FILES.gapLedger, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const required of requiredGaps) {
    const row = gaps.gaps?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.status !== required.status || row.severity !== required.severity || row.blocker !== required.blocker || row.publicTheoremEmissionAllowedByGap !== false) return reject0('PublicTheoremEmissionPreflight.GapMismatch', [FILES.gapLedger, required.id], 'required gap mismatch', { expected: required, actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateObligations0(ledger, requiredObligations) {
  if (!plain0(ledger) || ledger.kind !== 'PNPProofObligationLedger0' || ledger.coordinate !== EXPECTED_COORDINATES.proofObligationLedgerCoordinate || ledger.fullProofObligationDischargeProved !== false || ledger.publicTheoremEmissionAllowedByLedger !== false) return reject0('PublicTheoremEmissionPreflight.ProofObligationLedgerMismatch', [FILES.proofObligationLedger], 'proof obligation ledger mismatch or overclaim');
  const boundary = boundary0(ledger.claimBoundary, [FILES.proofObligationLedger, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const required of requiredObligations) {
    const row = ledger.obligations?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.status !== required.status) return reject0('PublicTheoremEmissionPreflight.ObligationMismatch', [FILES.proofObligationLedger, required.id], 'required proof obligation mismatch', { expected: required, actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateDoc0(text, manifest) {
  for (const fragment of manifest.requiredDocFragments) if (!text.includes(fragment)) return reject0('PublicTheoremEmissionPreflight.DocFragmentMissing', [FILES.preflightDoc, fragment], 'preflight doc required fragment missing');
  for (const reason of manifest.requiredDeniedReasons) if (!text.includes(reason)) return reject0('PublicTheoremEmissionPreflight.DocDeniedReasonMissing', [FILES.preflightDoc, reason], 'preflight doc denied reason missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionPreflight.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('PublicTheoremEmissionPreflight.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicTheoremEmissionPreflight.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicTheoremEmissionPreflight.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicTheoremEmissionPreflight.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicTheoremEmissionPreflight.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicTheoremEmissionPreflight.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-theorem-emission-preflight0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public theorem emission preflight CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicTheoremEmissionPreflight0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
