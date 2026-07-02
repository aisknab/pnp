#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckExternalReviewStatus0';
const VERSION = 0;
const COORD = 'PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01';
const OUT = 'artifacts/external-review-status/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  publicReviewChecklistCoordinate: 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01',
  publicReviewEntrypointCoordinate: 'PNP-PUBLIC-REVIEW-ENTRYPOINT-2026-06-27-01',
  publicReviewHandoffCoordinate: 'PNP-PUBLIC-REVIEW-HANDOFF-2026-06-27-01',
  publicReviewBoundaryCoordinate: 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const FILES = {
  manifest: 'review/EXTERNAL_REVIEW_STATUS.json',
  externalReviewStatus: 'EXTERNAL_REVIEW_STATUS.md',
  externalReviewManifestDoc: 'review/EXTERNAL_REVIEW_STATUS.md',
  status: 'PNP_STATUS.json',
  checklist: 'review/PUBLIC_REVIEW_CHECKLIST.json',
  ladder: 'release/RELEASE_LADDER.json',
  gaps: 'proof-obligations/GAP_LEDGER.json'
};

export async function CheckExternalReviewStatus0(options = {}) {
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

    const checklistRead = await readJson0(root, manifest.sourceFiles.checklist, options.checklistOverride);
    if (checklistRead.tag === 'reject') return write0(root, outputPath, writeOutput, checklistRead);
    const checklistCheck = validateChecklist0(checklistRead.value, manifest);
    if (checklistCheck.tag === 'reject') return write0(root, outputPath, writeOutput, checklistCheck);

    const ladderRead = await readJson0(root, manifest.sourceFiles.releaseLadder, options.ladderOverride);
    if (ladderRead.tag === 'reject') return write0(root, outputPath, writeOutput, ladderRead);
    const ladderCheck = validateReleaseLadder0(ladderRead.value, manifest.requiredReleaseLadderNode);
    if (ladderCheck.tag === 'reject') return write0(root, outputPath, writeOutput, ladderCheck);

    const gapRead = await readJson0(root, manifest.sourceFiles.gapLedger, options.gapLedgerOverride);
    if (gapRead.tag === 'reject') return write0(root, outputPath, writeOutput, gapRead);
    const gapCheck = validateGapLedger0(gapRead.value, manifest.requiredGap);
    if (gapCheck.tag === 'reject') return write0(root, outputPath, writeOutput, gapCheck);

    const externalTextRead = await readText0(root, manifest.sourceFiles.externalReviewStatus);
    if (externalTextRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalTextRead);
    const externalTextCheck = validateExternalReviewText0(externalTextRead.text, manifest.requiredExternalReviewDocFragments);
    if (externalTextCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalTextCheck);

    const manifestDocRead = await readText0(root, manifest.sourceFiles.externalReviewManifestDoc);
    if (manifestDocRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestDocRead);
    const manifestDocCheck = validateManifestDoc0(manifestDocRead.text, manifest.requiredManifestDocFragments);
    if (manifestDocCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestDocCheck);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'external-review-status-accepted-non-activating',
      externalReviewStatusReady: true,
      externalReviewAcceptanceClaimed: false,
      independentReviewAcceptanceConfirmed: false,
      noIndependentReviewerConfirmed: true,
      externalReviewBlockerStillActive: true,
      substantiveFeedbackRecorded: true,
      substantiveFeedbackIsAcceptance: false,
      publicTheoremEmissionAllowedByExternalReview: false,
      releaseLadderNode: manifest.requiredReleaseLadderNode,
      releaseGap: manifest.requiredGap,
      requiredCoordinates: { ...EXPECTED_COORDINATES },
      externalReviewStatusSha256: shaBytes0(externalTextRead.bytes),
      externalReviewManifestDocSha256: shaBytes0(manifestDocRead.bytes),
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
    return write0(root, outputPath, writeOutput, reject0('ExternalReviewStatus.UnhandledException', [], 'external review status checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPExternalReviewStatus0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'external-review-not-accepted') return reject0('ExternalReviewStatus.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    externalReviewStatusReady: true,
    externalReviewAcceptanceClaimed: false,
    independentReviewAcceptanceConfirmed: false,
    noIndependentReviewerConfirmed: true,
    externalReviewBlockerStillActive: true,
    substantiveFeedbackRecorded: true,
    substantiveFeedbackIsAcceptance: false,
    publicTheoremEmissionAllowedByExternalReview: false
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('ExternalReviewStatus.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.sourceFiles)) return reject0('ExternalReviewStatus.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [key, expectedPath] of Object.entries(FILES)) {
    if (key === 'manifest') continue;
    const fieldName = key === 'ladder' ? 'releaseLadder' : key === 'gaps' ? 'gapLedger' : key;
    if (m.sourceFiles[fieldName] !== expectedPath) return reject0('ExternalReviewStatus.SourceFileMismatch', [FILES.manifest, 'sourceFiles', fieldName], 'source file path mismatch', { expected: expectedPath, actual: m.sourceFiles[fieldName] });
  }
  if (!plain0(m.requiredCoordinates)) return reject0('ExternalReviewStatus.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('ExternalReviewStatus.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredExternalReviewDocFragments', 'requiredManifestDocFragments', 'requiredChecklistItemIds', 'requiredStatusVerificationSurfaceIds', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('ExternalReviewStatus.ArrayMissing', [FILES.manifest, field], 'manifest string array missing or invalid');
  if (!plain0(m.requiredReleaseLadderNode) || m.requiredReleaseLadderNode.id !== 'PublicTheoremEmissionCandidate' || m.requiredReleaseLadderNode.state !== 'blocked' || m.requiredReleaseLadderNode.blocker !== 'ExternalReview.Acceptance') return reject0('ExternalReviewStatus.RequiredReleaseNode', [FILES.manifest, 'requiredReleaseLadderNode'], 'required release ladder node mismatch');
  if (!plain0(m.requiredGap) || m.requiredGap.id !== 'GAP-002-ExternalReviewAcceptance' || m.requiredGap.status !== 'blocked-release-gap' || m.requiredGap.severity !== 'activation-blocking' || m.requiredGap.blocker !== 'ExternalReview.Acceptance') return reject0('ExternalReviewStatus.RequiredGap', [FILES.manifest, 'requiredGap'], 'required gap mismatch');
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('ExternalReviewStatus.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('ExternalReviewStatus.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('ExternalReviewStatus.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required verification surface missing from status', { id });
  if (!Array.isArray(status.nonClaims) || !status.nonClaims.some((line) => line.includes('does not activate public theorem emission'))) return reject0('ExternalReviewStatus.StatusNonClaimMissing', [FILES.status, 'nonClaims'], 'status non-claim missing');
  return { tag: 'accept' };
}

function validateChecklist0(checklist, manifest) {
  const expected = EXPECTED_COORDINATES.publicReviewChecklistCoordinate;
  if (!plain0(checklist) || checklist.kind !== 'PNPPublicReviewChecklist0' || checklist.coordinate !== expected || checklist.publicReviewChecklistReady !== true || checklist.externalReviewStatusBound !== true || checklist.reviewAcceptanceClaimed !== false || checklist.directTheoremEmissionAllowedByChecklist !== false) return reject0('ExternalReviewStatus.ChecklistShape', [FILES.checklist], 'public review checklist mismatch or overclaim');
  const boundary = boundary0(checklist.claimBoundary, [FILES.checklist, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  const ids = new Set((checklist.checklistItems ?? []).map((x) => x.id));
  for (const id of manifest.requiredChecklistItemIds) if (!ids.has(id)) return reject0('ExternalReviewStatus.ChecklistItemMissing', [FILES.checklist, 'checklistItems'], 'required checklist item missing', { id });
  return { tag: 'accept' };
}

function validateReleaseLadder0(ladder, requiredNode) {
  if (!plain0(ladder) || ladder.kind !== 'PNPReleaseLadder0' || ladder.coordinate !== EXPECTED_COORDINATES.releaseLadderCoordinate || ladder.publicTheoremEmissionAllowedByLadder !== false || ladder.finalTheoremReadyByLadder !== false) return reject0('ExternalReviewStatus.ReleaseLadderShape', [FILES.ladder], 'release ladder mismatch or overclaim');
  const boundary = boundary0(ladder.claimBoundary, [FILES.ladder, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  const node = ladder.ladder?.find?.((x) => x.id === requiredNode.id);
  if (!plain0(node) || node.state !== requiredNode.state || node.blocker !== requiredNode.blocker) return reject0('ExternalReviewStatus.ReleaseLadderNodeMismatch', [FILES.ladder, requiredNode.id], 'release ladder external-review node mismatch', { expected: requiredNode, actual: node ?? null });
  return { tag: 'accept' };
}

function validateGapLedger0(gaps, requiredGap) {
  if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0' || gaps.coordinate !== EXPECTED_COORDINATES.gapLedgerCoordinate || gaps.publicTheoremEmissionAllowedByLedger !== false || gaps.fullGapClosureProved !== false) return reject0('ExternalReviewStatus.GapLedgerShape', [FILES.gaps], 'gap ledger mismatch or overclaim');
  const boundary = boundary0(gaps.claimBoundary, [FILES.gaps, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  const gap = gaps.gaps?.find?.((x) => x.id === requiredGap.id);
  if (!plain0(gap) || gap.status !== requiredGap.status || gap.severity !== requiredGap.severity || gap.blocker !== requiredGap.blocker || gap.publicTheoremEmissionAllowedByGap !== false) return reject0('ExternalReviewStatus.GapMismatch', [FILES.gaps, requiredGap.id], 'external review gap mismatch', { expected: requiredGap, actual: gap ?? null });
  return { tag: 'accept' };
}

function validateExternalReviewText0(text, requiredFragments) {
  for (const fragment of requiredFragments) if (!text.includes(fragment)) return reject0('ExternalReviewStatus.ExternalTextFragmentMissing', [FILES.externalReviewStatus, fragment], 'external review status required fragment missing');
  for (const forbidden of ['independently confirmed theorem correctness', 'formally accepted the claimed result', 'ExternalReview.Acceptance cleared']) if (text.includes(forbidden)) return reject0('ExternalReviewStatus.ExternalTextOverclaim', [FILES.externalReviewStatus, forbidden], 'external review status contains forbidden acceptance-like fragment');
  return { tag: 'accept' };
}

function validateManifestDoc0(text, requiredFragments) {
  for (const fragment of requiredFragments) if (!text.includes(fragment)) return reject0('ExternalReviewStatus.ManifestDocFragmentMissing', [FILES.externalReviewManifestDoc, fragment], 'external review manifest doc required fragment missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('ExternalReviewStatus.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('ExternalReviewStatus.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('ExternalReviewStatus.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('ExternalReviewStatus.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('ExternalReviewStatus.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('ExternalReviewStatus.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('ExternalReviewStatus.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-external-review-status0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad external review status CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckExternalReviewStatus0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
