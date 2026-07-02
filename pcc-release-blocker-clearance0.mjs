#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckReleaseBlockerClearance0';
const VERSION = 0;
const COORD = 'PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01';
const OUT = 'artifacts/release-blocker-clearance/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COORDINATES = {
  releaseBlockerClearanceCoordinate: COORD,
  externalReviewStatusCoordinate: 'PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01',
  publicReviewChecklistCoordinate: 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01',
  publicReviewEntrypointCoordinate: 'PNP-PUBLIC-REVIEW-ENTRYPOINT-2026-06-27-01',
  publicReviewHandoffCoordinate: 'PNP-PUBLIC-REVIEW-HANDOFF-2026-06-27-01',
  publicReviewBoundaryCoordinate: 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01',
  proofObligationLedgerCoordinate: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const FILES = {
  manifest: 'release/RELEASE_BLOCKER_CLEARANCE.json',
  status: 'PNP_STATUS.json',
  releaseLadder: 'release/RELEASE_LADDER.json',
  gapLedger: 'proof-obligations/GAP_LEDGER.json',
  proofObligationLedger: 'proof-obligations/OBLIGATION_LEDGER.json',
  externalReviewStatus: 'review/EXTERNAL_REVIEW_STATUS.json',
  publicReviewChecklist: 'review/PUBLIC_REVIEW_CHECKLIST.json',
  clearanceDoc: 'release/RELEASE_BLOCKER_CLEARANCE.md'
};

export async function CheckReleaseBlockerClearance0(options = {}) {
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

    const ladderRead = await readJson0(root, manifest.sourceFiles.releaseLadder, options.ladderOverride);
    if (ladderRead.tag === 'reject') return write0(root, outputPath, writeOutput, ladderRead);
    const ladderCheck = validateReleaseLadder0(ladderRead.value, manifest);
    if (ladderCheck.tag === 'reject') return write0(root, outputPath, writeOutput, ladderCheck);

    const gapsRead = await readJson0(root, manifest.sourceFiles.gapLedger, options.gapLedgerOverride);
    if (gapsRead.tag === 'reject') return write0(root, outputPath, writeOutput, gapsRead);
    const gapsCheck = validateGapLedger0(gapsRead.value, manifest);
    if (gapsCheck.tag === 'reject') return write0(root, outputPath, writeOutput, gapsCheck);

    const obligationsRead = await readJson0(root, manifest.sourceFiles.proofObligationLedger, options.obligationOverride);
    if (obligationsRead.tag === 'reject') return write0(root, outputPath, writeOutput, obligationsRead);
    const obligationsCheck = validateObligations0(obligationsRead.value, manifest);
    if (obligationsCheck.tag === 'reject') return write0(root, outputPath, writeOutput, obligationsCheck);

    const externalRead = await readJson0(root, manifest.sourceFiles.externalReviewStatus, options.externalReviewOverride);
    if (externalRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalRead);
    const externalCheck = validateExternalReview0(externalRead.value);
    if (externalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalCheck);

    const checklistRead = await readJson0(root, manifest.sourceFiles.publicReviewChecklist, options.checklistOverride);
    if (checklistRead.tag === 'reject') return write0(root, outputPath, writeOutput, checklistRead);
    const checklistCheck = validateChecklist0(checklistRead.value);
    if (checklistCheck.tag === 'reject') return write0(root, outputPath, writeOutput, checklistCheck);

    const docRead = await readText0(root, manifest.sourceFiles.clearanceDoc);
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
      claimStatus: 'release-blocker-clearance-protocol-accepted-non-clearing',
      clearanceProtocolReady: true,
      releaseBlockersStillActive: true,
      releaseBlockerClearanceAccepted: false,
      unrestrictedFinalSoundnessClearanceAccepted: false,
      externalReviewClearanceAccepted: false,
      publicTheoremEmissionAllowedByClearance: false,
      finalTheoremReadyByClearance: false,
      blockedTransitionOnly: true,
      clearanceTransitionRequiresFuturePR: true,
      requiredBlockers: [...BLOCKERS],
      requiredBlockedLadderNodeCount: manifest.requiredBlockedLadderNodes.length,
      requiredReleaseGapCount: manifest.requiredReleaseGaps.length,
      requiredProofObligationCount: manifest.requiredProofObligations.length,
      clearanceRuleCount: manifest.clearanceRules.length,
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
    return write0(root, outputPath, writeOutput, reject0('ReleaseBlockerClearance.UnhandledException', [], 'release blocker clearance checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPReleaseBlockerClearance0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'release-blocker-clearance-protocol-ready') return reject0('ReleaseBlockerClearance.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    clearanceProtocolReady: true,
    releaseBlockersStillActive: true,
    releaseBlockerClearanceAccepted: false,
    unrestrictedFinalSoundnessClearanceAccepted: false,
    externalReviewClearanceAccepted: false,
    publicTheoremEmissionAllowedByClearance: false,
    finalTheoremReadyByClearance: false,
    blockedTransitionOnly: true,
    clearanceTransitionRequiresFuturePR: true
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('ReleaseBlockerClearance.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!sameArray0(m.requiredBlockers, BLOCKERS)) return reject0('ReleaseBlockerClearance.RequiredBlockers', [FILES.manifest, 'requiredBlockers'], 'required blockers mismatch', { expected: BLOCKERS, actual: m.requiredBlockers });
  if (!plain0(m.sourceFiles)) return reject0('ReleaseBlockerClearance.SourceFilesShape', [FILES.manifest, 'sourceFiles'], 'sourceFiles must be object');
  for (const [field, expected] of Object.entries(FILES)) if (field !== 'manifest' && m.sourceFiles[field] !== expected) return reject0('ReleaseBlockerClearance.SourceFileMismatch', [FILES.manifest, 'sourceFiles', field], 'source file path mismatch', { expected, actual: m.sourceFiles[field] });
  if (!plain0(m.requiredCoordinates)) return reject0('ReleaseBlockerClearance.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('ReleaseBlockerClearance.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredBlockedLadderNodes', 'requiredReleaseGaps', 'requiredProofObligations', 'clearanceRules', 'requiredStatusVerificationSurfaceIds', 'requiredDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0) return reject0('ReleaseBlockerClearance.ArrayMissing', [FILES.manifest, field], 'required manifest array missing');
  for (const rule of m.clearanceRules) {
    if (!plain0(rule) || !BLOCKERS.includes(rule.blocker) || rule.currentState !== 'not-cleared' || rule.mayClearNow !== false || rule.mustRemoveFromRemainingBlockersOnlyAfterAcceptedTransition !== true) return reject0('ReleaseBlockerClearance.RuleShape', [FILES.manifest, 'clearanceRules'], 'clearance rule mismatch or overclaim', { rule });
  }
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('ReleaseBlockerClearance.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  for (const [field, expected] of Object.entries(EXPECTED_COORDINATES)) if (status[field] !== expected) return reject0('ReleaseBlockerClearance.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredStatusVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('ReleaseBlockerClearance.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  if (!Array.isArray(status.nonClaims) || !status.nonClaims.some((line) => line.includes('does not clear Release.UnrestrictedFinalSoundness or ExternalReview.Acceptance'))) return reject0('ReleaseBlockerClearance.StatusNonClaimMissing', [FILES.status, 'nonClaims'], 'status release-blocker non-claim missing');
  return { tag: 'accept' };
}

function validateReleaseLadder0(ladder, manifest) {
  if (!plain0(ladder) || ladder.kind !== 'PNPReleaseLadder0' || ladder.coordinate !== EXPECTED_COORDINATES.releaseLadderCoordinate || ladder.releaseLadderReady !== true || ladder.publicTheoremEmissionAllowedByLadder !== false || ladder.finalTheoremReadyByLadder !== false || !sameArray0(ladder.activeFinalNodeIdsByLadder, [])) return reject0('ReleaseBlockerClearance.ReleaseLadderShape', [FILES.releaseLadder], 'release ladder mismatch or overclaim');
  const boundary = boundary0(ladder.claimBoundary, [FILES.releaseLadder, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const required of manifest.requiredBlockedLadderNodes) {
    const row = ladder.ladder?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.state !== required.state || row.blocker !== required.blocker) return reject0('ReleaseBlockerClearance.ReleaseNodeMismatch', [FILES.releaseLadder, required.id], 'required release ladder node mismatch', { expected: required, actual: row ?? null });
  }
  if (!Array.isArray(ladder.transitionRules) || !ladder.transitionRules.some((x) => x.includes('No blocked status may be treated as complete'))) return reject0('ReleaseBlockerClearance.ReleaseTransitionRuleMissing', [FILES.releaseLadder, 'transitionRules'], 'release transition rule missing');
  return { tag: 'accept' };
}

function validateGapLedger0(gaps, manifest) {
  if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0' || gaps.coordinate !== EXPECTED_COORDINATES.gapLedgerCoordinate || gaps.fullGapClosureProved !== false || gaps.publicTheoremEmissionAllowedByLedger !== false) return reject0('ReleaseBlockerClearance.GapLedgerShape', [FILES.gapLedger], 'gap ledger mismatch or overclaim');
  const boundary = boundary0(gaps.claimBoundary, [FILES.gapLedger, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const required of manifest.requiredReleaseGaps) {
    const row = gaps.gaps?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.status !== required.status || row.severity !== required.severity || row.blocker !== required.blocker || row.publicTheoremEmissionAllowedByGap !== false || typeof row.closeCondition !== 'string' || row.closeCondition.length === 0) return reject0('ReleaseBlockerClearance.GapMismatch', [FILES.gapLedger, required.id], 'required release gap mismatch', { expected: required, actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateObligations0(ledger, manifest) {
  if (!plain0(ledger) || ledger.kind !== 'PNPProofObligationLedger0' || ledger.coordinate !== EXPECTED_COORDINATES.proofObligationLedgerCoordinate || ledger.fullProofObligationDischargeProved !== false || ledger.publicTheoremEmissionAllowedByLedger !== false) return reject0('ReleaseBlockerClearance.ObligationLedgerShape', [FILES.proofObligationLedger], 'proof obligation ledger mismatch or overclaim');
  const boundary = boundary0(ledger.claimBoundary, [FILES.proofObligationLedger, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const required of manifest.requiredProofObligations) {
    const row = ledger.obligations?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.status !== required.status) return reject0('ReleaseBlockerClearance.ObligationMismatch', [FILES.proofObligationLedger, required.id], 'required proof obligation mismatch', { expected: required, actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateExternalReview0(external) {
  if (!plain0(external) || external.kind !== 'PNPExternalReviewStatus0' || external.coordinate !== EXPECTED_COORDINATES.externalReviewStatusCoordinate || external.externalReviewAcceptanceClaimed !== false || external.independentReviewAcceptanceConfirmed !== false || external.externalReviewBlockerStillActive !== true || external.publicTheoremEmissionAllowedByExternalReview !== false) return reject0('ReleaseBlockerClearance.ExternalReviewMismatch', [FILES.externalReviewStatus], 'external review status mismatch or overclaim');
  return boundary0(external.claimBoundary, [FILES.externalReviewStatus, 'claimBoundary']);
}

function validateChecklist0(checklist) {
  if (!plain0(checklist) || checklist.kind !== 'PNPPublicReviewChecklist0' || checklist.coordinate !== EXPECTED_COORDINATES.publicReviewChecklistCoordinate || checklist.publicReviewChecklistReady !== true || checklist.reviewAcceptanceClaimed !== false || checklist.directTheoremEmissionAllowedByChecklist !== false || checklist.externalReviewStatusBound !== true) return reject0('ReleaseBlockerClearance.ChecklistMismatch', [FILES.publicReviewChecklist], 'public review checklist mismatch or overclaim');
  const boundary = boundary0(checklist.claimBoundary, [FILES.publicReviewChecklist, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  const ids = new Set((checklist.checklistItems ?? []).map((x) => x.id));
  for (const id of ['CHK-005-external-review-status', 'CHK-011-release-ladder', 'CHK-012-gap-ledger']) if (!ids.has(id)) return reject0('ReleaseBlockerClearance.ChecklistItemMissing', [FILES.publicReviewChecklist, 'checklistItems'], 'required checklist item missing', { id });
  return { tag: 'accept' };
}

function validateDoc0(text, manifest) {
  for (const fragment of manifest.requiredDocFragments) if (!text.includes(fragment)) return reject0('ReleaseBlockerClearance.DocFragmentMissing', [FILES.clearanceDoc, fragment], 'clearance doc required fragment missing');
  for (const blocker of BLOCKERS) if (!text.includes(blocker)) return reject0('ReleaseBlockerClearance.DocBlockerMissing', [FILES.clearanceDoc, blocker], 'clearance doc blocker missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('ReleaseBlockerClearance.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('ReleaseBlockerClearance.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('ReleaseBlockerClearance.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('ReleaseBlockerClearance.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('ReleaseBlockerClearance.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('ReleaseBlockerClearance.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('ReleaseBlockerClearance.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-release-blocker-clearance0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad release blocker clearance CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckReleaseBlockerClearance0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
