#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckPublicSurfaceBaseline0 } from './pcc-public-surface-baseline0.mjs';

const CHECKER = 'CheckPublicReviewBoundary0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01';
const OUT = 'artifacts/public-review-boundary/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_COORDINATES = {
  statusKind: 'PNPStatus0',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01',
  historicalReportSupersessionCoordinate: 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01',
  historicalReportSanitizedCoordinate: 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01',
  historicalTheoremAnchorsCoordinate: 'PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01',
  publicSurfaceBaseline: 'PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01',
  directBindingIndexCoordinate: 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01',
  section22DirectBindingRunnerCoordinate: 'PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01'
};
const FILES = {
  manifest: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  status: 'PNP_STATUS.json',
  ladder: 'release/RELEASE_LADDER.json',
  gaps: 'proof-obligations/GAP_LEDGER.json',
  supersession: 'report-bindings/HISTORICAL_REPORT_SUPERSESSION.json',
  anchors: 'report-bindings/HISTORICAL_THEOREM_ANCHORS.json'
};

export async function CheckPublicReviewBoundary0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const reads = {};
    for (const [key, rel] of Object.entries(FILES)) {
      const read = await readJson0(root, options[`${key}Path`] ?? rel, options[`${key}Override`]);
      if (read.tag === 'reject') return write0(root, outputPath, writeOutput, read);
      reads[key] = read.value;
    }

    for (const check of [
      validateManifest0(reads.manifest),
      validateStatus0(reads.status, reads.manifest),
      validateReleaseLadder0(reads.ladder, reads.manifest),
      validateGapLedger0(reads.gaps, reads.manifest),
      validateSupersession0(reads.supersession),
      validateAnchors0(reads.anchors)
    ]) {
      if (check.tag === 'reject') return write0(root, outputPath, writeOutput, check);
    }

    const publicSurface = await CheckPublicSurfaceBaseline0({ root, writeOutput: false });
    const publicSurfaceCheck = validatePublicSurface0(publicSurface);
    if (publicSurfaceCheck.tag === 'reject') return write0(root, outputPath, writeOutput, publicSurfaceCheck);

    const evidence = await digestEvidence0(root, reads.manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-review-boundary-accepted-non-activating',
      publicReviewBoundaryReady: true,
      publicTheoremEmissionAllowedByBoundary: false,
      finalTheoremReadyByBoundary: false,
      publicSurfaceBaselineFrozen: true,
      historicalReportSanitized: true,
      historicalTheoremAnchorsNonEmitting: true,
      releaseLadderBlocked: true,
      gapLedgerBlocksPublicEmission: true,
      section22ExecutableSurfaceIndexed: true,
      section22RunnerBound: true,
      requiredCoordinates: { ...REQUIRED_COORDINATES },
      blockedReleaseNodes: reads.manifest.requiredBlockedLadderNodes,
      releaseGapIds: reads.manifest.requiredReleaseGaps,
      publicSurfaceBaselineDigest: publicSurface.evidenceDigestSha256 ?? null,
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
    return write0(root, outputPath, writeOutput, reject0('PublicReviewBoundary.UnhandledException', [], 'public review boundary checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicReviewBoundary0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-review-boundary-ready') return reject0('PublicReviewBoundary.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    publicReviewBoundaryReady: true,
    publicTheoremEmissionAllowedByBoundary: false,
    finalTheoremReadyByBoundary: false,
    publicSurfaceBaselineFrozen: true,
    historicalReportSanitized: true,
    historicalTheoremAnchorsNonEmitting: true,
    releaseLadderBlocked: true,
    gapLedgerBlocksPublicEmission: true,
    section22ExecutableSurfaceIndexed: true,
    section22RunnerBound: true
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicReviewBoundary.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const b = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  if (!plain0(m.requiredCoordinates)) return reject0('PublicReviewBoundary.RequiredCoordinatesShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicReviewBoundary.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredBlockedLadderNodes', 'requiredReleaseGaps', 'requiredVerificationSurfaceIds', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0) return reject0('PublicReviewBoundary.ArrayMissing', [FILES.manifest, field], 'manifest array missing');
  return { tag: 'accept' };
}

function validateStatus0(s, manifest) {
  if (!plain0(s) || s.kind !== REQUIRED_COORDINATES.statusKind || s.project !== 'PNP') return reject0('PublicReviewBoundary.StatusShape', [FILES.status], 'status shape mismatch');
  const b = boundary0(s, [FILES.status]);
  if (b.tag === 'reject') return b;
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) {
    if (field === 'statusKind') continue;
    if (s[field] !== expected) return reject0('PublicReviewBoundary.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: s[field] });
  }
  const surfaceIds = new Set((s.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicReviewBoundary.StatusVerificationSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required status verification surface missing', { id });
  return { tag: 'accept' };
}

function validateReleaseLadder0(ladder, manifest) {
  if (!plain0(ladder) || ladder.kind !== 'PNPReleaseLadder0' || ladder.coordinate !== REQUIRED_COORDINATES.releaseLadderCoordinate || ladder.releaseLadderReady !== true || ladder.publicTheoremEmissionAllowedByLadder !== false || ladder.finalTheoremReadyByLadder !== false || !sameArray0(ladder.activeFinalNodeIdsByLadder, [])) return reject0('PublicReviewBoundary.ReleaseLadderShape', [FILES.ladder], 'release ladder shape mismatch or overclaim');
  const b = boundary0(ladder.claimBoundary, [FILES.ladder, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  for (const required of manifest.requiredBlockedLadderNodes) {
    const row = ladder.ladder?.find?.((x) => x.id === required.id);
    if (!plain0(row) || row.state !== 'blocked' || row.blocker !== required.blocker) return reject0('PublicReviewBoundary.ReleaseNodeNotBlocked', [FILES.ladder, required.id], 'required release ladder node is not blocked as expected', { required, actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateGapLedger0(gaps, manifest) {
  if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0' || gaps.coordinate !== REQUIRED_COORDINATES.gapLedgerCoordinate || gaps.fullGapClosureProved !== false || gaps.publicTheoremEmissionAllowedByLedger !== false) return reject0('PublicReviewBoundary.GapLedgerShape', [FILES.gaps], 'gap ledger shape mismatch or overclaim');
  const b = boundary0(gaps.claimBoundary, [FILES.gaps, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  for (const id of manifest.requiredReleaseGaps) {
    const row = gaps.gaps?.find?.((x) => x.id === id);
    if (!plain0(row) || row.status !== 'blocked-release-gap' || row.severity !== 'activation-blocking' || row.publicTheoremEmissionAllowedByGap !== false) return reject0('PublicReviewBoundary.ReleaseGapMismatch', [FILES.gaps, id], 'required release gap mismatch', { actual: row ?? null });
  }
  return { tag: 'accept' };
}

function validateSupersession0(s) {
  if (!plain0(s) || s.kind !== 'PNPHistoricalReportSupersession0' || s.coordinate !== REQUIRED_COORDINATES.historicalReportSupersessionCoordinate || s.sanitizedReportCoordinate !== REQUIRED_COORDINATES.historicalReportSanitizedCoordinate || s.historicalReportSanitizedReady !== true || s.historicalDirectTheoremEmissionSanitized !== true || s.publicTheoremEmissionAllowedBySupersession !== false) return reject0('PublicReviewBoundary.SupersessionMismatch', [FILES.supersession], 'historical report supersession mismatch or overclaim');
  return boundary0(s.claimBoundary, [FILES.supersession, 'claimBoundary']);
}

function validateAnchors0(a) {
  if (!plain0(a) || a.kind !== 'PNPHistoricalTheoremAnchors0' || a.coordinate !== REQUIRED_COORDINATES.historicalTheoremAnchorsCoordinate || a.anchorIndexReady !== true || a.anchorIndexIsTheoremEmissionSurface !== false || a.publicTheoremEmissionAllowedByAnchorIndex !== false) return reject0('PublicReviewBoundary.AnchorsMismatch', [FILES.anchors], 'historical theorem anchors mismatch or overclaim');
  return boundary0(a.claimBoundary, [FILES.anchors, 'claimBoundary']);
}

function validatePublicSurface0(surface) {
  if (!plain0(surface) || surface.tag !== 'accept' || surface.coordinate !== REQUIRED_COORDINATES.publicSurfaceBaseline || surface.publicSurfaceBaselineReady !== true || surface.publicEntryReleaseSurfaceAccepted !== true || surface.publicSurfaceFrozen !== true || surface.publicTheoremEmissionAllowed !== false || surface.finalTheoremReady !== false) return reject0('PublicReviewBoundary.PublicSurfaceBaselineMismatch', ['CheckPublicSurfaceBaseline0'], 'public surface baseline checker mismatch or overclaim', { actualTag: surface?.tag ?? null, actualCoordinate: surface?.coordinate ?? null });
  return boundary0(surface, ['CheckPublicSurfaceBaseline0', 'boundary']);
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicReviewBoundary.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicReviewBoundary.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicReviewBoundary.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicReviewBoundary.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicReviewBoundary.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicReviewBoundary.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-review-boundary0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public review boundary CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicReviewBoundary0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
