#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckPublicReviewHandoff0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-REVIEW-HANDOFF-2026-06-27-01';
const OUT = 'artifacts/public-review-handoff/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_COORDINATES = {
  publicReviewBoundaryCoordinate: 'PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01',
  publicSurfaceBaseline: 'PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01',
  historicalReportSupersessionCoordinate: 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01',
  historicalReportSanitizedCoordinate: 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01',
  historicalTheoremAnchorsCoordinate: 'PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01',
  directBindingIndexCoordinate: 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01',
  section22DirectBindingRunnerCoordinate: 'PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const FILES = {
  manifest: 'release/PUBLIC_REVIEW_HANDOFF.json',
  handoffDoc: 'release/PUBLIC_REVIEW_HANDOFF.md',
  boundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  status: 'PNP_STATUS.json'
};

export async function CheckPublicReviewHandoff0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? FILES.manifest, options.manifestOverride);
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifest = manifestRead.value;
    const manifestCheck = validateManifest0(manifest);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const statusRead = await readJson0(root, FILES.status, options.statusOverride);
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const statusCheck = validateStatus0(statusRead.value, manifest);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const boundaryRead = await readJson0(root, FILES.boundary, options.boundaryOverride);
    if (boundaryRead.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryRead);
    const boundaryCheck = validateBoundary0(boundaryRead.value);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const docRead = await readText0(root, FILES.handoffDoc);
    if (docRead.tag === 'reject') return write0(root, outputPath, writeOutput, docRead);
    const docCheck = validateHandoffDoc0(docRead.text, manifest);
    if (docCheck.tag === 'reject') return write0(root, outputPath, writeOutput, docCheck);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-review-handoff-accepted-non-activating',
      publicReviewHandoffReady: true,
      handoffDocReady: true,
      publicReviewBoundaryBound: true,
      oneCommandVerifierBound: true,
      historicalReportSanitized: true,
      publicSurfaceBaselineBound: true,
      section22DirectBindingSurfacesBound: true,
      directTheoremEmissionAllowedByHandoff: false,
      requiredCommandCount: manifest.requiredCommands.length,
      requiredVerificationSurfaceCount: manifest.requiredVerificationSurfaceIds.length,
      requiredCoordinates: { ...REQUIRED_COORDINATES },
      handoffDocSha256: shaBytes0(docRead.bytes),
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
    return write0(root, outputPath, writeOutput, reject0('PublicReviewHandoff.UnhandledException', [], 'public review handoff checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicReviewHandoff0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-review-handoff-ready') return reject0('PublicReviewHandoff.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    publicReviewHandoffReady: true,
    handoffDocReady: true,
    publicReviewBoundaryBound: true,
    oneCommandVerifierBound: true,
    historicalReportSanitized: true,
    publicSurfaceBaselineBound: true,
    section22DirectBindingSurfacesBound: true,
    directTheoremEmissionAllowedByHandoff: false
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicReviewHandoff.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.requiredCoordinates)) return reject0('PublicReviewHandoff.RequiredCoordinateShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) if (m.requiredCoordinates[field] !== expected) return reject0('PublicReviewHandoff.RequiredCoordinateMismatch', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCoordinates[field] });
  for (const field of ['requiredCommands', 'requiredVerificationSurfaceIds', 'requiredHandoffDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('PublicReviewHandoff.ArrayMissing', [FILES.manifest, field], 'manifest string array missing or invalid');
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicReviewHandoff.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  if (status.pnpVerifyCommand !== 'npm run pnp:verify') return reject0('PublicReviewHandoff.StatusVerifyCommand', [FILES.status, 'pnpVerifyCommand'], 'status pnp verify command mismatch', { actual: status.pnpVerifyCommand });
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) if (status[field] !== expected) return reject0('PublicReviewHandoff.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicReviewHandoff.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required verification surface missing from status', { id });
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary) || boundary.kind !== 'PNPPublicReviewBoundary0' || boundary.coordinate !== REQUIRED_COORDINATES.publicReviewBoundaryCoordinate || boundary.publicReviewBoundaryReady !== true || boundary.publicTheoremEmissionAllowedByBoundary !== false || boundary.finalTheoremReadyByBoundary !== false) return reject0('PublicReviewHandoff.BoundaryShape', [FILES.boundary], 'public review boundary shape mismatch or overclaim');
  return boundary0(boundary.claimBoundary, [FILES.boundary, 'claimBoundary']);
}

function validateHandoffDoc0(text, manifest) {
  for (const fragment of manifest.requiredHandoffDocFragments) if (!text.includes(fragment)) return reject0('PublicReviewHandoff.DocFragmentMissing', [FILES.handoffDoc, fragment], 'handoff doc required fragment missing');
  for (const command of manifest.requiredCommands) if (!text.includes(command)) return reject0('PublicReviewHandoff.DocCommandMissing', [FILES.handoffDoc, command], 'handoff doc required command missing');
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) if (!text.includes(expected)) return reject0('PublicReviewHandoff.DocCoordinateMissing', [FILES.handoffDoc, field], 'handoff doc required coordinate missing', { expected });
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicReviewHandoff.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('PublicReviewHandoff.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicReviewHandoff.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicReviewHandoff.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicReviewHandoff.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicReviewHandoff.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicReviewHandoff.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-review-handoff0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public review handoff CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicReviewHandoff0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
