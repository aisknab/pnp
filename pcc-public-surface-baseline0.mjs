#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  CheckPublicEntryReleaseSurface0,
  PUBLIC_SURFACE_BASELINE0,
} from './pcc-public-surface-freeze0.mjs';

const CHECKER = 'CheckPublicSurfaceBaseline0';
const VERSION = 0;
const COORD = 'PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01';
const OUT = 'artifacts/public-surface-baseline/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EVIDENCE = [
  'pcc-public-surface-baseline0.mjs',
  'pcc-public-surface-freeze0.mjs',
  'test/pcc-public-surface-freeze0.test.mjs',
  'audits/public-surface-baseline0.test.mjs',
  'index.mjs',
  'package.json',
  'PNP_STATUS.json'
];

export async function CheckPublicSurfaceBaseline0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const statusRead = await readJson0(root, options.statusPath ?? 'PNP_STATUS.json', options.statusOverride);
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const statusCheck = validateStatus0(statusRead.value);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const baselineCheck = validateBaseline0(PUBLIC_SURFACE_BASELINE0);
    if (baselineCheck.tag === 'reject') return write0(root, outputPath, writeOutput, baselineCheck);

    const surface = await CheckPublicEntryReleaseSurface0({ rootDir: root });
    const surfaceCheck = validateSurface0(surface);
    if (surfaceCheck.tag === 'reject') return write0(root, outputPath, writeOutput, surfaceCheck);

    const evidence = await digestEvidence0(root, EVIDENCE);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-surface-baseline-accepted-under-public-review-boundary',
      publicSurfaceBaselineReady: true,
      publicSurfaceBaselineCoordinate: COORD,
      publicEntryReleaseSurfaceAccepted: true,
      publicSurfaceFrozen: true,
      publicSurfaceBaselineStatus: PUBLIC_SURFACE_BASELINE0.status,
      publicEntryExportCount: surface.NF.publicEntryExportCount,
      packageExportCount: surface.NF.packageExportCount,
      packageBinCount: surface.NF.packageBinCount,
      packageScriptCount: surface.NF.packageScriptCount,
      underlyingChecker: surface.checker,
      underlyingDigest: surface.Digest,
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
    return write0(root, outputPath, writeOutput, reject0('PublicSurfaceBaseline.UnhandledException', [], 'public surface baseline checker threw unexpectedly', normErr0(error)));
  }
}

function validateStatus0(status) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicSurfaceBaseline.StatusShape', ['PNP_STATUS.json'], 'status shape mismatch');
  const boundary = boundary0(status, ['PNP_STATUS.json']);
  if (boundary.tag === 'reject') return boundary;
  if (status.publicSurfaceBaseline !== COORD) return reject0('PublicSurfaceBaseline.StatusCoordinate', ['PNP_STATUS.json', 'publicSurfaceBaseline'], 'public surface baseline coordinate mismatch', { expected: COORD, actual: status.publicSurfaceBaseline });
  return { tag: 'accept' };
}

function validateBaseline0(baseline) {
  if (!plain0(baseline) || baseline.kind !== 'PublicSurfaceBaseline0' || baseline.version !== VERSION || baseline.coordinate !== COORD) return reject0('PublicSurfaceBaseline.BaselineShape', ['PUBLIC_SURFACE_BASELINE0'], 'public surface baseline constant mismatch');
  if (typeof baseline.status !== 'string' || !baseline.status.includes('public-review-surface')) return reject0('PublicSurfaceBaseline.BaselineStatus', ['PUBLIC_SURFACE_BASELINE0', 'status'], 'public surface baseline status mismatch', { actual: baseline.status });
  return { tag: 'accept' };
}

function validateSurface0(surface) {
  if (!plain0(surface) || surface.tag !== 'accept' || surface.checker !== 'CheckPublicEntryReleaseSurface0') return reject0('PublicSurfaceBaseline.SurfaceReject', ['CheckPublicEntryReleaseSurface0'], 'underlying public-entry surface checker did not accept', { actualTag: surface?.tag ?? null, actualChecker: surface?.checker ?? null });
  if (!plain0(surface.NF) || surface.NF.surfaceFrozen !== true || surface.NF.surfaceBaseline?.coordinate !== COORD) return reject0('PublicSurfaceBaseline.SurfaceNF', ['CheckPublicEntryReleaseSurface0', 'NF'], 'underlying public-entry surface NF mismatch');
  for (const field of ['publicEntryExportCount', 'packageExportCount', 'packageBinCount', 'packageScriptCount']) {
    if (!Number.isInteger(surface.NF[field]) || surface.NF[field] <= 0) return reject0('PublicSurfaceBaseline.SurfaceCount', ['CheckPublicEntryReleaseSurface0', 'NF', field], 'surface count must be positive integer', { actual: surface.NF[field] });
  }
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicSurfaceBaseline.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicSurfaceBaseline.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicSurfaceBaseline.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicSurfaceBaseline.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) {
  if (!plain0(b)) return reject0('PublicSurfaceBaseline.BoundaryShape', pathArray, 'boundary must be object');
  if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicSurfaceBaseline.BoundaryMismatch', pathArray, 'non-activation boundary mismatch');
  return { tag: 'accept' };
}
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-surface-baseline0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public surface baseline CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicSurfaceBaseline0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
