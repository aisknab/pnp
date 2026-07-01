#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckDirectBindingIndex0';
const VERSION = 0;
const COORD = 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01';
const OUT = 'artifacts/direct-binding-index/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const FILES = {
  index: 'report-bindings/direct-bindings/DIRECT_BINDING_INDEX.json',
  inventory: 'report-bindings/REPORT_THEOREM_INVENTORY.json',
  matrix: 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json',
  closure: 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json',
  status: 'PNP_STATUS.json'
};

export async function CheckDirectBindingIndex0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const reads = {};
    for (const [k, f] of Object.entries(FILES)) {
      const r = await readJson0(root, options[`${k}Path`] ?? f, options[`${k}Override`]);
      if (r.tag === 'reject') return write0(root, outputPath, writeOutput, r);
      reads[k] = r;
    }
    const idxCheck = indexShape0(reads.index.value);
    if (idxCheck.tag === 'reject') return write0(root, outputPath, writeOutput, idxCheck);
    for (const check of [boundary0(reads.index.value.claimBoundary, ['index', 'claimBoundary']), boundary0(reads.status.value, ['status'])]) {
      if (check.tag === 'reject') return write0(root, outputPath, writeOutput, check);
    }
    const rows = reads.index.value.entries.map((raw, i) => entry0(raw, i));
    for (const row of rows) if (row.tag === 'reject') return write0(root, outputPath, writeOutput, row);
    const entries = rows.map((x) => x.entry);
    const full = await checkRows0(root, entries, reads.inventory.value, reads.matrix.value, reads.closure.value);
    if (full.tag === 'reject') return write0(root, outputPath, writeOutput, full);
    const files = await digestFiles0(root, [FILES.index, FILES.inventory, FILES.matrix, FILES.closure, FILES.status, ...entries.flatMap((x) => [x.manifestPath, x.checkerPath, x.testPath])]);
    if (files.tag === 'reject') return write0(root, outputPath, writeOutput, files);
    return write0(root, outputPath, writeOutput, {
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD,
      claimStatus: 'section22-direct-binding-index-accepted-under-public-review-boundary',
      section22RowsIndexed: true, indexedEntryCount: entries.length,
      allSection22RowsHaveExecutableSurface: true,
      allSection22RowsDirectCheckerComplete: false,
      publicTheoremEmissionAllowedByIndex: false,
      directCheckerBindingCompleteCount: full.directCheckerBindingCompleteCount,
      releaseCriticalBoundaryRows: full.releaseCriticalBoundaryRows,
      blockedGapRows: full.blockedGapRows,
      seedUpgradeRows: full.seedUpgradeRows,
      closureStatusCounts: full.closureStatusCounts,
      coverageClassCounts: full.coverageClassCounts,
      indexDigestSha256: shaText0(stable0(files.files)),
      evidenceFileCount: files.files.length,
      evidenceFiles: files.files,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('DirectBindingIndex.UnhandledException', [], 'direct-binding index checker threw unexpectedly', normErr0(error)));
  }
}

async function checkRows0(root, entries, inv, matrix, closure) {
  const inventoryRows = arr0(inv?.inventoryEntries);
  const coverageRows = arr0(matrix?.coverageEntries);
  const closureRows = arr0(closure?.closureEntries);
  if (inventoryRows.length !== entries.length) return reject0('DirectBindingIndex.InventoryCount', ['inventoryEntries'], 'inventory count mismatch', { expected: entries.length, actual: inventoryRows.length });
  if (coverageRows.length !== entries.length) return reject0('DirectBindingIndex.CoverageCount', ['coverageEntries'], 'coverage count mismatch', { expected: entries.length, actual: coverageRows.length });
  if (closureRows.length !== entries.length) return reject0('DirectBindingIndex.ClosureCount', ['closureEntries'], 'closure count mismatch', { expected: entries.length, actual: closureRows.length });
  const seen = new Set();
  const closureStatusCounts = {};
  const coverageClassCounts = {};
  let directCheckerBindingCompleteCount = 0, releaseCriticalBoundaryRows = 0, blockedGapRows = 0, seedUpgradeRows = 0;
  for (const e of entries) {
    const key = `${e.inventoryEntryId}/${e.coverageEntryId}/${e.closureEntryId}`;
    if (seen.has(key)) return reject0('DirectBindingIndex.DuplicateEntry', ['entries', key], 'duplicate direct-binding index row');
    seen.add(key);
    const ir = inventoryRows.find((x) => x.id === e.inventoryEntryId);
    const cr = coverageRows.find((x) => x.id === e.coverageEntryId);
    const dr = closureRows.find((x) => x.id === e.closureEntryId);
    if (!plain0(ir) || ir.sourceLabel !== e.sourceLabel || ir.publicEmissionEffect !== 'none' || ir.dischargesPublicTheorem !== false) return reject0('DirectBindingIndex.InventoryRowMismatch', ['inventory', e.inventoryEntryId], 'inventory row mismatch');
    if (!plain0(cr) || cr.inventoryEntryId !== e.inventoryEntryId || cr.sourceLabel !== e.sourceLabel || cr.directCheckerBindingComplete !== false || cr.publicEmissionEffect !== 'none' || cr.dischargesPublicTheorem !== false) return reject0('DirectBindingIndex.CoverageRowMismatch', ['coverage', e.coverageEntryId], 'coverage row mismatch');
    if (!plain0(dr) || dr.coverageEntryId !== e.coverageEntryId || dr.inventoryEntryId !== e.inventoryEntryId || dr.sourceLabel !== e.sourceLabel || dr.nextDirectBindingSurface !== path.basename(e.checkerPath) || dr.mayFlipDirectCheckerBindingComplete !== false || dr.publicEmissionEffect !== 'none' || dr.dischargesPublicTheorem !== false) return reject0('DirectBindingIndex.ClosureRowMismatch', ['closure', e.closureEntryId], 'closure row mismatch');
    const mr = await readJson0(root, e.manifestPath);
    if (mr.tag === 'reject') return mr;
    const br = mr.value?.boundInventoryEntry;
    if (!plain0(br) || br.inventoryEntryId !== e.inventoryEntryId || br.coverageEntryId !== e.coverageEntryId || br.closureEntryId !== e.closureEntryId || br.sourceLabel !== e.sourceLabel) return reject0('DirectBindingIndex.ManifestBoundRowMismatch', ['manifest', e.manifestPath, 'boundInventoryEntry'], 'manifest bound row mismatch');
    if (mr.value.directCheckerBindingComplete !== false || mr.value.publicTheoremEmissionAllowedByBinding !== false) return reject0('DirectBindingIndex.ManifestOverclaim', ['manifest', e.manifestPath], 'manifest direct-binding overclaim');
    const bc = boundary0(mr.value.claimBoundary, ['manifest', e.manifestPath, 'claimBoundary']);
    if (bc.tag === 'reject') return bc;
    for (const f of [e.checkerPath, e.testPath]) {
      const ex = await fileExists0(root, f);
      if (ex.tag === 'reject') return ex;
    }
    closureStatusCounts[dr.closureStatus] = (closureStatusCounts[dr.closureStatus] ?? 0) + 1;
    coverageClassCounts[dr.currentCoverageClass] = (coverageClassCounts[dr.currentCoverageClass] ?? 0) + 1;
    if (cr.directCheckerBindingComplete === true) directCheckerBindingCompleteCount += 1;
    if (dr.currentCoverageClass === 'release-critical-boundary-surface') releaseCriticalBoundaryRows += 1;
    if (String(dr.closureStatus).startsWith('blocked-by')) blockedGapRows += 1;
    if (dr.closureStatus === 'direct-binding-seed-upgrade-needed') seedUpgradeRows += 1;
  }
  const indexedInv = new Set(entries.map((x) => x.inventoryEntryId));
  for (const row of inventoryRows) if (!indexedInv.has(row.id)) return reject0('DirectBindingIndex.InventoryUnindexed', ['inventory', row.id], 'inventory row missing from direct-binding index');
  return { tag: 'accept', closureStatusCounts, coverageClassCounts, directCheckerBindingCompleteCount, releaseCriticalBoundaryRows, blockedGapRows, seedUpgradeRows };
}
function indexShape0(x) {
  if (!plain0(x) || x.kind !== 'PNPDirectBindingIndex0' || x.version !== VERSION || x.coordinate !== COORD || x.section22RowsIndexed !== true || x.allSection22RowsHaveExecutableSurface !== true || x.allSection22RowsDirectCheckerComplete !== false || x.publicTheoremEmissionAllowedByIndex !== false) return reject0('DirectBindingIndex.Shape', ['index'], 'index manifest shape mismatch');
  if (!Array.isArray(x.entries) || x.entries.length !== x.expectedEntryCount || x.expectedEntryCount !== 27) return reject0('DirectBindingIndex.EntryCount', ['index', 'entries'], 'index entry count mismatch');
  return { tag: 'accept' };
}
function entry0(raw, i) {
  if (!Array.isArray(raw) || raw.length !== 7 || raw.some((v) => typeof v !== 'string' || v.length === 0)) return reject0('DirectBindingIndex.BadEntry', ['entries', i], 'index entry must be seven non-empty strings');
  const [inventoryEntryId, coverageEntryId, closureEntryId, sourceLabel, manifestPath, checkerPath, testPath] = raw;
  return { tag: 'accept', entry: { inventoryEntryId, coverageEntryId, closureEntryId, sourceLabel, manifestPath, checkerPath, testPath } };
}
async function readJson0(root, f, override) { if (override !== undefined) return { tag: 'accept', value: override }; try { const bytes = await readFile(path.join(root, f)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')) }; } catch (error) { return reject0('DirectBindingIndex.ReadOrParseFailed', [f], 'could not read or parse JSON', normErr0(error)); } }
async function fileExists0(root, f) { try { const info = await stat(path.join(root, f)); if (!info.isFile()) return reject0('DirectBindingIndex.NotFile', [f], 'path is not a file'); return { tag: 'accept' }; } catch (error) { return reject0('DirectBindingIndex.MissingFile', [f], 'required file missing', normErr0(error)); } }
async function digestFiles0(root, paths) { const files = []; for (const f of [...new Set(paths)]) { const safe = safeJoin0(root, f); if (safe === null) return reject0('DirectBindingIndex.UnsafePath', [f], 'unsafe evidence path'); try { const info = await stat(safe); if (!info.isFile()) return reject0('DirectBindingIndex.NotFile', [f], 'evidence path is not a file'); const bytes = await readFile(safe); files.push({ path: f, size: bytes.length, sha256: sha0(bytes) }); } catch (error) { return reject0('DirectBindingIndex.MissingEvidence', [f], 'evidence path missing', normErr0(error)); } } return { tag: 'accept', files }; }
function boundary0(b, p) { if (!plain0(b)) return reject0('DirectBindingIndex.BoundaryShape', p, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('DirectBindingIndex.BoundaryMismatch', p, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function arr0(v) { return Array.isArray(v) ? v : []; }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function sha0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return sha0(Buffer.from(text, 'utf8')); }
function normErr0(e) { return { name: e?.name ?? 'Error', message: e?.message ?? String(e), code: e?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-direct-binding-index0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let o; try { o = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad direct-binding index CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const v = await CheckDirectBindingIndex0(o); const rendered = JSON.stringify(v, null, 2); if (o.json || v.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(v.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
