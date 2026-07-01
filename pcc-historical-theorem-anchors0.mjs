#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckHistoricalTheoremAnchors0';
const VERSION = 0;
const COORD = 'PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01';
const OUT = 'artifacts/historical-theorem-anchors/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_LINKED = {
  reportTheoremBindings: 'REPORT-THEOREM-BINDINGS-2026-06-27-01',
  historicalReportSupersession: 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01',
  historicalReportSanitized: 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01'
};
const STATUS_COORDS = {
  historicalReportSupersessionCoordinate: 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01',
  historicalReportSanitizedCoordinate: 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01',
  theoremBindingLedgerCoordinate: 'REPORT-THEOREM-BINDINGS-2026-06-27-01'
};
const DEFAULT_FILES = {
  manifest: 'report-bindings/HISTORICAL_THEOREM_ANCHORS.json',
  markdown: 'report-bindings/HISTORICAL_THEOREM_ANCHORS.md',
  bindings: 'report-bindings/REPORT_THEOREM_BINDINGS.json',
  supersession: 'report-bindings/HISTORICAL_REPORT_SUPERSESSION.json',
  status: 'PNP_STATUS.json'
};

export async function CheckHistoricalTheoremAnchors0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? DEFAULT_FILES.manifest, options.manifestOverride);
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifest = manifestRead.value;
    const m = validateManifest0(manifest);
    if (m.tag === 'reject') return write0(root, outputPath, writeOutput, m);

    const bindingsRead = await readJson0(root, manifest.sourceFiles.reportTheoremBindings, options.bindingsOverride);
    if (bindingsRead.tag === 'reject') return write0(root, outputPath, writeOutput, bindingsRead);
    const bindingsCheck = validateBindings0(bindingsRead.value, manifest.anchors);
    if (bindingsCheck.tag === 'reject') return write0(root, outputPath, writeOutput, bindingsCheck);

    const statusRead = await readJson0(root, manifest.sourceFiles.status, options.statusOverride);
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const statusCheck = validateStatus0(statusRead.value);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const supersessionRead = await readJson0(root, manifest.sourceFiles.historicalReportSupersession, options.supersessionOverride);
    if (supersessionRead.tag === 'reject') return write0(root, outputPath, writeOutput, supersessionRead);
    const supersessionCheck = validateSupersession0(supersessionRead.value);
    if (supersessionCheck.tag === 'reject') return write0(root, outputPath, writeOutput, supersessionCheck);

    const mdRead = await readText0(root, manifest.sourceFiles.anchorMarkdown);
    if (mdRead.tag === 'reject') return write0(root, outputPath, writeOutput, mdRead);
    const mdCheck = validateMarkdown0(mdRead.text, manifest.anchors);
    if (mdCheck.tag === 'reject') return write0(root, outputPath, writeOutput, mdCheck);

    const evidence = await digestEvidence0(root, [
      options.manifestPath ?? DEFAULT_FILES.manifest,
      manifest.sourceFiles.anchorMarkdown,
      manifest.sourceFiles.reportTheoremBindings,
      manifest.sourceFiles.historicalReportSupersession,
      manifest.sourceFiles.status,
      'pcc-historical-theorem-anchors0.mjs',
      'audits/historical-theorem-anchors0.test.mjs'
    ]);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'historical-theorem-anchor-index-accepted-under-public-review-boundary',
      anchorIndexReady: true,
      anchorIndexIsTheoremEmissionSurface: false,
      publicTheoremEmissionAllowedByAnchorIndex: false,
      anchorCount: manifest.anchors.length,
      boundTheoremBindingCount: bindingsCheck.boundTheoremBindingCount,
      linkedCoordinates: { ...EXPECTED_LINKED },
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
    return write0(root, outputPath, writeOutput, reject0('HistoricalTheoremAnchors.UnhandledException', [], 'historical theorem anchor checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPHistoricalTheoremAnchors0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'historical-theorem-anchor-index-ready') return reject0('HistoricalTheoremAnchors.ManifestShape', [DEFAULT_FILES.manifest], 'manifest shape mismatch');
  if (m.anchorIndexReady !== true || m.anchorIndexIsTheoremEmissionSurface !== false || m.publicTheoremEmissionAllowedByAnchorIndex !== false) return reject0('HistoricalTheoremAnchors.ManifestFlags', [DEFAULT_FILES.manifest], 'manifest flag mismatch');
  const b = boundary0(m.claimBoundary, [DEFAULT_FILES.manifest, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  if (!plain0(m.linkedCoordinates)) return reject0('HistoricalTheoremAnchors.LinkedShape', [DEFAULT_FILES.manifest, 'linkedCoordinates'], 'linked coordinates missing');
  for (const [field, expected] of Object.entries(EXPECTED_LINKED)) {
    if (m.linkedCoordinates[field] !== expected) return reject0('HistoricalTheoremAnchors.LinkedCoordinateMismatch', [DEFAULT_FILES.manifest, 'linkedCoordinates', field], 'linked coordinate mismatch', { expected, actual: m.linkedCoordinates[field] });
  }
  if (!plain0(m.sourceFiles)) return reject0('HistoricalTheoremAnchors.SourceFilesShape', [DEFAULT_FILES.manifest, 'sourceFiles'], 'sourceFiles missing');
  for (const field of ['anchorMarkdown', 'reportTheoremBindings', 'historicalReportSupersession', 'status']) {
    if (typeof m.sourceFiles[field] !== 'string' || m.sourceFiles[field].length === 0) return reject0('HistoricalTheoremAnchors.SourceFileMissing', [DEFAULT_FILES.manifest, 'sourceFiles', field], 'source file path missing');
  }
  if (!Array.isArray(m.anchors) || m.anchors.length !== m.expectedAnchorCount || m.expectedAnchorCount !== 20) return reject0('HistoricalTheoremAnchors.AnchorCount', [DEFAULT_FILES.manifest, 'anchors'], 'anchor count mismatch', { expected: 20, actual: m.anchors?.length ?? null });
  const seenIds = new Set();
  const seenAnchors = new Set();
  for (let i = 0; i < m.anchors.length; i += 1) {
    const row = m.anchors[i];
    if (!plain0(row) || typeof row.theoremBindingId !== 'string' || row.theoremBindingId.length === 0 || typeof row.anchor !== 'string' || row.anchor.length === 0) return reject0('HistoricalTheoremAnchors.AnchorShape', [DEFAULT_FILES.manifest, 'anchors', i], 'anchor row shape mismatch');
    if (seenIds.has(row.theoremBindingId)) return reject0('HistoricalTheoremAnchors.DuplicateBindingId', [DEFAULT_FILES.manifest, 'anchors', i], 'duplicate theorem binding id', { theoremBindingId: row.theoremBindingId });
    if (seenAnchors.has(row.anchor)) return reject0('HistoricalTheoremAnchors.DuplicateAnchor', [DEFAULT_FILES.manifest, 'anchors', i], 'duplicate anchor', { anchor: row.anchor });
    seenIds.add(row.theoremBindingId);
    seenAnchors.add(row.anchor);
  }
  return { tag: 'accept' };
}

function validateBindings0(bindings, anchors) {
  if (!plain0(bindings) || bindings.kind !== 'PNPReportTheoremBindings0' || bindings.coordinate !== EXPECTED_LINKED.reportTheoremBindings) return reject0('HistoricalTheoremAnchors.BindingsShape', [DEFAULT_FILES.bindings], 'report theorem bindings shape mismatch');
  const b = boundary0(bindings.claimBoundary, [DEFAULT_FILES.bindings, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  if (!Array.isArray(bindings.theoremBindings) || bindings.theoremBindings.length !== anchors.length) return reject0('HistoricalTheoremAnchors.BindingCount', [DEFAULT_FILES.bindings, 'theoremBindings'], 'theorem binding count mismatch', { expected: anchors.length, actual: bindings.theoremBindings?.length ?? null });
  const anchorById = new Map(anchors.map((row) => [row.theoremBindingId, row.anchor]));
  for (const binding of bindings.theoremBindings) {
    if (!plain0(binding) || typeof binding.id !== 'string') return reject0('HistoricalTheoremAnchors.BindingShape', [DEFAULT_FILES.bindings, 'theoremBindings'], 'binding row shape mismatch');
    if (!anchorById.has(binding.id)) return reject0('HistoricalTheoremAnchors.UnindexedBinding', [DEFAULT_FILES.bindings, 'theoremBindings', binding.id], 'theorem binding missing from anchor index');
    const expectedAnchor = anchorById.get(binding.id);
    if (!Array.isArray(binding.reportAnchors) || binding.reportAnchors.length !== 1 || binding.reportAnchors[0] !== expectedAnchor) return reject0('HistoricalTheoremAnchors.BindingAnchorMismatch', [DEFAULT_FILES.bindings, 'theoremBindings', binding.id, 'reportAnchors'], 'binding report anchor mismatch', { expected: expectedAnchor, actual: binding.reportAnchors });
    if (binding.publicEmissionEffect !== 'none' || binding.dischargesPublicTheorem !== false) return reject0('HistoricalTheoremAnchors.BindingOverclaim', [DEFAULT_FILES.bindings, 'theoremBindings', binding.id], 'binding overclaims public theorem emission');
  }
  return { tag: 'accept', boundTheoremBindingCount: bindings.theoremBindings.length };
}

function validateStatus0(status) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('HistoricalTheoremAnchors.StatusShape', [DEFAULT_FILES.status], 'status shape mismatch');
  const b = boundary0(status, [DEFAULT_FILES.status]);
  if (b.tag === 'reject') return b;
  for (const [field, expected] of Object.entries(STATUS_COORDS)) {
    if (status[field] !== expected) return reject0('HistoricalTheoremAnchors.StatusCoordinateMismatch', [DEFAULT_FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  }
  return { tag: 'accept' };
}

function validateSupersession0(s) {
  if (!plain0(s) || s.kind !== 'PNPHistoricalReportSupersession0' || s.coordinate !== EXPECTED_LINKED.historicalReportSupersession || s.sanitizedReportCoordinate !== EXPECTED_LINKED.historicalReportSanitized || s.historicalReportSanitizedReady !== true || s.publicTheoremEmissionAllowedBySupersession !== false) return reject0('HistoricalTheoremAnchors.SupersessionShape', [DEFAULT_FILES.supersession], 'historical report supersession shape mismatch');
  return boundary0(s.claimBoundary, [DEFAULT_FILES.supersession, 'claimBoundary']);
}

function validateMarkdown0(text, anchors) {
  if (!text.includes(COORD)) return reject0('HistoricalTheoremAnchors.MarkdownCoordinateMissing', [DEFAULT_FILES.markdown], 'markdown coordinate missing');
  if (!text.includes('not a theorem-emission surface')) return reject0('HistoricalTheoremAnchors.MarkdownNonClaimMissing', [DEFAULT_FILES.markdown], 'markdown non-claim missing');
  for (const { anchor } of anchors) {
    if (!text.includes(anchor)) return reject0('HistoricalTheoremAnchors.MarkdownAnchorMissing', [DEFAULT_FILES.markdown, anchor], 'anchor missing from markdown index');
  }
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('HistoricalTheoremAnchors.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('HistoricalTheoremAnchors.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('HistoricalTheoremAnchors.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('HistoricalTheoremAnchors.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('HistoricalTheoremAnchors.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) {
  if (!plain0(b)) return reject0('HistoricalTheoremAnchors.BoundaryShape', pathArray, 'boundary must be object');
  if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('HistoricalTheoremAnchors.BoundaryMismatch', pathArray, 'non-activation boundary mismatch');
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--manifest') o.manifestPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-historical-theorem-anchors0.mjs [--json] [--no-write] [--root <path>] [--output <path>] [--manifest <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad historical theorem anchor CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckHistoricalTheoremAnchors0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
