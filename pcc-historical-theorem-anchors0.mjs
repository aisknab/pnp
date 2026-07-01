#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckHistoricalTheoremAnchors0';
const VERSION = 0;
const COORD = 'PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01';
const OUT = 'artifacts/historical-theorem-anchors/latest-verdict.json';
const MANIFEST = 'report-bindings/HISTORICAL_THEOREM_ANCHORS.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_STATUS_COORDS = {
  historicalReportSanitizedCoordinate: 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01',
  historicalReportSupersessionCoordinate: 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01'
};

export async function CheckHistoricalTheoremAnchors0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? MANIFEST, options.manifestOverride);
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifest = manifestRead.value;
    const manifestCheck = validateManifest0(manifest);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const statusRead = await readJson0(root, manifest.currentStatusPath, options.statusOverride);
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const statusCheck = validateStatus0(statusRead.value);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const bindingsRead = await readJson0(root, manifest.theoremBindingLedgerPath, options.bindingsOverride);
    if (bindingsRead.tag === 'reject') return write0(root, outputPath, writeOutput, bindingsRead);
    const bindingsCheck = validateBindings0(bindingsRead.value, manifest);
    if (bindingsCheck.tag === 'reject') return write0(root, outputPath, writeOutput, bindingsCheck);

    const anchorRead = await readText0(root, manifest.anchorIndexPath);
    if (anchorRead.tag === 'reject') return write0(root, outputPath, writeOutput, anchorRead);
    const rootReportRead = await readText0(root, manifest.currentRootReportPath);
    if (rootReportRead.tag === 'reject') return write0(root, outputPath, writeOutput, rootReportRead);
    const anchorCheck = validateAnchorText0(anchorRead.text, rootReportRead.text, manifest, bindingsRead.value);
    if (anchorCheck.tag === 'reject') return write0(root, outputPath, writeOutput, anchorCheck);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);
    const bindingAnchors = sortedUnique0(bindingsRead.value.theoremBindings.flatMap((b) => b.reportAnchors ?? []));
    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'historical-theorem-anchors-accepted-under-public-review-boundary',
      anchorIndexReady: true,
      anchorIndexUsedForHistoricalBindingCompatibility: true,
      anchorIndexIsPublicTheoremEmissionSurface: false,
      publicTheoremEmissionAllowedByAnchorIndex: false,
      allReportBindingAnchorsRepresented: true,
      theoremBindingLedgerCoordinate: bindingsRead.value.coordinate,
      theoremBindingCount: bindingsRead.value.theoremBindings.length,
      anchorCount: manifest.requiredAnchors.length,
      bindingAnchorCount: bindingAnchors.length,
      anchorIndexPath: manifest.anchorIndexPath,
      anchorIndexSha256: shaBytes0(anchorRead.bytes),
      currentRootReportPath: manifest.currentRootReportPath,
      currentRootReportSha256: shaBytes0(rootReportRead.bytes),
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
  if (!plain0(m) || m.kind !== 'PNPHistoricalTheoremAnchors0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'historical-theorem-anchors-ready') return reject0('HistoricalTheoremAnchors.ManifestShape', [MANIFEST], 'manifest shape mismatch');
  const flags = {
    anchorIndexReady: true,
    anchorIndexUsedForHistoricalBindingCompatibility: true,
    anchorIndexIsPublicTheoremEmissionSurface: false,
    publicTheoremEmissionAllowedByAnchorIndex: false,
    allReportBindingAnchorsRepresented: true
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('HistoricalTheoremAnchors.ManifestFlag', [MANIFEST, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const b = boundary0(m.claimBoundary, [MANIFEST, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  for (const field of ['anchorIndexPath', 'theoremBindingLedgerPath', 'currentStatusPath', 'currentRootReportPath', 'expectedBindingLedgerCoordinate']) if (typeof m[field] !== 'string' || m[field].length === 0) return reject0('HistoricalTheoremAnchors.ManifestString', [MANIFEST, field], 'manifest string field missing');
  if (!plain0(m.requiredStatusCoordinates)) return reject0('HistoricalTheoremAnchors.StatusCoordinateShape', [MANIFEST, 'requiredStatusCoordinates'], 'requiredStatusCoordinates must be object');
  for (const [field, expected] of Object.entries(REQUIRED_STATUS_COORDS)) if (m.requiredStatusCoordinates[field] !== expected) return reject0('HistoricalTheoremAnchors.ManifestStatusCoordinate', [MANIFEST, 'requiredStatusCoordinates', field], 'required status coordinate mismatch', { expected, actual: m.requiredStatusCoordinates[field] });
  for (const field of ['requiredAnchors', 'forbiddenActiveClaimFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('HistoricalTheoremAnchors.ArrayMissing', [MANIFEST, field], 'manifest array missing or invalid');
  if (new Set(m.requiredAnchors).size !== m.requiredAnchors.length) return reject0('HistoricalTheoremAnchors.DuplicateAnchor', [MANIFEST, 'requiredAnchors'], 'required anchors must be unique');
  return { tag: 'accept' };
}

function validateStatus0(s) {
  if (!plain0(s) || s.kind !== 'PNPStatus0' || s.project !== 'PNP') return reject0('HistoricalTheoremAnchors.StatusShape', ['PNP_STATUS.json'], 'status shape mismatch');
  const b = boundary0(s, ['PNP_STATUS.json']);
  if (b.tag === 'reject') return b;
  for (const [field, expected] of Object.entries(REQUIRED_STATUS_COORDS)) if (s[field] !== expected) return reject0('HistoricalTheoremAnchors.StatusCoordinate', ['PNP_STATUS.json', field], 'status required coordinate mismatch', { expected, actual: s[field] });
  return { tag: 'accept' };
}

function validateBindings0(bindings, manifest) {
  if (!plain0(bindings) || bindings.kind !== 'PNPReportTheoremBindings0' || bindings.coordinate !== manifest.expectedBindingLedgerCoordinate) return reject0('HistoricalTheoremAnchors.BindingLedgerShape', [manifest.theoremBindingLedgerPath], 'binding ledger shape mismatch');
  const b = boundary0(bindings.claimBoundary, [manifest.theoremBindingLedgerPath, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  if (!Array.isArray(bindings.theoremBindings) || bindings.theoremBindings.length === 0) return reject0('HistoricalTheoremAnchors.BindingRowsMissing', [manifest.theoremBindingLedgerPath, 'theoremBindings'], 'theorem bindings missing');
  const manifestAnchors = new Set(manifest.requiredAnchors);
  for (let i = 0; i < bindings.theoremBindings.length; i += 1) {
    const row = bindings.theoremBindings[i];
    if (!plain0(row) || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('HistoricalTheoremAnchors.BindingOverclaim', [manifest.theoremBindingLedgerPath, 'theoremBindings', i], 'theorem binding row overclaims');
    if (!Array.isArray(row.reportAnchors) || row.reportAnchors.length === 0) return reject0('HistoricalTheoremAnchors.BindingAnchorMissing', [manifest.theoremBindingLedgerPath, 'theoremBindings', i, 'reportAnchors'], 'reportAnchors missing');
    for (const anchor of row.reportAnchors) if (!manifestAnchors.has(anchor)) return reject0('HistoricalTheoremAnchors.BindingAnchorUnrepresented', [manifest.theoremBindingLedgerPath, 'theoremBindings', i, 'reportAnchors'], 'binding ledger anchor absent from requiredAnchors manifest', { anchor, theoremId: row.id ?? null });
  }
  return { tag: 'accept' };
}

function validateAnchorText0(anchorText, rootReportText, manifest, bindings) {
  if (!anchorText.includes(COORD)) return reject0('HistoricalTheoremAnchors.AnchorCoordinateMissing', [manifest.anchorIndexPath], 'anchor index coordinate missing');
  const combined = `${anchorText}\n${rootReportText}`;
  for (const anchor of manifest.requiredAnchors) {
    if (!anchorText.includes(anchor)) return reject0('HistoricalTheoremAnchors.RequiredAnchorMissing', [manifest.anchorIndexPath, anchor], 'required anchor missing from anchor index');
  }
  for (const row of bindings.theoremBindings) {
    for (const anchor of row.reportAnchors) if (!combined.includes(anchor)) return reject0('HistoricalTheoremAnchors.BindingAnchorNotFindable', [manifest.theoremBindingLedgerPath, row.id ?? null, anchor], 'binding anchor not findable in anchor index or current report');
  }
  for (const fragment of manifest.forbiddenActiveClaimFragments) {
    if (anchorText.includes(fragment)) return reject0('HistoricalTheoremAnchors.ForbiddenAnchorClaim', [manifest.anchorIndexPath, fragment], 'anchor index contains forbidden active claim fragment');
    if (rootReportText.includes(fragment)) return reject0('HistoricalTheoremAnchors.ForbiddenRootClaim', [manifest.currentRootReportPath, fragment], 'current root report contains forbidden active claim fragment');
  }
  for (const fragment of ['publicTheoremEmissionAllowed = false', 'finalTheoremReady = false', 'activeFinalNodeIds = []']) if (!anchorText.includes(fragment)) return reject0('HistoricalTheoremAnchors.AnchorBoundaryMissing', [manifest.anchorIndexPath, fragment], 'anchor index boundary fragment missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) { if (override !== undefined) return { tag: 'accept', value: override }; try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('HistoricalTheoremAnchors.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); } }
async function readText0(root, rel) { try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; } catch (error) { return reject0('HistoricalTheoremAnchors.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); } }
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of paths) {
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
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('HistoricalTheoremAnchors.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('HistoricalTheoremAnchors.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function safeJoinRequired0(root, rel) { const p = safeJoin0(root, rel); if (p === null) throw new Error(`unsafe path: ${rel}`); return p; }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sortedUnique0(values) { return Array.from(new Set(values)).sort(); }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function shaBytes0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return createHash('sha256').update(String(text), 'utf8').digest('hex'); }
function normErr0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--manifest') o.manifestPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-historical-theorem-anchors0.mjs [--json] [--no-write] [--root <path>] [--output <path>] [--manifest <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad historical theorem anchor CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckHistoricalTheoremAnchors0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
