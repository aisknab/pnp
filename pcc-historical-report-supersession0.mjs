#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckHistoricalReportSupersession0';
const VERSION = 0;
const COORD = 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01';
const SANITIZED_COORD = 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01';
const OUT = 'artifacts/historical-report-supersession/latest-verdict.json';
const MANIFEST = 'report-bindings/HISTORICAL_REPORT_SUPERSESSION.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_COORDINATES = {
  directBindingIndexCoordinate: 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01',
  section22DirectBindingRunnerCoordinate: 'PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01'
};
const PDF_REQUIRED_FRAGMENTS = [
  SANITIZED_COORD,
  'Public theorem emission is disabled',
  'finalTheoremReady = false',
  'activeFinalNodeIds = []',
  'Release.UnrestrictedFinalSoundness',
  'ExternalReview.Acceptance',
  'npm run pnp:verify'
];

export async function CheckHistoricalReportSupersession0(options = {}) {
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

    const texRead = await readText0(root, manifest.historicalReportPath);
    if (texRead.tag === 'reject') return write0(root, outputPath, writeOutput, texRead);
    const texCheck = validateSanitizedTex0(texRead.text, manifest.requiredCurrentReportFragments, manifest.forbiddenHistoricalDirectClaimFragments);
    if (texCheck.tag === 'reject') return write0(root, outputPath, writeOutput, texCheck);

    const pdfRead = await readText0(root, manifest.historicalReportPdfPath);
    if (pdfRead.tag === 'reject') return write0(root, outputPath, writeOutput, pdfRead);
    const pdfCheck = validateSanitizedPdf0(pdfRead.text, manifest.forbiddenHistoricalDirectClaimFragments);
    if (pdfCheck.tag === 'reject') return write0(root, outputPath, writeOutput, pdfCheck);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      sanitizedReportCoordinate: SANITIZED_COORD,
      claimStatus: 'historical-report-sanitized-under-public-review-boundary',
      historicalReportSupersessionReady: true,
      historicalReportSanitizedReady: true,
      historicalReportPath: manifest.historicalReportPath,
      historicalReportPdfPath: manifest.historicalReportPdfPath,
      historicalTexSha256: shaBytes0(texRead.bytes),
      historicalPdfSha256: shaBytes0(pdfRead.bytes),
      historicalDirectTheoremEmissionRepresented: false,
      historicalDirectTheoremEmissionSanitized: true,
      currentRootReportSanitized: true,
      currentPdfSanitized: true,
      requiredCurrentReportFragmentCount: manifest.requiredCurrentReportFragments.length,
      forbiddenHistoricalDirectClaimFragmentCount: manifest.forbiddenHistoricalDirectClaimFragments.length,
      currentBoundarySupersedesHistoricalEmission: true,
      historicalReportMayBeMutatedBySuccessorPRs: true,
      publicTheoremEmissionAllowedBySupersession: false,
      requiredCurrentCoordinates: { ...REQUIRED_COORDINATES },
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
    return write0(root, outputPath, writeOutput, reject0('HistoricalReportSupersession.UnhandledException', [], 'historical report supersession checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPHistoricalReportSupersession0' || m.version !== VERSION || m.coordinate !== COORD || m.sanitizedReportCoordinate !== SANITIZED_COORD || m.status !== 'historical-report-sanitized-ready') return reject0('HistoricalReportSupersession.ManifestShape', [MANIFEST], 'manifest shape mismatch');
  const flags = {
    historicalReportSupersessionReady: true,
    historicalReportSanitizedReady: true,
    historicalDirectTheoremEmissionRepresented: false,
    historicalDirectTheoremEmissionSanitized: true,
    currentRootReportSanitized: true,
    currentPdfSanitized: true,
    currentBoundarySupersedesHistoricalEmission: true,
    historicalReportMayBeMutatedBySuccessorPRs: true,
    publicTheoremEmissionAllowedBySupersession: false
  };
  for (const [field, expected] of Object.entries(flags)) {
    if (m[field] !== expected) return reject0('HistoricalReportSupersession.ManifestFlag', [MANIFEST, field], 'manifest flag mismatch', { expected, actual: m[field] });
  }
  const b = boundary0(m.claimBoundary, [MANIFEST, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  if (!plain0(m.requiredCurrentCoordinates)) return reject0('HistoricalReportSupersession.CoordinateShape', [MANIFEST, 'requiredCurrentCoordinates'], 'required coordinate object missing');
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) {
    if (m.requiredCurrentCoordinates[field] !== expected) return reject0('HistoricalReportSupersession.ManifestCoordinate', [MANIFEST, 'requiredCurrentCoordinates', field], 'required coordinate mismatch', { expected, actual: m.requiredCurrentCoordinates[field] });
  }
  for (const field of ['historicalReportPath', 'historicalReportPdfPath', 'currentStatusPath']) {
    if (typeof m[field] !== 'string' || m[field].length === 0) return reject0('HistoricalReportSupersession.PathMissing', [MANIFEST, field], 'manifest path missing');
  }
  for (const field of ['requiredCurrentReportFragments', 'forbiddenHistoricalDirectClaimFragments', 'evidenceSurfaces', 'nonClaims']) {
    if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('HistoricalReportSupersession.ArrayMissing', [MANIFEST, field], 'manifest array missing or invalid');
  }
  return { tag: 'accept' };
}
function validateStatus0(s) {
  if (!plain0(s) || s.kind !== 'PNPStatus0' || s.project !== 'PNP') return reject0('HistoricalReportSupersession.StatusShape', ['PNP_STATUS.json'], 'status shape mismatch');
  const b = boundary0(s, ['PNP_STATUS.json']);
  if (b.tag === 'reject') return b;
  for (const [field, expected] of Object.entries(REQUIRED_COORDINATES)) {
    if (s[field] !== expected) return reject0('HistoricalReportSupersession.StatusCoordinate', ['PNP_STATUS.json', field], 'status required coordinate mismatch', { expected, actual: s[field] });
  }
  return { tag: 'accept' };
}
function validateSanitizedTex0(tex, required, forbidden) {
  for (const fragment of required) {
    if (!tex.includes(fragment)) return reject0('HistoricalReportSupersession.RequiredCurrentFragmentMissing', ['canonical_proof_report.tex', fragment], 'sanitized root report required fragment missing');
  }
  for (const fragment of forbidden) {
    if (tex.includes(fragment)) return reject0('HistoricalReportSupersession.ForbiddenDirectClaimPresent', ['canonical_proof_report.tex', fragment], 'sanitized root report still contains a forbidden historical direct theorem-emission fragment');
  }
  return { tag: 'accept' };
}
function validateSanitizedPdf0(pdfText, forbidden) {
  if (!pdfText.startsWith('%PDF-')) return reject0('HistoricalReportSupersession.PdfHeader', ['canonical_proof_report.pdf'], 'sanitized PDF must have a PDF header');
  for (const fragment of PDF_REQUIRED_FRAGMENTS) {
    if (!pdfText.includes(fragment)) return reject0('HistoricalReportSupersession.PdfRequiredFragmentMissing', ['canonical_proof_report.pdf', fragment], 'sanitized PDF required fragment missing');
  }
  for (const fragment of forbidden) {
    if (pdfText.includes(fragment)) return reject0('HistoricalReportSupersession.PdfForbiddenDirectClaimPresent', ['canonical_proof_report.pdf', fragment], 'sanitized PDF still contains a forbidden historical direct theorem-emission fragment');
  }
  return { tag: 'accept' };
}
async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('HistoricalReportSupersession.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('HistoricalReportSupersession.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of paths) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('HistoricalReportSupersession.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('HistoricalReportSupersession.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('HistoricalReportSupersession.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) {
  if (!plain0(b)) return reject0('HistoricalReportSupersession.BoundaryShape', pathArray, 'boundary must be object');
  if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('HistoricalReportSupersession.BoundaryMismatch', pathArray, 'non-activation boundary mismatch');
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
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--manifest') o.manifestPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-historical-report-supersession0.mjs [--json] [--no-write] [--root <path>] [--output <path>] [--manifest <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad historical report supersession CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckHistoricalReportSupersession0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
