#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckGDirectBindingSeed0';
const VERSION = 0;
const COORD = 'PNP-DIRECT-BIND-G-LOCKED-NAND-THRESHOLD-SEED-2026-06-27-01';
const OUT = 'artifacts/direct-bind-locked-nand-threshold/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const CLOSURE_GAPS = ['GAP-003-BoundedSmallModelsNotUniformProof', 'GAP-004-FiniteToUnboundedUniformity'];
const FILES = {
  manifest: 'report-bindings/direct-bindings/G_DIRECT_BINDING_SEED.json',
  inventory: 'report-bindings/REPORT_THEOREM_INVENTORY.json',
  matrix: 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json',
  closure: 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json',
  smallModels: 'semantics/locked-nand-sat-small-models-config.json',
  complexity: 'complexity/COMPLEXITY_LEDGER.json',
  gaps: 'proof-obligations/GAP_LEDGER.json',
  finite: 'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json',
  status: 'PNP_STATUS.json'
};

export async function CheckGDirectBindingSeed0(options = {}) {
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
    for (const check of [manifest0(reads.manifest.value), inventory0(reads.inventory.value), matrix0(reads.matrix.value), closure0(reads.closure.value), smallModels0(reads.smallModels.value), complexity0(reads.complexity.value), gaps0(reads.gaps.value), finite0(reads.finite.value), boundary0(reads.status.value, ['status'])]) {
      if (check.tag === 'reject') return write0(root, outputPath, writeOutput, check);
    }
    const evidence = await digestEvidence0(root, reads.manifest.value.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);
    return write0(root, outputPath, writeOutput, {
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD,
      claimStatus: 'g-direct-binding-seed-accepted-under-public-review-boundary',
      gDirectBindingSeedReady: true, directBindingBlockedByGaps: true,
      boundInventoryEntryId: 'TL-025-G', boundCoverageEntryId: 'COV-025-G', boundClosureEntryId: 'DCC-025-G',
      coverageClass: 'locked-nand-seed-surface', closureStatus: 'direct-binding-seed-upgrade-needed',
      blockingGaps: [...CLOSURE_GAPS], directCheckerBindingComplete: false, fullHistoricalGTheoremDischarged: false,
      publicTheoremEmissionAllowedByBinding: false, fullLockedNANDThresholdCoverageProved: false,
      evidenceFileCount: evidence.files.length, evidenceDigestSha256: shaText0(stable0(evidence.files)), evidenceFiles: evidence.files,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('GDirectBindingSeed.UnhandledException', [], 'G checker threw unexpectedly', normErr0(error)));
  }
}

async function readJson0(root, f, override) {
  if (override !== undefined) return { tag: 'accept', value: override, bytes: Buffer.from(`${JSON.stringify(override)}\n`) };
  try { const bytes = await readFile(path.join(root, f)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('GDirectBindingSeed.ReadOrParseFailed', [f], 'could not read or parse JSON', normErr0(error)); }
}
function manifest0(m) {
  const e = { kind: 'PNPGDirectBindingSeed0', version: VERSION, coordinate: COORD, status: 'g-direct-binding-seed-ready', gDirectBindingSeedReady: true, directCheckerBindingComplete: false, fullHistoricalGTheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false, directBindingBlockedByGaps: true };
  if (!plain0(m)) return reject0('GDirectBindingSeed.ManifestShape', [], 'manifest must be object');
  for (const [k, v] of Object.entries(e)) if (m[k] !== v) return reject0(`GDirectBindingSeed.Manifest.${k}`, [k], 'manifest field mismatch', { expected: v, actual: m[k] });
  const b = boundary0(m.claimBoundary, ['claimBoundary']); if (b.tag === 'reject') return b;
  const be = m.boundInventoryEntry;
  if (!plain0(be) || be.inventoryEntryId !== 'TL-025-G' || be.coverageEntryId !== 'COV-025-G' || be.closureEntryId !== 'DCC-025-G' || be.sourceLabel !== 'G' || be.expectedCoverageClass !== 'locked-nand-seed-surface' || be.expectedClosureStatus !== 'direct-binding-seed-upgrade-needed' || be.expectedNextDirectBindingSurface !== 'pcc-direct-bind-locked-nand-threshold0.mjs') return reject0('GDirectBindingSeed.BoundEntry', ['boundInventoryEntry'], 'bound row mismatch');
  if (!sameArray0(m.blockingGaps, CLOSURE_GAPS)) return reject0('GDirectBindingSeed.BlockingGaps', ['blockingGaps'], 'blocking gaps mismatch');
  for (const key of ['coveredGComponents', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[key]) || m[key].length === 0) return reject0('GDirectBindingSeed.ArrayMissing', [key], 'expected nonempty array');
  return { tag: 'accept' };
}
function inventory0(inv) {
  const row = inv?.inventoryEntries?.find?.((x) => x.id === 'TL-025-G');
  const c = String(row?.content ?? '');
  if (!plain0(row) || row.sourceLabel !== 'G' || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('GDirectBindingSeed.InventoryMismatch', ['inventory'], 'G inventory row mismatch');
  for (const needle of ['Locked NAND SAT embedding', 'macro truth tables', 'threshold', 'residual slack at most four']) if (!c.includes(needle)) return reject0('GDirectBindingSeed.InventoryContent', ['inventory', needle], 'G inventory content missing');
  return { tag: 'accept' };
}
function matrix0(mx) {
  const row = mx?.coverageEntries?.find?.((x) => x.id === 'COV-025-G');
  if (!plain0(row) || row.inventoryEntryId !== 'TL-025-G' || row.sourceLabel !== 'G' || row.coverageClass !== 'locked-nand-seed-surface' || row.directCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('GDirectBindingSeed.MatrixMismatch', ['matrix'], 'G coverage row mismatch');
  for (const obligation of ['OBL-009-LockedNANDSATSmallModels', 'OBL-010-ComplexityImplicationLedger']) if (!Array.isArray(row.relatedObligations) || !row.relatedObligations.includes(obligation)) return reject0('GDirectBindingSeed.MatrixObligationMissing', ['matrix', 'relatedObligations'], 'G matrix required obligation missing', { obligation });
  if (!Array.isArray(row.relatedGaps) || !row.relatedGaps.includes('GAP-001-UnrestrictedFinalSoundness')) return reject0('GDirectBindingSeed.MatrixGapMissing', ['matrix', 'relatedGaps'], 'G matrix must cite unrestricted soundness gap');
  return { tag: 'accept' };
}
function closure0(cl) {
  const row = cl?.closureEntries?.find?.((x) => x.id === 'DCC-025-G');
  if (!plain0(row) || row.coverageEntryId !== 'COV-025-G' || row.inventoryEntryId !== 'TL-025-G' || row.sourceLabel !== 'G' || row.currentCoverageClass !== 'locked-nand-seed-surface' || row.closureStatus !== 'direct-binding-seed-upgrade-needed' || row.nextDirectBindingSurface !== 'pcc-direct-bind-locked-nand-threshold0.mjs' || row.mayFlipDirectCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('GDirectBindingSeed.ClosureMismatch', ['closure'], 'G closure row mismatch');
  if (!sameArray0(row.blockingGaps, CLOSURE_GAPS)) return reject0('GDirectBindingSeed.ClosureGaps', ['closure', 'blockingGaps'], 'closure blocking gaps mismatch');
  return { tag: 'accept' };
}
function smallModels0(s) {
  if (!plain0(s) || s.kind !== 'PNPLockedNANDSATSmallModelsConfig0' || s.coordinate !== 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01' || s.satSmallModelsReady !== true || s.fullLockedNANDThresholdCoverageProved !== false || s.exhaustiveWithinConfiguredFormulaUniverse !== true) return reject0('GDirectBindingSeed.SmallModelsMismatch', ['smallModels'], 'locked-NAND small-model seed mismatch');
  const b = boundary0(s.claimBoundary, ['smallModels', 'claimBoundary']); if (b.tag === 'reject') return b;
  if (s.thresholdModel?.thresholdPredicate !== 'exactMinimum(finalLockedOutput) > baselineMinimum') return reject0('GDirectBindingSeed.ThresholdPredicate', ['smallModels', 'thresholdModel'], 'threshold predicate mismatch');
  return { tag: 'accept' };
}
function complexity0(c) {
  if (!plain0(c) || c.kind !== 'PNPComplexityLedger0' || c.coordinate !== 'PNP-COMPLEXITY-LEDGER-2026-06-27-01' || c.fullComplexityImplicationDischarged !== false || c.publicTheoremEmissionAllowedByLedger !== false) return reject0('GDirectBindingSeed.ComplexityLedgerOverclaim', ['complexity'], 'complexity ledger overclaim');
  return { tag: 'accept' };
}
function gaps0(g) {
  if (!plain0(g) || g.kind !== 'PNPGapLedger0' || g.fullGapClosureProved !== false || g.publicTheoremEmissionAllowedByLedger !== false) return reject0('GDirectBindingSeed.GapLedgerOverclaim', ['gaps'], 'gap ledger overclaim');
  const ids = new Set((g.gaps ?? []).map((x) => x.id));
  for (const gap of CLOSURE_GAPS) if (!ids.has(gap)) return reject0('GDirectBindingSeed.GapMissing', ['gaps'], 'required gap missing', { gap });
  return { tag: 'accept' };
}
function finite0(f) {
  if (!plain0(f) || f.kind !== 'PNPFiniteToUnboundedFamilyAudit0' || f.coordinate !== 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01' || f.uniformAllInputSizesCoverageProved !== false || f.polynomialUniformGeneratorProved !== false || f.unrestrictedFinalSoundnessDischarged !== false || f.publicTheoremEmissionAllowedByAudit !== false) return reject0('GDirectBindingSeed.FiniteAuditMismatch', ['finite'], 'finite-to-unbounded audit must remain non-discharging');
  return { tag: 'accept' };
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of paths) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('GDirectBindingSeed.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try { const info = await stat(safe); if (!info.isFile()) return reject0('GDirectBindingSeed.PathNotFile', ['evidenceSurfaces', rel], 'not a file'); const bytes = await readFile(safe); files.push({ path: rel, size: bytes.length, sha256: sha0(bytes) }); }
    catch (error) { return reject0('GDirectBindingSeed.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error)); }
  }
  return { tag: 'accept', files };
}
function boundary0(b, p) { if (!plain0(b)) return reject0('GDirectBindingSeed.BoundaryShape', p, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('GDirectBindingSeed.BoundaryMismatch', p, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function sha0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return sha0(Buffer.from(text, 'utf8')); }
function normErr0(e) { return { name: e?.name ?? 'Error', message: e?.message ?? String(e), code: e?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-direct-bind-locked-nand-threshold0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let o; try { o = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad G direct-binding seed CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const v = await CheckGDirectBindingSeed0(o); const rendered = JSON.stringify(v, null, 2); if (o.json || v.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(v.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
