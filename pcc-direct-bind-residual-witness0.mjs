#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckRWDirectBindingGapSeed0';
const VERSION = 0;
const COORD = 'PNP-DIRECT-BIND-RW-RESIDUAL-WITNESS-GAP-SEED-2026-06-27-01';
const OUT = 'artifacts/direct-bind-residual-witness/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const GAPS = ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity'];
const FILES = {
  manifest: 'report-bindings/direct-bindings/RW_DIRECT_BINDING_GAP_SEED.json',
  inventory: 'report-bindings/REPORT_THEOREM_INVENTORY.json',
  matrix: 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json',
  closure: 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json',
  gaps: 'proof-obligations/GAP_LEDGER.json',
  finite: 'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json',
  status: 'PNP_STATUS.json'
};

export async function CheckRWDirectBindingGapSeed0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const reads = {};
    for (const [k, f] of Object.entries(FILES)) {
      const read = await readJson0(root, options[`${k}Path`] ?? f, options[`${k}Override`]);
      if (read.tag === 'reject') return write0(root, outputPath, writeOutput, read);
      reads[k] = read;
    }
    for (const check of [manifest0(reads.manifest.value), inventory0(reads.inventory.value), matrix0(reads.matrix.value), closure0(reads.closure.value), gaps0(reads.gaps.value), finite0(reads.finite.value), status0(reads.status.value)]) if (check.tag === 'reject') return write0(root, outputPath, writeOutput, check);
    const evidence = await digestEvidence0(root, reads.manifest.value.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);
    return write0(root, outputPath, writeOutput, { tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD, claimStatus: 'rw-direct-binding-gap-seed-accepted-under-public-review-boundary', rwDirectBindingGapSeedReady: true, directBindingBlockedByGaps: true, boundInventoryEntryId: 'TL-014-RW', boundCoverageEntryId: 'COV-014-RW', boundClosureEntryId: 'DCC-014-RW', blockingGaps: [...GAPS], directCheckerBindingComplete: false, fullHistoricalRWTheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false, evidenceFileCount: evidence.files.length, evidenceDigestSha256: shaText0(stable0(evidence.files)), evidenceFiles: evidence.files, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS], outputPath: writeOutput ? outputPath : null });
  } catch (error) { return write0(root, outputPath, writeOutput, reject0('RWDirectBindingGapSeed.UnhandledException', [], 'RW checker threw unexpectedly', normErr0(error))); }
}

async function readJson0(root, f, override) { if (override !== undefined) return { tag: 'accept', value: override, bytes: Buffer.from(`${JSON.stringify(override)}\n`) }; try { const bytes = await readFile(path.join(root, f)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('RWDirectBindingGapSeed.ReadOrParseFailed', [f], 'could not read or parse JSON', normErr0(error)); } }
function manifest0(m) { if (!plain0(m)) return reject0('RWDirectBindingGapSeed.ManifestShape', [], 'manifest must be object'); const exact = { kind: 'PNPRWDirectBindingGapSeed0', version: VERSION, coordinate: COORD, status: 'rw-direct-binding-gap-seed-ready', rwDirectBindingGapSeedReady: true, directCheckerBindingComplete: false, fullHistoricalRWTheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false, directBindingBlockedByGaps: true }; for (const [k, v] of Object.entries(exact)) if (m[k] !== v) return reject0(`RWDirectBindingGapSeed.Manifest.${k}`, [k], 'manifest field mismatch', { expected: v, actual: m[k] }); const b = boundary0(m.claimBoundary, ['claimBoundary']); if (b.tag === 'reject') return b; const be = m.boundInventoryEntry; if (!plain0(be) || be.inventoryEntryId !== 'TL-014-RW' || be.coverageEntryId !== 'COV-014-RW' || be.closureEntryId !== 'DCC-014-RW' || be.sourceLabel !== 'RW' || be.expectedCoverageClass !== 'uniformity-gap-surface' || be.expectedClosureStatus !== 'blocked-by-unrestricted-final-soundness' || be.expectedNextDirectBindingSurface !== 'pcc-direct-bind-residual-witness0.mjs') return reject0('RWDirectBindingGapSeed.BoundEntry', ['boundInventoryEntry'], 'bound row mismatch'); if (!sameArray0(m.blockingGaps, GAPS)) return reject0('RWDirectBindingGapSeed.BlockingGaps', ['blockingGaps'], 'blocking gaps mismatch'); for (const key of ['coveredRWComponents', 'evidenceSurfaces', 'nonClaims']) { const s = stringArray0(m[key], [key]); if (s.tag === 'reject') return s; } return { tag: 'accept' }; }
function inventory0(inv) { const row = inv?.inventoryEntries?.find?.((x) => x.id === 'TL-014-RW'); if (!plain0(row) || row.sourceLabel !== 'RW' || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('RWDirectBindingGapSeed.InventoryMismatch', ['inventory'], 'RW inventory row mismatch'); const c = String(row.content); for (const needle of ['MuBridge', 'SpanPolicy', 'SaturatePositive', 'RankWF', 'BCELReady']) if (!c.includes(needle)) return reject0('RWDirectBindingGapSeed.InventoryContent', ['inventory', needle], 'RW inventory content missing'); return { tag: 'accept' }; }
function matrix0(mx) { const row = mx?.coverageEntries?.find?.((x) => x.id === 'COV-014-RW'); if (!plain0(row) || row.inventoryEntryId !== 'TL-014-RW' || row.sourceLabel !== 'RW' || row.coverageClass !== 'uniformity-gap-surface' || row.directCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('RWDirectBindingGapSeed.MatrixMismatch', ['matrix'], 'RW coverage row mismatch'); if (!Array.isArray(row.relatedGaps) || !row.relatedGaps.includes(GAPS[0])) return reject0('RWDirectBindingGapSeed.MatrixGapMissing', ['matrix', 'relatedGaps'], 'RW matrix must cite unrestricted soundness gap'); return { tag: 'accept' }; }
function closure0(cl) { const row = cl?.closureEntries?.find?.((x) => x.id === 'DCC-014-RW'); if (!plain0(row) || row.coverageEntryId !== 'COV-014-RW' || row.inventoryEntryId !== 'TL-014-RW' || row.sourceLabel !== 'RW' || row.currentCoverageClass !== 'uniformity-gap-surface' || row.closureStatus !== 'blocked-by-unrestricted-final-soundness' || row.nextDirectBindingSurface !== 'pcc-direct-bind-residual-witness0.mjs' || row.mayFlipDirectCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('RWDirectBindingGapSeed.ClosureMismatch', ['closure'], 'RW closure row mismatch'); if (!sameArray0(row.blockingGaps, GAPS)) return reject0('RWDirectBindingGapSeed.ClosureGaps', ['closure', 'blockingGaps'], 'closure blocking gaps mismatch'); return { tag: 'accept' }; }
function gaps0(g) { if (!plain0(g) || g.kind !== 'PNPGapLedger0' || g.fullGapClosureProved !== false || g.publicTheoremEmissionAllowedByLedger !== false) return reject0('RWDirectBindingGapSeed.GapLedgerOverclaim', ['gaps'], 'gap ledger overclaim'); const ids = new Set((g.gaps ?? []).map((x) => x.id)); for (const gap of GAPS) if (!ids.has(gap)) return reject0('RWDirectBindingGapSeed.GapMissing', ['gaps'], 'required gap missing', { gap }); return { tag: 'accept' }; }
function finite0(f) { if (!plain0(f) || f.kind !== 'PNPFiniteToUnboundedFamilyAudit0' || f.coordinate !== 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01' || f.uniformAllInputSizesCoverageProved !== false || f.polynomialUniformGeneratorProved !== false || f.unrestrictedFinalSoundnessDischarged !== false || f.publicTheoremEmissionAllowedByAudit !== false) return reject0('RWDirectBindingGapSeed.FiniteAuditMismatch', ['finite'], 'finite-to-unbounded audit must remain non-discharging'); return { tag: 'accept' }; }
function status0(s) { if (!plain0(s) || s.kind !== 'PNPStatus0' || s.rwDirectBindingGapSeedCoordinate !== COORD) return reject0('RWDirectBindingGapSeed.StatusCoordinate', ['status'], 'status must bind RW coordinate'); return boundary0(s, ['status']); }
async function digestEvidence0(root, paths) { const files = []; for (const rel of paths) { const safe = safeJoin0(root, rel); if (safe === null) return reject0('RWDirectBindingGapSeed.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path'); try { const info = await stat(safe); if (!info.isFile()) return reject0('RWDirectBindingGapSeed.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(safe); files.push({ path: rel, size: bytes.length, sha256: sha0(bytes) }); } catch (error) { return reject0('RWDirectBindingGapSeed.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error)); } } return { tag: 'accept', files }; }
function boundary0(b, p) { if (!plain0(b)) return reject0('RWDirectBindingGapSeed.BoundaryShape', p, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('RWDirectBindingGapSeed.BoundaryMismatch', p, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function stringArray0(v, p) { if (!Array.isArray(v) || v.length === 0 || v.some((x) => typeof x !== 'string' || x.length === 0)) return reject0('RWDirectBindingGapSeed.StringArray', p, 'expected nonempty string array'); return { tag: 'accept' }; }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function sha0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return sha0(Buffer.from(text, 'utf8')); }
function normErr0(e) { return { name: e?.name ?? 'Error', message: e?.message ?? String(e), code: e?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-direct-bind-residual-witness0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let o; try { o = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad RW direct-binding gap seed CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const v = await CheckRWDirectBindingGapSeed0(o); const rendered = JSON.stringify(v, null, 2); if (o.json || v.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(v.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
