#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckFinalTheoremBoundarySeed0';
const VERSION = 0;
const COORD = 'PNP-DIRECT-BIND-FINAL-THEOREM-BOUNDARY-SEED-2026-06-27-01';
const OUT = 'artifacts/direct-bind-final-theorem-boundary/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const GAPS = ['GAP-001-UnrestrictedFinalSoundness', 'GAP-002-ExternalReviewAcceptance'];
const FILES = {
  manifest: 'report-bindings/direct-bindings/FINAL_DIRECT_BINDING_BOUNDARY_SEED.json',
  inventory: 'report-bindings/REPORT_THEOREM_INVENTORY.json',
  matrix: 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json',
  closure: 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json',
  bindings: 'report-bindings/REPORT_THEOREM_BINDINGS.json',
  ladder: 'release/RELEASE_LADDER.json',
  gaps: 'proof-obligations/GAP_LEDGER.json',
  status: 'PNP_STATUS.json'
};

export async function CheckFinalTheoremBoundarySeed0(options = {}) {
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
    for (const check of [manifest0(reads.manifest.value), inventory0(reads.inventory.value), matrix0(reads.matrix.value), closure0(reads.closure.value), bindings0(reads.bindings.value), ladder0(reads.ladder.value), gaps0(reads.gaps.value), boundary0(reads.status.value, ['status'])]) {
      if (check.tag === 'reject') return write0(root, outputPath, writeOutput, check);
    }
    const evidence = await digestEvidence0(root, reads.manifest.value.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);
    return write0(root, outputPath, writeOutput, {
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD,
      claimStatus: 'final-theorem-boundary-seed-accepted-under-public-review-boundary',
      finalTheoremBoundarySeedReady: true, releaseBoundaryBlocked: true,
      boundInventoryEntryId: 'TL-026-Final', boundCoverageEntryId: 'COV-026-Final', boundClosureEntryId: 'DCC-026-Final',
      coverageClass: 'release-critical-boundary-surface', closureStatus: 'release-boundary-blocked', blockingGaps: [...GAPS],
      directCheckerBindingComplete: false, fullHistoricalFinalTheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false,
      publicTheoremActivationBySeed: false, releaseLadderTransitionActivated: false,
      evidenceFileCount: evidence.files.length, evidenceDigestSha256: shaText0(stable0(evidence.files)), evidenceFiles: evidence.files,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('FinalTheoremBoundarySeed.UnhandledException', [], 'Final boundary checker threw unexpectedly', normErr0(error)));
  }
}

async function readJson0(root, f, override) {
  if (override !== undefined) return { tag: 'accept', value: override, bytes: Buffer.from(`${JSON.stringify(override)}\n`) };
  try { const bytes = await readFile(path.join(root, f)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('FinalTheoremBoundarySeed.ReadOrParseFailed', [f], 'could not read or parse JSON', normErr0(error)); }
}
function manifest0(m) {
  const e = { kind: 'PNPFinalDirectBindingBoundarySeed0', version: VERSION, coordinate: COORD, status: 'final-theorem-boundary-seed-ready', finalTheoremBoundarySeedReady: true, directCheckerBindingComplete: false, fullHistoricalFinalTheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false, releaseBoundaryBlocked: true };
  if (!plain0(m)) return reject0('FinalTheoremBoundarySeed.ManifestShape', [], 'manifest must be object');
  for (const [k, v] of Object.entries(e)) if (m[k] !== v) return reject0(`FinalTheoremBoundarySeed.Manifest.${k}`, [k], 'manifest field mismatch', { expected: v, actual: m[k] });
  const b = boundary0(m.claimBoundary, ['claimBoundary']); if (b.tag === 'reject') return b;
  const be = m.boundInventoryEntry;
  if (!plain0(be) || be.inventoryEntryId !== 'TL-026-Final' || be.coverageEntryId !== 'COV-026-Final' || be.closureEntryId !== 'DCC-026-Final' || be.sourceLabel !== 'Final' || be.expectedCoverageClass !== 'release-critical-boundary-surface' || be.expectedClosureStatus !== 'release-boundary-blocked' || be.expectedNextDirectBindingSurface !== 'pcc-direct-bind-final-theorem-boundary0.mjs') return reject0('FinalTheoremBoundarySeed.BoundEntry', ['boundInventoryEntry'], 'bound row mismatch');
  if (!sameArray0(m.blockingGaps, GAPS)) return reject0('FinalTheoremBoundarySeed.BlockingGaps', ['blockingGaps'], 'blocking gaps mismatch');
  for (const key of ['coveredFinalComponents', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[key]) || m[key].length === 0) return reject0('FinalTheoremBoundarySeed.ArrayMissing', [key], 'expected nonempty array');
  return { tag: 'accept' };
}
function inventory0(inv) {
  const row = inv?.inventoryEntries?.find?.((x) => x.id === 'TL-026-Final');
  const c = String(row?.content ?? '');
  if (!plain0(row) || row.sourceLabel !== 'Final' || row.coverageStatus !== 'release-critical-boundary-represented' || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('FinalTheoremBoundarySeed.InventoryMismatch', ['inventory'], 'Final inventory row mismatch');
  for (const needle of ['Framework match', 'SAT decision', 'accepted package implies P = NP']) if (!c.includes(needle)) return reject0('FinalTheoremBoundarySeed.InventoryContent', ['inventory', needle], 'Final inventory content missing');
  return { tag: 'accept' };
}
function matrix0(mx) {
  const row = mx?.coverageEntries?.find?.((x) => x.id === 'COV-026-Final');
  if (!plain0(row) || row.inventoryEntryId !== 'TL-026-Final' || row.sourceLabel !== 'Final' || row.coverageClass !== 'release-critical-boundary-surface' || row.coverageStatus !== 'represented-by-explicit-ledger-surface' || row.directCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('FinalTheoremBoundarySeed.MatrixMismatch', ['matrix'], 'Final coverage row mismatch');
  for (const obligation of ['OBL-013-ReleaseLadderNonActivation', 'OBL-014-UnrestrictedFinalSoundnessBlocked']) if (!Array.isArray(row.relatedObligations) || !row.relatedObligations.includes(obligation)) return reject0('FinalTheoremBoundarySeed.MatrixObligationMissing', ['matrix', 'relatedObligations'], 'Final matrix required obligation missing', { obligation });
  if (!Array.isArray(row.relatedGaps) || !row.relatedGaps.includes(GAPS[0])) return reject0('FinalTheoremBoundarySeed.MatrixGapMissing', ['matrix', 'relatedGaps'], 'Final matrix must cite unrestricted soundness gap');
  return { tag: 'accept' };
}
function closure0(cl) {
  const row = cl?.closureEntries?.find?.((x) => x.id === 'DCC-026-Final');
  if (!plain0(row) || row.coverageEntryId !== 'COV-026-Final' || row.inventoryEntryId !== 'TL-026-Final' || row.sourceLabel !== 'Final' || row.currentCoverageClass !== 'release-critical-boundary-surface' || row.closureStatus !== 'release-boundary-blocked' || row.nextDirectBindingSurface !== 'pcc-direct-bind-final-theorem-boundary0.mjs' || row.mayFlipDirectCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('FinalTheoremBoundarySeed.ClosureMismatch', ['closure'], 'Final closure row mismatch');
  if (!sameArray0(row.blockingGaps, GAPS)) return reject0('FinalTheoremBoundarySeed.ClosureGaps', ['closure', 'blockingGaps'], 'closure blocking gaps mismatch');
  return { tag: 'accept' };
}
function bindings0(b) {
  if (!plain0(b) || b.kind !== 'PNPReportTheoremBindings0' || b.coordinate !== 'REPORT-THEOREM-BINDINGS-2026-06-27-01') return reject0('FinalTheoremBoundarySeed.BindingsMismatch', ['bindings'], 'theorem bindings ledger mismatch');
  const group = b.bindingGroups?.['final-release-boundary'];
  if (!plain0(group) || !String(group.bindingStrength ?? '').includes('public theorem emission remains disabled')) return reject0('FinalTheoremBoundarySeed.FinalReleaseGroup', ['bindings', 'bindingGroups', 'final-release-boundary'], 'final-release binding group must preserve public-emission boundary');
  const thm = b.theoremBindings?.find?.((x) => x.id === 'THM-1-1');
  if (!plain0(thm) || thm.publicEmissionEffect !== 'none' || thm.dischargesPublicTheorem !== false || !Array.isArray(thm.bindingGroupIds) || !thm.bindingGroupIds.includes('final-release-boundary')) return reject0('FinalTheoremBoundarySeed.TheoremBinding', ['bindings', 'theoremBindings', 'THM-1-1'], 'final theorem binding must be non-emitting and boundary-bound');
  return boundary0(b.claimBoundary, ['bindings', 'claimBoundary']);
}
function ladder0(l) {
  if (!plain0(l) || l.kind !== 'PNPReleaseLadder0' || l.coordinate !== 'PNP-RELEASE-LADDER-2026-06-27-01' || l.publicTheoremEmissionAllowedByLadder !== false || l.finalTheoremReadyByLadder !== false || !sameArray0(l.activeFinalNodeIdsByLadder, [])) return reject0('FinalTheoremBoundarySeed.LadderOverclaim', ['ladder'], 'release ladder overclaim');
  const b = boundary0(l.claimBoundary, ['ladder', 'claimBoundary']); if (b.tag === 'reject') return b;
  for (const [id, blocker] of [['UnrestrictedFinalSoundnessRepresented', 'Release.UnrestrictedFinalSoundness'], ['InternalTheoremActivationCandidate', 'Release.UnrestrictedFinalSoundness'], ['PublicTheoremEmissionCandidate', 'ExternalReview.Acceptance']]) {
    const row = l.ladder?.find?.((x) => x.id === id);
    if (!plain0(row) || row.state !== 'blocked' || row.blocker !== blocker) return reject0('FinalTheoremBoundarySeed.LadderBlockedState', ['ladder', id], 'required blocked ladder state mismatch', { expectedBlocker: blocker });
  }
  return { tag: 'accept' };
}
function gaps0(g) {
  if (!plain0(g) || g.kind !== 'PNPGapLedger0' || g.fullGapClosureProved !== false || g.publicTheoremEmissionAllowedByLedger !== false) return reject0('FinalTheoremBoundarySeed.GapLedgerOverclaim', ['gaps'], 'gap ledger overclaim');
  const ids = new Set((g.gaps ?? []).map((x) => x.id));
  for (const gap of GAPS) if (!ids.has(gap)) return reject0('FinalTheoremBoundarySeed.GapMissing', ['gaps'], 'required release gap missing', { gap });
  return { tag: 'accept' };
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of paths) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('FinalTheoremBoundarySeed.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try { const info = await stat(safe); if (!info.isFile()) return reject0('FinalTheoremBoundarySeed.PathNotFile', ['evidenceSurfaces', rel], 'not a file'); const bytes = await readFile(safe); files.push({ path: rel, size: bytes.length, sha256: sha0(bytes) }); }
    catch (error) { return reject0('FinalTheoremBoundarySeed.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error)); }
  }
  return { tag: 'accept', files };
}
function boundary0(b, p) { if (!plain0(b)) return reject0('FinalTheoremBoundarySeed.BoundaryShape', p, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('FinalTheoremBoundarySeed.BoundaryMismatch', p, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function sha0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return sha0(Buffer.from(text, 'utf8')); }
function normErr0(e) { return { name: e?.name ?? 'Error', message: e?.message ?? String(e), code: e?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-direct-bind-final-theorem-boundary0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let o; try { o = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad Final theorem boundary seed CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const v = await CheckFinalTheoremBoundarySeed0(o); const rendered = JSON.stringify(v, null, 2); if (o.json || v.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(v.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
