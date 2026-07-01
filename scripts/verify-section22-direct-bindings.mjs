#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckSection22DirectBindingRunner0';
const VERSION = 0;
const COORD = 'PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01';
const INDEX_COORD = 'PNP-DIRECT-BINDING-INDEX-2026-06-27-01';
const INDEX = 'report-bindings/direct-bindings/DIRECT_BINDING_INDEX.json';
const OUTPUT = 'artifacts/section22-direct-bindings/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export async function RunSection22DirectBindings0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUTPUT;
  const writeOutput = options.writeOutput ?? true;
  const includeRowTests = options.includeRowTests ?? true;
  try {
    const indexRead = await readJson0(root, options.indexPath ?? INDEX, options.indexOverride);
    if (indexRead.tag === 'reject') return write0(root, outputPath, writeOutput, indexRead);
    const index = indexRead.value;
    const shape = validateIndex0(index);
    if (shape.tag === 'reject') return write0(root, outputPath, writeOutput, shape);

    const rowResults = [];
    let checkerAcceptCount = 0;
    let testAcceptCount = 0;
    for (let i = 0; i < index.entries.length; i += 1) {
      const entryResult = normalizeEntry0(index.entries[i], i);
      if (entryResult.tag === 'reject') return write0(root, outputPath, writeOutput, entryResult);
      const entry = entryResult.entry;
      const checkerStep = await runStep0({ id: `section22:${entry.sourceLabel}:checker`, args: [entry.checkerPath, '--json'], root, kind: 'json' });
      if (checkerStep.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0(checkerStep.coord ?? 'Section22DirectBindingRunner.CheckerReject', [entry.sourceLabel, entry.checkerPath], 'row checker process failed', { entry, checkerStep, rowResults }));
      const jsonCheck = validateCheckerJson0(entry, checkerStep.json);
      if (jsonCheck.tag === 'reject') return write0(root, outputPath, writeOutput, jsonCheck);
      checkerAcceptCount += 1;
      let testStep = null;
      if (includeRowTests) {
        testStep = await runStep0({ id: `section22:${entry.sourceLabel}:test`, args: ['--test', entry.testPath], root, kind: 'process' });
        if (testStep.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0(testStep.coord ?? 'Section22DirectBindingRunner.TestReject', [entry.sourceLabel, entry.testPath], 'row test process failed', { entry, testStep, rowResults }));
        testAcceptCount += 1;
      }
      rowResults.push({
        sourceLabel: entry.sourceLabel,
        inventoryEntryId: entry.inventoryEntryId,
        coverageEntryId: entry.coverageEntryId,
        closureEntryId: entry.closureEntryId,
        manifestPath: entry.manifestPath,
        checkerPath: entry.checkerPath,
        testPath: entry.testPath,
        checkerTag: checkerStep.json.tag,
        checkerCoordinate: checkerStep.json.coordinate ?? null,
        directCheckerBindingComplete: checkerStep.json.directCheckerBindingComplete ?? null,
        publicTheoremEmissionAllowed: checkerStep.json.publicTheoremEmissionAllowed,
        finalTheoremReady: checkerStep.json.finalTheoremReady,
        checkerStdoutSha256: checkerStep.stdoutSha256,
        checkerStderrSha256: checkerStep.stderrSha256,
        testExitCode: testStep?.exitCode ?? null,
        testStdoutSha256: testStep?.stdoutSha256 ?? null,
        testStderrSha256: testStep?.stderrSha256 ?? null
      });
    }

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'section22-direct-binding-runner-accepted-under-public-review-boundary',
      directBindingIndexCoordinate: INDEX_COORD,
      section22RowsExecuted: true,
      section22RowCount: index.entries.length,
      checkerAcceptCount,
      testAcceptCount,
      includeRowTests,
      allSection22RowCheckersAccepted: checkerAcceptCount === index.entries.length,
      allSection22RowTestsAccepted: includeRowTests ? testAcceptCount === index.entries.length : null,
      directCheckerBindingCompleteCount: rowResults.filter((r) => r.directCheckerBindingComplete === true).length,
      publicTheoremEmissionAllowedByRunner: false,
      rowResults,
      rowResultsDigestSha256: shaText0(stable0(rowResults)),
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('Section22DirectBindingRunner.UnhandledException', [], 'Section 22 direct-binding runner threw unexpectedly', normErr0(error)));
  }
}

function validateIndex0(index) {
  if (!plain0(index) || index.kind !== 'PNPDirectBindingIndex0' || index.coordinate !== INDEX_COORD || index.section22RowsIndexed !== true || index.allSection22RowsHaveExecutableSurface !== true || index.allSection22RowsDirectCheckerComplete !== false || index.publicTheoremEmissionAllowedByIndex !== false) return reject0('Section22DirectBindingRunner.IndexShape', [INDEX], 'direct-binding index shape mismatch');
  if (!Array.isArray(index.entries) || index.entries.length !== 27 || index.expectedEntryCount !== 27) return reject0('Section22DirectBindingRunner.EntryCount', [INDEX, 'entries'], 'direct-binding index entry count mismatch');
  const b = boundary0(index.claimBoundary, [INDEX, 'claimBoundary']);
  if (b.tag === 'reject') return b;
  return { tag: 'accept' };
}
function normalizeEntry0(raw, i) {
  if (!Array.isArray(raw) || raw.length !== 7 || raw.some((v) => typeof v !== 'string' || v.length === 0)) return reject0('Section22DirectBindingRunner.BadEntry', [INDEX, 'entries', i], 'index row must be seven non-empty strings');
  const [inventoryEntryId, coverageEntryId, closureEntryId, sourceLabel, manifestPath, checkerPath, testPath] = raw;
  return { tag: 'accept', entry: { inventoryEntryId, coverageEntryId, closureEntryId, sourceLabel, manifestPath, checkerPath, testPath } };
}
function validateCheckerJson0(entry, json) {
  if (!plain0(json) || json.tag !== 'accept') return reject0('Section22DirectBindingRunner.RowCheckerTag', [entry.sourceLabel, entry.checkerPath], 'row checker JSON did not accept', { actualTag: json?.tag ?? null });
  if (json.directCheckerBindingComplete !== false) return reject0('Section22DirectBindingRunner.RowOverclaim', [entry.sourceLabel, 'directCheckerBindingComplete'], 'row checker overclaimed direct binding completion', { actual: json.directCheckerBindingComplete });
  if (json.publicTheoremEmissionAllowedByBinding !== false && json.publicTheoremEmissionAllowedByIndex !== false) return reject0('Section22DirectBindingRunner.RowBindingEmission', [entry.sourceLabel, 'publicTheoremEmissionAllowedByBinding'], 'row checker overclaimed theorem emission by binding', { actual: json.publicTheoremEmissionAllowedByBinding ?? json.publicTheoremEmissionAllowedByIndex });
  const boundary = boundary0(json, [entry.sourceLabel, 'boundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const [field, expected] of [['boundInventoryEntryId', entry.inventoryEntryId], ['boundCoverageEntryId', entry.coverageEntryId], ['boundClosureEntryId', entry.closureEntryId]]) {
    if (json[field] !== expected) return reject0('Section22DirectBindingRunner.RowBoundIdMismatch', [entry.sourceLabel, field], 'row checker bound id mismatch', { expected, actual: json[field] });
  }
  return { tag: 'accept' };
}
async function readJson0(root, f, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(path.join(root, f)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')) }; }
  catch (error) { return reject0('Section22DirectBindingRunner.ReadOrParseFailed', [f], 'could not read or parse JSON', normErr0(error)); }
}
function runStep0({ id, args, root, kind }) {
  return new Promise((resolve) => {
    const child = spawn(process.execPath, args, { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    let settled = false;
    child.stdout.on('data', (chunk) => { stdout += chunk.toString('utf8'); });
    child.stderr.on('data', (chunk) => { stderr += chunk.toString('utf8'); });
    child.on('error', (error) => { if (settled) return; settled = true; resolve({ tag: 'reject', id, kind, coord: 'Process.SpawnFailed', path: [id], command: [process.execPath, ...args].join(' '), witness: normErr0(error) }); });
    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      const base = { id, kind, command: [process.execPath, ...args].join(' '), exitCode: code, stdoutSha256: shaText0(stdout), stderrSha256: shaText0(stderr), stdoutPreview: preview0(stdout), stderrPreview: preview0(stderr) };
      if (code !== 0) return resolve({ tag: 'reject', ...base, coord: 'Process.NonZeroExit', path: [id], witness: { reason: 'process exited non-zero', code } });
      if (kind === 'json') {
        try { return resolve({ tag: 'accept', ...base, json: JSON.parse(stdout) }); }
        catch (error) { return resolve({ tag: 'reject', ...base, coord: 'Process.BadJson', path: [id], witness: normErr0(error) }); }
      }
      return resolve({ tag: 'accept', ...base });
    });
  });
}
function boundary0(b, p) { if (!plain0(b)) return reject0('Section22DirectBindingRunner.BoundaryShape', p, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('Section22DirectBindingRunner.BoundaryMismatch', p, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function preview0(text) { return text ? (text.length > 4000 ? `${text.slice(0, 4000)}\n...[truncated ${text.length - 4000} bytes]` : text) : ''; }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function shaText0(text) { return createHash('sha256').update(String(text), 'utf8').digest('hex'); }
function normErr0(e) { return { name: e?.name ?? 'Error', message: e?.message ?? String(e), code: e?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUTPUT, writeOutput: true, json: false, includeRowTests: true }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--skip-row-tests') o.includeRowTests = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--index') o.indexPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node scripts/verify-section22-direct-bindings.mjs [--json] [--no-write] [--skip-row-tests] [--root <path>] [--output <path>] [--index <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let o; try { o = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad Section 22 direct-binding runner CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const v = await RunSection22DirectBindings0(o); const rendered = JSON.stringify(v, null, 2); if (o.json || v.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(v.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
