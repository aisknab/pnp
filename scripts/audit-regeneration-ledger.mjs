#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'AuditRegenerationLedger0';
const VERSION = 0;
const LEDGER_PATH = 'artifacts/regeneration/REGENERATION_LEDGER.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/regeneration/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-REGENERATION-LEDGER-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_RECORD_IDS = [
  'status-dashboard',
  'trust-base',
  'theorem-bindings',
  'report-theorem-inventory',
  'report-theorem-coverage-matrix',
  'no-prose-only-theorem-policy',
  'proof-obligation-ledger',
  'gap-ledger',
  'finite-to-unbounded-family-audit',
  'minimal-kernel-cross-verify',
  'nand-semantics',
  'nand-small-models',
  'locked-nand-sat-small-models',
  'complexity-ledger',
  'no-hidden-oracle',
  'fresh-clone-verifier',
  'container-environment',
  'multi-platform-ci',
  'determinism-audit',
  'release-ladder',
  'regeneration-ledger',
];

export async function AuditRegenerationLedger0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const ledgerPath = options.ledgerPath ?? LEDGER_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const read = await readLedger0({ root, ledgerPath, override: options.ledgerOverride });
    if (read.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, read);
    const validation = validateLedger0(read.ledger);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, validation);
    const sourceDigest = await digestRecords0(root, read.ledger.records);
    if (sourceDigest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, sourceDigest);
    const outputDigest = await digestOutputPolicy0(root, read.ledger.records);
    if (outputDigest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, outputDigest);

    const deterministicRecordCount = read.ledger.records.filter((record) => record.deterministic === true).length;
    const runtimeGeneratedRecordCount = read.ledger.records.filter((record) => record.generatedAtRuntime === true).length;
    const committedOutputRecordCount = read.ledger.records.filter((record) => record.outputCommitted === true).length;

    return writeAndReturn0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'artifact-regeneration-ledger-accepted-under-public-review-boundary',
      ledgerPath,
      ledgerSha256: sha256Hex0(read.bytes),
      regenerationLedgerReady: true,
      fullArtifactRegenerationProved: false,
      publicTheoremEmissionAllowedByLedger: false,
      recordCount: read.ledger.records.length,
      deterministicRecordCount,
      runtimeGeneratedRecordCount,
      committedOutputRecordCount,
      sourceDigestLedgerSha256: sha256Text0(stableStringify0(sourceDigest.records)),
      outputPolicyDigestLedgerSha256: sha256Text0(stableStringify0(outputDigest.records)),
      records: sourceDigest.records,
      outputPolicyRecords: outputDigest.records,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('RegenerationLedger.UnhandledException', [], 'regeneration ledger audit threw unexpectedly', normalizeError0(error)));
  }
}

async function readLedger0({ root, ledgerPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', ledger: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, ledgerPath));
    return { tag: 'accept', ledger: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('RegenerationLedger.ReadOrParseFailed', [ledgerPath], 'could not read or parse regeneration ledger JSON', normalizeError0(error));
  }
}

function validateLedger0(ledger) {
  if (!plain0(ledger)) return reject0('RegenerationLedger.Shape', [], 'ledger must be an object');
  if (ledger.kind !== 'PNPArtifactRegenerationLedger0') return reject0('RegenerationLedger.Kind', ['kind'], 'ledger kind mismatch');
  if (ledger.version !== VERSION) return reject0('RegenerationLedger.Version', ['version'], 'ledger version mismatch');
  if (ledger.coordinate !== EXPECTED_COORDINATE) return reject0('RegenerationLedger.Coordinate', ['coordinate'], 'ledger coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: ledger.coordinate });
  if (ledger.status !== 'regeneration-ledger-ready') return reject0('RegenerationLedger.Status', ['status'], 'ledger status mismatch');
  if (ledger.regenerationLedgerReady !== true) return reject0('RegenerationLedger.ReadyFlag', ['regenerationLedgerReady'], 'regenerationLedgerReady must be true');
  if (ledger.fullArtifactRegenerationProved !== false) return reject0('RegenerationLedger.FullProofFlag', ['fullArtifactRegenerationProved'], 'seed regeneration ledger cannot claim full regeneration proof');
  if (ledger.publicTheoremEmissionAllowedByLedger !== false) return reject0('RegenerationLedger.PublicEmissionByLedgerFlag', ['publicTheoremEmissionAllowedByLedger'], 'regeneration ledger cannot allow public theorem emission');

  const boundary = validateBoundary0(ledger.claimBoundary);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(ledger.runtimeOutputPolicy)) return reject0('RegenerationLedger.RuntimePolicyShape', ['runtimeOutputPolicy'], 'runtimeOutputPolicy must be an object');
  if (ledger.runtimeOutputPolicy.generatedVerdictsCommitted !== false) return reject0('RegenerationLedger.GeneratedVerdictsCommitted', ['runtimeOutputPolicy', 'generatedVerdictsCommitted'], 'generated verdicts must not be committed by default');
  if (!nonempty0(ledger.runtimeOutputPolicy.generatedVerdictsLocation) || !nonempty0(ledger.runtimeOutputPolicy.rationale)) return reject0('RegenerationLedger.RuntimePolicyFields', ['runtimeOutputPolicy'], 'runtime output policy fields must be non-empty strings');

  if (!Array.isArray(ledger.records)) return reject0('RegenerationLedger.RecordsShape', ['records'], 'records must be an array');
  const actualIds = ledger.records.map((record) => record?.id);
  if (!sameArray0(actualIds, EXPECTED_RECORD_IDS)) return reject0('RegenerationLedger.RecordIds', ['records'], 'regeneration record ids must stay exact and ordered', { expected: EXPECTED_RECORD_IDS, actual: actualIds });
  const ids = new Set();
  for (let index = 0; index < ledger.records.length; index += 1) {
    const record = ledger.records[index];
    const recordPath = ['records', index];
    if (!plain0(record)) return reject0('RegenerationLedger.RecordShape', recordPath, 'record must be an object');
    if (ids.has(record.id)) return reject0('RegenerationLedger.DuplicateRecordId', [...recordPath, 'id'], 'record id must be unique', { id: record.id });
    ids.add(record.id);
    for (const field of ['id', 'kind', 'command', 'outputPath']) {
      if (!nonempty0(record[field])) return reject0('RegenerationLedger.RecordField', [...recordPath, field], 'record field must be a non-empty string');
    }
    const sourceCheck = validateStringArray0(record.sourceFiles, [...recordPath, 'sourceFiles'], true);
    if (sourceCheck.tag === 'reject') return sourceCheck;
    for (const field of ['deterministic', 'outputCommitted', 'generatedAtRuntime']) {
      if (typeof record[field] !== 'boolean') return reject0('RegenerationLedger.BooleanField', [...recordPath, field], `${field} must be boolean`);
    }
    if (record.outputCommitted === true && record.generatedAtRuntime === true) return reject0('RegenerationLedger.OutputPolicyConflict', recordPath, 'output cannot be both committed and generated-at-runtime-only');
  }

  if (!plain0(ledger.audit)) return reject0('RegenerationLedger.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = { checker: CHECKER, script: 'scripts/audit-regeneration-ledger.mjs', test: 'audits/regeneration-ledger0.test.mjs', expectedAcceptTag: 'accept' };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (ledger.audit[key] !== expected) return reject0('RegenerationLedger.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: ledger.audit[key] });
  }
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('RegenerationLedger.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('RegenerationLedger.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('RegenerationLedger.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('RegenerationLedger.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('RegenerationLedger.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

async function digestRecords0(root, records) {
  const out = [];
  for (const record of records) {
    const sourceFiles = [];
    for (const relativePath of record.sourceFiles) {
      const file = await digestFile0(root, relativePath, ['records', record.id, 'sourceFiles']);
      if (file.tag === 'reject') return file;
      sourceFiles.push(file);
    }
    out.push({ id: record.id, kind: record.kind, command: record.command, outputPath: record.outputPath, deterministic: record.deterministic, outputCommitted: record.outputCommitted, generatedAtRuntime: record.generatedAtRuntime, sourceFiles, sourceDigest: sha256Text0(stableStringify0(sourceFiles)) });
  }
  return { tag: 'accept', records: out };
}

async function digestOutputPolicy0(root, records) {
  const out = [];
  for (const record of records) {
    if (record.outputCommitted === true) {
      const file = await digestFile0(root, record.outputPath, ['records', record.id, 'outputPath']);
      if (file.tag === 'reject') return file;
      out.push({ id: record.id, outputPath: record.outputPath, outputCommitted: true, outputExists: true, outputSha256: file.sha256, outputSize: file.size });
    } else {
      out.push({ id: record.id, outputPath: record.outputPath, outputCommitted: false, generatedAtRuntime: record.generatedAtRuntime, outputExistsRequiredNow: false });
    }
  }
  return { tag: 'accept', records: out };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('RegenerationLedger.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('RegenerationLedger.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('RegenerationLedger.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('RegenerationLedger.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('RegenerationLedger.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('RegenerationLedger.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
  return { tag: 'accept' };
}

function safeJoin0(root, relativePath) {
  if (!nonempty0(relativePath) || path.isAbsolute(relativePath)) return null;
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
}

function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS] }; }
async function writeAndReturn0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const absoluteOutputPath = path.join(root, outputPath); await mkdir(path.dirname(absoluteOutputPath), { recursive: true }); await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function stableStringify0(value) { if (value === null || typeof value !== 'object') return JSON.stringify(value); if (Array.isArray(value)) return `[${value.map((entry) => stableStringify0(entry)).join(',')}]`; return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), ledgerPath: LEDGER_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--ledger') options.ledgerPath = requireValue0(argv, ++index, '--ledger');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}
function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node scripts/audit-regeneration-ledger.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/regeneration/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --ledger <path>    Regeneration ledger path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad regeneration ledger CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await AuditRegenerationLedger0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
