#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckProofObligationLedger0';
const VERSION = 0;
const LEDGER_PATH = 'proof-obligations/OBLIGATION_LEDGER.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/proof-obligations/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const ALLOWED_STATUSES = ['machine-checked-seed', 'represented-not-activated', 'explicit-external-trust', 'blocked-release-obligation'];
const EXPECTED_OBLIGATION_IDS = [
  'OBL-001-ClaimBoundaryNonActivation',
  'OBL-002-TrustBaseExplicit',
  'OBL-003-TrustBaseShrinkPlan',
  'OBL-004-TheoremToCheckerBindings',
  'OBL-005-MinimalKernelCrossVerification',
  'OBL-006-CheckerSoundnessSeedAudits',
  'OBL-007-NANDDirectWireSemantics',
  'OBL-008-NANDSmallModels',
  'OBL-009-LockedNANDSATSmallModels',
  'OBL-010-ComplexityImplicationLedger',
  'OBL-011-NoHiddenOracleSourceSurface',
  'OBL-012-ReproducibilityStack',
  'OBL-013-ReleaseLadderNonActivation',
  'OBL-014-UnrestrictedFinalSoundnessBlocked',
  'OBL-015-FiniteToUnboundedFamilyAudit',
  'OBL-016-BaseDirectBindingSeed',
  'OBL-017-CHGDirectBindingSeed',
];

export async function CheckProofObligationLedger0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const ledgerPath = options.ledgerPath ?? LEDGER_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  try {
    const read = await readLedger0(root, ledgerPath, options.ledgerOverride);
    if (read.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, read);
    const validation = validateLedger0(read.ledger);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, validation);
    const digest = await digestObligations0(root, read.ledger.obligations);
    if (digest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, digest);
    return writeAndReturn0(root, outputPath, writeOutput, {
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: EXPECTED_COORDINATE,
      claimStatus: 'proof-obligation-ledger-accepted-under-public-review-boundary', ledgerPath, ledgerSha256: sha256Hex0(read.bytes),
      proofObligationLedgerReady: true, fullProofObligationDischargeProved: false, publicTheoremEmissionAllowedByLedger: false,
      obligationCount: read.ledger.obligations.length, obligationIds: [...EXPECTED_OBLIGATION_IDS], statusCounts: countBy0(read.ledger.obligations.map((obligation) => obligation.status)), sourceFileCount: digest.sourceFileCount, testFileCount: digest.testFileCount, obligationDigestLedgerSha256: sha256Text0(stableStringify0(digest.obligationDigests)), obligationDigests: digest.obligationDigests,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS], outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('ProofObligationLedger.UnhandledException', [], 'proof obligation ledger checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readLedger0(root, ledgerPath, override) {
  if (override !== undefined) return { tag: 'accept', ledger: override, bytes: Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8') };
  try { const bytes = await readFile(path.join(root, ledgerPath)); return { tag: 'accept', ledger: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('ProofObligationLedger.ReadOrParseFailed', [ledgerPath], 'could not read or parse proof obligation ledger JSON', normalizeError0(error)); }
}

function validateLedger0(ledger) {
  if (!plain0(ledger)) return reject0('ProofObligationLedger.Shape', [], 'ledger must be an object');
  if (ledger.kind !== 'PNPProofObligationLedger0') return reject0('ProofObligationLedger.Kind', ['kind'], 'ledger kind mismatch');
  if (ledger.version !== VERSION) return reject0('ProofObligationLedger.Version', ['version'], 'ledger version mismatch');
  if (ledger.coordinate !== EXPECTED_COORDINATE) return reject0('ProofObligationLedger.Coordinate', ['coordinate'], 'ledger coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: ledger.coordinate });
  if (ledger.status !== 'proof-obligation-ledger-ready') return reject0('ProofObligationLedger.Status', ['status'], 'ledger status mismatch');
  if (ledger.proofObligationLedgerReady !== true) return reject0('ProofObligationLedger.ReadyFlag', ['proofObligationLedgerReady'], 'proofObligationLedgerReady must be true');
  if (ledger.fullProofObligationDischargeProved !== false) return reject0('ProofObligationLedger.FullDischargeFlag', ['fullProofObligationDischargeProved'], 'seed ledger cannot claim full proof obligation discharge');
  if (ledger.publicTheoremEmissionAllowedByLedger !== false) return reject0('ProofObligationLedger.PublicEmissionByLedger', ['publicTheoremEmissionAllowedByLedger'], 'ledger cannot allow public theorem emission');
  const boundary = validateBoundary0(ledger.claimBoundary);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(ledger.hashPolicy) || ledger.hashPolicy.mode !== 'checker-computed-source-digests' || ledger.hashPolicy.algorithm !== 'SHA256' || !nonempty0(ledger.hashPolicy.rationale)) return reject0('ProofObligationLedger.HashPolicy', ['hashPolicy'], 'hash policy mismatch');
  if (!plain0(ledger.obligationStatusLegend)) return reject0('ProofObligationLedger.StatusLegendShape', ['obligationStatusLegend'], 'obligationStatusLegend must be an object');
  for (const status of ALLOWED_STATUSES) if (!nonempty0(ledger.obligationStatusLegend[status])) return reject0('ProofObligationLedger.StatusLegendMissing', ['obligationStatusLegend', status], 'status legend missing required status');
  if (!Array.isArray(ledger.obligations)) return reject0('ProofObligationLedger.ObligationsShape', ['obligations'], 'obligations must be an array');
  const ids = ledger.obligations.map((obligation) => obligation?.id);
  if (!sameArray0(ids, EXPECTED_OBLIGATION_IDS)) return reject0('ProofObligationLedger.ObligationIds', ['obligations'], 'obligation ids must stay exact and ordered', { expected: EXPECTED_OBLIGATION_IDS, actual: ids });
  const seen = new Set();
  for (let index = 0; index < ledger.obligations.length; index += 1) {
    const check = validateObligation0(ledger.obligations[index], ['obligations', index], seen);
    if (check.tag === 'reject') return check;
    seen.add(ledger.obligations[index].id);
  }
  const expectedAudit = { checker: CHECKER, script: 'pcc-proof-obligation-ledger0.mjs', test: 'audits/proof-obligation-ledger0.test.mjs', expectedAcceptTag: 'accept' };
  if (!plain0(ledger.audit)) return reject0('ProofObligationLedger.AuditShape', ['audit'], 'audit must be an object');
  for (const [key, expected] of Object.entries(expectedAudit)) if (ledger.audit[key] !== expected) return reject0('ProofObligationLedger.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: ledger.audit[key] });
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('ProofObligationLedger.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ProofObligationLedger.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ProofObligationLedger.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('ProofObligationLedger.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ProofObligationLedger.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

function validateObligation0(obligation, obligationPath, seen) {
  if (!plain0(obligation)) return reject0('ProofObligationLedger.ObligationShape', obligationPath, 'obligation must be an object');
  for (const field of ['id', 'statement', 'checker', 'status', 'hashMode']) if (!nonempty0(obligation[field])) return reject0('ProofObligationLedger.ObligationField', [...obligationPath, field], 'obligation field must be a non-empty string');
  if (!ALLOWED_STATUSES.includes(obligation.status)) return reject0('ProofObligationLedger.ObligationStatus', [...obligationPath, 'status'], 'obligation status is not allowed', { allowed: ALLOWED_STATUSES, actual: obligation.status });
  if (obligation.hashMode !== 'checker-computed') return reject0('ProofObligationLedger.HashMode', [...obligationPath, 'hashMode'], 'obligation hashMode must be checker-computed');
  for (const [field, nonEmpty] of [['sourceFiles', true], ['testFiles', true], ['dependencies', false]]) { const check = validateStringArray0(obligation[field], [...obligationPath, field], nonEmpty); if (check.tag === 'reject') return check; }
  for (const dependency of obligation.dependencies) if (!seen.has(dependency)) return reject0('ProofObligationLedger.ForwardDependency', [...obligationPath, 'dependencies'], 'obligation dependencies must point to earlier obligations', { dependency });
  if (obligation.status === 'blocked-release-obligation' && !obligation.dependencies.some((id) => id.startsWith('OBL-013') || id.startsWith('OBL-010') || id.startsWith('OBL-011') || id.startsWith('OBL-012'))) return reject0('ProofObligationLedger.BlockedDependency', [...obligationPath, 'dependencies'], 'blocked release obligations must depend on represented activation or release-ladder obligations');
  return { tag: 'accept' };
}

async function digestObligations0(root, obligations) {
  const obligationDigests = [];
  let sourceFileCount = 0;
  let testFileCount = 0;
  for (const obligation of obligations) {
    const sourceFiles = [];
    for (const relativePath of obligation.sourceFiles) { const file = await digestFile0(root, relativePath, ['obligations', obligation.id, 'sourceFiles']); if (file.tag === 'reject') return file; sourceFiles.push(file); sourceFileCount += 1; }
    const testFiles = [];
    for (const relativePath of obligation.testFiles) { const file = await digestFile0(root, relativePath, ['obligations', obligation.id, 'testFiles']); if (file.tag === 'reject') return file; testFiles.push(file); testFileCount += 1; }
    obligationDigests.push({ id: obligation.id, status: obligation.status, checker: obligation.checker, sourceDigest: sha256Text0(stableStringify0(sourceFiles)), testDigest: sha256Text0(stableStringify0(testFiles)), sourceFiles, testFiles, dependencyDigest: sha256Text0(stableStringify0(obligation.dependencies)) });
  }
  return { tag: 'accept', obligationDigests, sourceFileCount, testFileCount };
}

async function digestFile0(root, relativePath, pathArray) { const safePath = safeJoin0(root, relativePath); if (safePath === null) return reject0('ProofObligationLedger.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root'); try { const info = await stat(safePath); if (!info.isFile()) return reject0('ProofObligationLedger.PathNotFile', [...pathArray, relativePath], 'path must be a file'); const bytes = await readFile(safePath); return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length }; } catch (error) { return reject0('ProofObligationLedger.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error)); } }
function validateStringArray0(value, pathArray, nonEmpty) { if (!Array.isArray(value)) return reject0('ProofObligationLedger.StringArrayShape', pathArray, 'field must be an array of strings'); if (nonEmpty && value.length === 0) return reject0('ProofObligationLedger.StringArrayEmpty', pathArray, 'field must not be empty'); for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('ProofObligationLedger.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
function safeJoin0(root, relativePath) { if (!nonempty0(relativePath) || path.isAbsolute(relativePath)) return null; const resolvedRoot = path.resolve(root); const resolved = path.resolve(resolvedRoot, relativePath); const relative = path.relative(resolvedRoot, resolved); if (relative.startsWith('..') || path.isAbsolute(relative)) return null; return resolved; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS] }; }
async function writeAndReturn0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const absoluteOutputPath = path.join(root, outputPath); await mkdir(path.dirname(absoluteOutputPath), { recursive: true }); await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function countBy0(values) { const map = new Map(); for (const value of values) map.set(value, (map.get(value) ?? 0) + 1); return Object.fromEntries([...map.entries()].sort(([a], [b]) => a.localeCompare(b))); }
function stableStringify0(value) { if (value === null || typeof value !== 'object') return JSON.stringify(value); if (Array.isArray(value)) return `[${value.map((entry) => stableStringify0(entry)).join(',')}]`; return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const options = { root: process.cwd(), ledgerPath: LEDGER_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false }; for (let index = 0; index < argv.length; index += 1) { const arg = argv[index]; if (arg === '--json') options.json = true; else if (arg === '--no-write') options.writeOutput = false; else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root'); else if (arg === '--ledger') options.ledgerPath = requireValue0(argv, ++index, '--ledger'); else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output'); else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); } else throw new Error(`unknown argument: ${arg}`); } return options; }
function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node pcc-proof-obligation-ledger0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/proof-obligations/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --ledger <path>    Proof obligation ledger path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad proof obligation ledger CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckProofObligationLedger0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
