#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckReportTheoremInventory0';
const VERSION = 0;
const INVENTORY_PATH = 'report-bindings/REPORT_THEOREM_INVENTORY.json';
const BINDINGS_PATH = 'report-bindings/REPORT_THEOREM_BINDINGS.json';
const POLICY_PATH = 'report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/report-theorem-inventory/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_IDS = [
  'TL-001-Base',
  'TL-002-CHG',
  'TL-003-Mode',
  'TL-004-E',
  'TL-005-N',
  'TL-006-FT',
  'TL-007-X',
  'TL-008-BC',
  'TL-009-UN',
  'TL-010-HN',
  'TL-011-HResolve',
  'TL-012-BUD',
  'TL-013-NOR-FF',
  'TL-014-RW',
  'TL-015-BN2',
  'TL-016-BN3',
  'TL-017-BN4',
  'TL-018-BN5',
  'TL-019-PkgC',
  'TL-020-BN6',
  'TL-021-Packet',
  'TL-022-R',
  'TL-023-HB',
  'TL-024-O',
  'TL-025-G',
  'TL-026-Final',
  'TL-027-PACK',
];

export async function CheckReportTheoremInventory0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const inventoryRead = await readJson0({ root, filePath: options.inventoryPath ?? INVENTORY_PATH, override: options.inventoryOverride, label: 'report theorem inventory' });
    if (inventoryRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventoryRead);
    const bindingsRead = await readJson0({ root, filePath: options.bindingsPath ?? BINDINGS_PATH, override: options.bindingsOverride, label: 'theorem binding ledger' });
    if (bindingsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, bindingsRead);
    const policyRead = await readJson0({ root, filePath: options.policyPath ?? POLICY_PATH, override: options.policyOverride, label: 'no prose-only theorem policy' });
    if (policyRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, policyRead);
    const statusRead = await readJson0({ root, filePath: options.statusPath ?? STATUS_PATH, override: options.statusOverride, label: 'PNP status' });
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    const inventoryValidation = validateInventory0(inventoryRead.value);
    if (inventoryValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventoryValidation);
    const linkedValidation = validateLinkedLedgers0({ inventory: inventoryRead.value, bindings: bindingsRead.value, policy: policyRead.value, status: statusRead.value });
    if (linkedValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, linkedValidation);

    const evidencePaths = [
      INVENTORY_PATH,
      BINDINGS_PATH,
      POLICY_PATH,
      'proof-obligations/OBLIGATION_LEDGER.json',
      'proof-obligations/GAP_LEDGER.json',
      'release/RELEASE_LADDER.json',
      STATUS_PATH,
    ];
    const evidence = await digestEvidence0(root, evidencePaths);
    if (evidence.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, evidence);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'report-theorem-inventory-accepted-under-public-review-boundary',
      inventoryPath: options.inventoryPath ?? INVENTORY_PATH,
      inventorySha256: sha256Hex0(inventoryRead.bytes),
      theoremBindingLedgerSha256: sha256Hex0(bindingsRead.bytes),
      noProseOnlyTheoremPolicySha256: sha256Hex0(policyRead.bytes),
      statusSha256: sha256Hex0(statusRead.bytes),
      inventoryReady: true,
      sourceReportSection: '22 Theorem ledger',
      inventoryEntryCount: inventoryRead.value.inventoryEntries.length,
      expectedInventoryEntryCount: EXPECTED_IDS.length,
      releaseCriticalSpineCoveredByBindings: true,
      allNumberedReportTheoremsInventoried: false,
      fullHistoricalReportTheoremInventoryExhaustive: false,
      allInventoryEntriesBoundToCheckers: false,
      publicTheoremEmissionAllowedByInventory: false,
      proseOnlyTheoremActivationAllowedByInventory: false,
      evidenceFileCount: evidence.files.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.files)),
      evidence: evidence.files,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('ReportTheoremInventory.UnhandledException', [], 'report theorem inventory checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readJson0({ root, filePath, override, label }) {
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, filePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('ReportTheoremInventory.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validateInventory0(inventory) {
  if (!plain0(inventory)) return reject0('ReportTheoremInventory.Shape', [], 'inventory must be an object');
  if (inventory.kind !== 'PNPReportTheoremInventory0') return reject0('ReportTheoremInventory.Kind', ['kind'], 'inventory kind mismatch');
  if (inventory.version !== VERSION) return reject0('ReportTheoremInventory.Version', ['version'], 'inventory version mismatch');
  if (inventory.coordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremInventory.Coordinate', ['coordinate'], 'inventory coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: inventory.coordinate });
  if (inventory.status !== 'report-theorem-inventory-ready') return reject0('ReportTheoremInventory.Status', ['status'], 'inventory status mismatch');
  if (inventory.inventoryReady !== true) return reject0('ReportTheoremInventory.ReadyFlag', ['inventoryReady'], 'inventoryReady must be true');
  if (inventory.publicTheoremEmissionAllowedByInventory !== false) return reject0('ReportTheoremInventory.PublicEmissionByInventory', ['publicTheoremEmissionAllowedByInventory'], 'inventory cannot allow public theorem emission');
  if (inventory.proseOnlyTheoremActivationAllowedByInventory !== false) return reject0('ReportTheoremInventory.ProseActivationByInventory', ['proseOnlyTheoremActivationAllowedByInventory'], 'inventory cannot allow prose-only theorem activation');

  const boundary = validateBoundary0(inventory.claimBoundary, ['claimBoundary']);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(inventory.inventoryScope)) return reject0('ReportTheoremInventory.ScopeShape', ['inventoryScope'], 'inventoryScope must be an object');
  const scope = inventory.inventoryScope;
  if (scope.mode !== 'historical-section-22-theorem-ledger-rows') return reject0('ReportTheoremInventory.ScopeMode', ['inventoryScope', 'mode'], 'inventory scope mode mismatch');
  if (scope.expectedEntryCount !== EXPECTED_IDS.length) return reject0('ReportTheoremInventory.ExpectedCount', ['inventoryScope', 'expectedEntryCount'], 'expected entry count mismatch');
  if (scope.releaseCriticalSpineCoveredByBindings !== true) return reject0('ReportTheoremInventory.ReleaseCriticalSpineFlag', ['inventoryScope', 'releaseCriticalSpineCoveredByBindings'], 'release-critical spine coverage flag must be true');
  if (scope.allNumberedReportTheoremsInventoried !== false) return reject0('ReportTheoremInventory.AllNumberedOverclaim', ['inventoryScope', 'allNumberedReportTheoremsInventoried'], 'inventory cannot claim all numbered report theorems are inventoried yet');
  if (scope.fullHistoricalReportTheoremInventoryExhaustive !== false) return reject0('ReportTheoremInventory.ExhaustiveOverclaim', ['inventoryScope', 'fullHistoricalReportTheoremInventoryExhaustive'], 'inventory cannot claim full historical report theorem inventory yet');
  if (scope.allInventoryEntriesBoundToCheckers !== false) return reject0('ReportTheoremInventory.AllBoundOverclaim', ['inventoryScope', 'allInventoryEntriesBoundToCheckers'], 'inventory cannot claim all entries are bound to checkers yet');
  if (scope.futureExpansionRequired !== true) return reject0('ReportTheoremInventory.FutureExpansionFlag', ['inventoryScope', 'futureExpansionRequired'], 'future expansion must remain required');

  if (!plain0(inventory.linkedCoordinates)) return reject0('ReportTheoremInventory.LinkedCoordinatesShape', ['linkedCoordinates'], 'linkedCoordinates must be an object');
  const expectedLinks = {
    theoremBindingLedger: 'REPORT-THEOREM-BINDINGS-2026-06-27-01',
    noProseOnlyTheoremPolicy: 'PNP-NO-PROSE-ONLY-THEOREM-POLICY-2026-06-27-01',
    proofObligationLedger: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01',
    gapLedger: 'PNP-GAP-LEDGER-2026-06-27-01',
    releaseLadder: 'PNP-RELEASE-LADDER-2026-06-27-01',
  };
  for (const [key, expected] of Object.entries(expectedLinks)) {
    if (inventory.linkedCoordinates[key] !== expected) return reject0('ReportTheoremInventory.LinkedCoordinate', ['linkedCoordinates', key], 'linked coordinate mismatch', { expected, actual: inventory.linkedCoordinates[key] });
  }

  if (!Array.isArray(inventory.inventoryEntries)) return reject0('ReportTheoremInventory.EntriesShape', ['inventoryEntries'], 'inventoryEntries must be an array');
  const ids = inventory.inventoryEntries.map((entry) => entry?.id);
  if (!sameArray0(ids, EXPECTED_IDS)) return reject0('ReportTheoremInventory.EntryIds', ['inventoryEntries'], 'inventory entry ids must stay exact and ordered', { expected: EXPECTED_IDS, actual: ids });
  const labels = new Set();
  for (let index = 0; index < inventory.inventoryEntries.length; index += 1) {
    const entry = inventory.inventoryEntries[index];
    const entryPath = ['inventoryEntries', index];
    if (!plain0(entry)) return reject0('ReportTheoremInventory.EntryShape', entryPath, 'inventory entry must be an object');
    for (const field of ['id', 'sourceLabel', 'sourceSection', 'content', 'coverageStatus', 'publicEmissionEffect']) {
      if (!nonempty0(entry[field])) return reject0('ReportTheoremInventory.EntryField', [...entryPath, field], 'inventory entry field must be a non-empty string');
    }
    if (labels.has(entry.sourceLabel)) return reject0('ReportTheoremInventory.DuplicateSourceLabel', [...entryPath, 'sourceLabel'], 'source labels must be unique', { sourceLabel: entry.sourceLabel });
    labels.add(entry.sourceLabel);
    if (entry.sourceSection !== '22') return reject0('ReportTheoremInventory.SourceSection', [...entryPath, 'sourceSection'], 'source section must be 22');
    if (entry.publicEmissionEffect !== 'none') return reject0('ReportTheoremInventory.EntryPublicEmissionEffect', [...entryPath, 'publicEmissionEffect'], 'inventory entries cannot have public emission effect');
    if (entry.dischargesPublicTheorem !== false) return reject0('ReportTheoremInventory.EntryDischargesPublicTheorem', [...entryPath, 'dischargesPublicTheorem'], 'inventory entries cannot discharge public theorem');
    if (!['inventoried-not-exhaustively-bound', 'release-critical-boundary-represented'].includes(entry.coverageStatus)) return reject0('ReportTheoremInventory.EntryCoverageStatus', [...entryPath, 'coverageStatus'], 'unexpected inventory coverage status', { actual: entry.coverageStatus });
  }

  const nonClaimsCheck = validateStringArray0(inventory.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;

  if (!plain0(inventory.audit)) return reject0('ReportTheoremInventory.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = { checker: CHECKER, script: 'pcc-report-theorem-inventory0.mjs', test: 'audits/report-theorem-inventory0.test.mjs', expectedAcceptTag: 'accept' };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (inventory.audit[key] !== expected) return reject0('ReportTheoremInventory.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: inventory.audit[key] });
  }
  return { tag: 'accept' };
}

function validateLinkedLedgers0({ inventory, bindings, policy, status }) {
  if (!plain0(bindings) || bindings.kind !== 'PNPReportTheoremBindings0') return reject0('ReportTheoremInventory.BindingsKind', [BINDINGS_PATH], 'theorem bindings ledger kind mismatch');
  if (bindings.coordinate !== inventory.linkedCoordinates.theoremBindingLedger) return reject0('ReportTheoremInventory.BindingsCoordinate', ['linkedCoordinates', 'theoremBindingLedger'], 'binding coordinate mismatch');
  if (!Array.isArray(bindings.theoremBindings) || bindings.theoremBindings.length !== 20) return reject0('ReportTheoremInventory.BindingsCount', ['theoremBindings'], 'theorem binding ledger must keep release-critical count 20');
  if (bindings.theoremBindings.some((entry) => entry.dischargesPublicTheorem !== false || entry.publicEmissionEffect !== 'none')) return reject0('ReportTheoremInventory.BindingEmission', ['theoremBindings'], 'theorem bindings cannot discharge public theorem');

  if (!plain0(policy) || policy.kind !== 'PNPNoProseOnlyTheoremPolicy0') return reject0('ReportTheoremInventory.PolicyKind', [POLICY_PATH], 'policy kind mismatch');
  if (policy.coordinate !== inventory.linkedCoordinates.noProseOnlyTheoremPolicy) return reject0('ReportTheoremInventory.PolicyCoordinate', ['linkedCoordinates', 'noProseOnlyTheoremPolicy'], 'policy coordinate mismatch');
  if (policy.allNumberedReportTheoremsCovered !== false || policy.fullReportTheoremInventoryExhaustive !== false) return reject0('ReportTheoremInventory.PolicyOverclaim', [POLICY_PATH], 'no-prose-only policy cannot overclaim exhaustive coverage');
  if (policy.reportTheoremInventoryCoordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremInventory.PolicyInventoryCoordinate', [POLICY_PATH, 'reportTheoremInventoryCoordinate'], 'policy must bind report theorem inventory coordinate');

  if (!plain0(status) || status.kind !== 'PNPStatus0') return reject0('ReportTheoremInventory.StatusKind', [STATUS_PATH], 'status kind mismatch');
  if (status.reportTheoremInventoryCoordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremInventory.StatusCoordinate', ['reportTheoremInventoryCoordinate'], 'status must bind report theorem inventory coordinate');
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReportTheoremInventory.StatusBoundary', [STATUS_PATH], 'status boundary mismatch');
  return { tag: 'accept' };
}

function validateBoundary0(boundary, pathArray) {
  if (!plain0(boundary)) return reject0('ReportTheoremInventory.BoundaryShape', pathArray, 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ReportTheoremInventory.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ReportTheoremInventory.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('ReportTheoremInventory.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must be empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReportTheoremInventory.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

async function digestEvidence0(root, paths) {
  const files = [];
  for (const relativePath of paths) {
    const file = await digestFile0(root, relativePath, ['evidenceFiles']);
    if (file.tag === 'reject') return file;
    files.push(file);
  }
  return { tag: 'accept', files };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('ReportTheoremInventory.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('ReportTheoremInventory.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('ReportTheoremInventory.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('ReportTheoremInventory.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('ReportTheoremInventory.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('ReportTheoremInventory.StringArrayEntry', [...pathArray, index], 'array entry must be non-empty string');
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
  const options = { root: process.cwd(), outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--inventory') options.inventoryPath = requireValue0(argv, ++index, '--inventory');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}
function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node pcc-report-theorem-inventory0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/report-theorem-inventory/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --inventory <path> Inventory JSON path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad report theorem inventory CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckReportTheoremInventory0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
