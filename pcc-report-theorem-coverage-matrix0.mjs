#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckReportTheoremCoverageMatrix0';
const VERSION = 0;
const MATRIX_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json';
const INVENTORY_PATH = 'report-bindings/REPORT_THEOREM_INVENTORY.json';
const BINDINGS_PATH = 'report-bindings/REPORT_THEOREM_BINDINGS.json';
const POLICY_PATH = 'report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/report-theorem-coverage-matrix/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-REPORT-THEOREM-COVERAGE-MATRIX-2026-06-27-01';
const EXPECTED_INVENTORY_COORDINATE = 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_INVENTORY_IDS = [
  'TL-001-Base', 'TL-002-CHG', 'TL-003-Mode', 'TL-004-E', 'TL-005-N', 'TL-006-FT', 'TL-007-X', 'TL-008-BC', 'TL-009-UN',
  'TL-010-HN', 'TL-011-HResolve', 'TL-012-BUD', 'TL-013-NOR-FF', 'TL-014-RW', 'TL-015-BN2', 'TL-016-BN3', 'TL-017-BN4',
  'TL-018-BN5', 'TL-019-PkgC', 'TL-020-BN6', 'TL-021-Packet', 'TL-022-R', 'TL-023-HB', 'TL-024-O', 'TL-025-G', 'TL-026-Final', 'TL-027-PACK',
];
const EXPECTED_COVERAGE_IDS = EXPECTED_INVENTORY_IDS.map((id) => `COV-${id.slice(3)}`);
const ALLOWED_CLASSES = [
  'semantics-seed-surface',
  'obligation-ledger-surface',
  'inventory-ledger-surface',
  'uniformity-gap-surface',
  'complexity-and-gap-surface',
  'locked-nand-seed-surface',
  'release-critical-boundary-surface',
];

export async function CheckReportTheoremCoverageMatrix0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const matrixRead = await readJson0({ root, filePath: options.matrixPath ?? MATRIX_PATH, override: options.matrixOverride, label: 'coverage matrix' });
    if (matrixRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, matrixRead);
    const inventoryRead = await readJson0({ root, filePath: options.inventoryPath ?? INVENTORY_PATH, override: options.inventoryOverride, label: 'report theorem inventory' });
    if (inventoryRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventoryRead);
    const bindingsRead = await readJson0({ root, filePath: options.bindingsPath ?? BINDINGS_PATH, override: options.bindingsOverride, label: 'theorem bindings' });
    if (bindingsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, bindingsRead);
    const policyRead = await readJson0({ root, filePath: options.policyPath ?? POLICY_PATH, override: options.policyOverride, label: 'no-prose policy' });
    if (policyRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, policyRead);
    const statusRead = await readJson0({ root, filePath: options.statusPath ?? STATUS_PATH, override: options.statusOverride, label: 'PNP status' });
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    const matrixValidation = validateMatrix0(matrixRead.value);
    if (matrixValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, matrixValidation);
    const linkedValidation = validateLinked0({ matrix: matrixRead.value, inventory: inventoryRead.value, bindings: bindingsRead.value, policy: policyRead.value, status: statusRead.value });
    if (linkedValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, linkedValidation);
    const digest = await digestCoverageEvidence0(root, matrixRead.value.coverageEntries);
    if (digest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, digest);

    const directCompleteCount = matrixRead.value.coverageEntries.filter((entry) => entry.directCheckerBindingComplete === true).length;
    const releaseCriticalCount = matrixRead.value.coverageEntries.filter((entry) => entry.coverageClass === 'release-critical-boundary-surface').length;

    return writeAndReturn0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'report-theorem-coverage-matrix-accepted-under-public-review-boundary',
      matrixPath: options.matrixPath ?? MATRIX_PATH,
      matrixSha256: sha256Hex0(matrixRead.bytes),
      inventorySha256: sha256Hex0(inventoryRead.bytes),
      theoremBindingLedgerSha256: sha256Hex0(bindingsRead.bytes),
      noProseOnlyTheoremPolicySha256: sha256Hex0(policyRead.bytes),
      statusSha256: sha256Hex0(statusRead.bytes),
      coverageMatrixReady: true,
      allInventoryEntriesHaveCoverageRows: true,
      releaseCriticalEntriesHaveBoundaryRows: true,
      allInventoryEntriesDirectCheckerBound: false,
      fullHistoricalReportTheoremCoverageProved: false,
      publicTheoremEmissionAllowedByCoverage: false,
      inventoryEntryCount: inventoryRead.value.inventoryEntries.length,
      coverageEntryCount: matrixRead.value.coverageEntries.length,
      directCheckerBindingCompleteCount: directCompleteCount,
      releaseCriticalCoverageEntryCount: releaseCriticalCount,
      evidenceFileCount: digest.evidenceFiles.length,
      coverageDigestSha256: sha256Text0(stableStringify0(digest.coverageDigests)),
      evidenceDigestSha256: sha256Text0(stableStringify0(digest.evidenceFiles)),
      coverageDigests: digest.coverageDigests,
      evidenceFiles: digest.evidenceFiles,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('ReportTheoremCoverageMatrix.UnhandledException', [], 'coverage matrix checker threw unexpectedly', normalizeError0(error)));
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
    return reject0('ReportTheoremCoverageMatrix.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validateMatrix0(matrix) {
  if (!plain0(matrix)) return reject0('ReportTheoremCoverageMatrix.Shape', [], 'matrix must be an object');
  if (matrix.kind !== 'PNPReportTheoremCoverageMatrix0') return reject0('ReportTheoremCoverageMatrix.Kind', ['kind'], 'matrix kind mismatch');
  if (matrix.version !== VERSION) return reject0('ReportTheoremCoverageMatrix.Version', ['version'], 'matrix version mismatch');
  if (matrix.coordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremCoverageMatrix.Coordinate', ['coordinate'], 'matrix coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: matrix.coordinate });
  if (matrix.status !== 'report-theorem-coverage-matrix-ready') return reject0('ReportTheoremCoverageMatrix.Status', ['status'], 'matrix status mismatch');
  for (const [field, expected] of Object.entries({ coverageMatrixReady: true, allInventoryEntriesHaveCoverageRows: true, releaseCriticalEntriesHaveBoundaryRows: true, allInventoryEntriesDirectCheckerBound: false, fullHistoricalReportTheoremCoverageProved: false, publicTheoremEmissionAllowedByCoverage: false })) {
    if (matrix[field] !== expected) return reject0('ReportTheoremCoverageMatrix.Flag', [field], 'coverage matrix flag mismatch', { expected, actual: matrix[field] });
  }
  const boundary = validateBoundary0(matrix.claimBoundary, ['claimBoundary']);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(matrix.coverageScope)) return reject0('ReportTheoremCoverageMatrix.ScopeShape', ['coverageScope'], 'coverageScope must be an object');
  if (matrix.coverageScope.mode !== 'historical-section-22-theorem-ledger-row-coverage-matrix') return reject0('ReportTheoremCoverageMatrix.ScopeMode', ['coverageScope', 'mode'], 'coverage scope mode mismatch');
  if (matrix.coverageScope.inventoryCoordinate !== EXPECTED_INVENTORY_COORDINATE) return reject0('ReportTheoremCoverageMatrix.ScopeInventoryCoordinate', ['coverageScope', 'inventoryCoordinate'], 'inventory coordinate mismatch');
  if (matrix.coverageScope.expectedInventoryEntryCount !== EXPECTED_INVENTORY_IDS.length || matrix.coverageScope.expectedCoverageEntryCount !== EXPECTED_COVERAGE_IDS.length) return reject0('ReportTheoremCoverageMatrix.ScopeCounts', ['coverageScope'], 'coverage counts mismatch');
  if (matrix.coverageScope.coverageRowsAreActivationSafe !== true || matrix.coverageScope.directCheckerBindingExpansionRequired !== true) return reject0('ReportTheoremCoverageMatrix.ScopePolicyFlags', ['coverageScope'], 'coverage scope policy flags mismatch');

  if (!plain0(matrix.linkedCoordinates)) return reject0('ReportTheoremCoverageMatrix.LinkedShape', ['linkedCoordinates'], 'linkedCoordinates must be an object');
  const expectedLinks = {
    reportTheoremInventory: EXPECTED_INVENTORY_COORDINATE,
    theoremBindingLedger: 'REPORT-THEOREM-BINDINGS-2026-06-27-01',
    noProseOnlyTheoremPolicy: 'PNP-NO-PROSE-ONLY-THEOREM-POLICY-2026-06-27-01',
    proofObligationLedger: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01',
    gapLedger: 'PNP-GAP-LEDGER-2026-06-27-01',
    finiteToUnboundedFamilyAudit: 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01',
    releaseLadder: 'PNP-RELEASE-LADDER-2026-06-27-01',
  };
  for (const [key, expected] of Object.entries(expectedLinks)) if (matrix.linkedCoordinates[key] !== expected) return reject0('ReportTheoremCoverageMatrix.LinkedCoordinate', ['linkedCoordinates', key], 'linked coordinate mismatch', { expected, actual: matrix.linkedCoordinates[key] });

  if (!plain0(matrix.coverageClassLegend)) return reject0('ReportTheoremCoverageMatrix.LegendShape', ['coverageClassLegend'], 'coverage class legend must be an object');
  for (const key of ALLOWED_CLASSES) if (!nonempty0(matrix.coverageClassLegend[key])) return reject0('ReportTheoremCoverageMatrix.LegendMissing', ['coverageClassLegend', key], 'coverage class legend missing key');

  if (!Array.isArray(matrix.coverageEntries)) return reject0('ReportTheoremCoverageMatrix.EntriesShape', ['coverageEntries'], 'coverageEntries must be an array');
  const ids = matrix.coverageEntries.map((entry) => entry?.id);
  if (!sameArray0(ids, EXPECTED_COVERAGE_IDS)) return reject0('ReportTheoremCoverageMatrix.CoverageIds', ['coverageEntries'], 'coverage ids must stay exact and ordered', { expected: EXPECTED_COVERAGE_IDS, actual: ids });
  const inventoryIds = matrix.coverageEntries.map((entry) => entry?.inventoryEntryId);
  if (!sameArray0(inventoryIds, EXPECTED_INVENTORY_IDS)) return reject0('ReportTheoremCoverageMatrix.InventoryIds', ['coverageEntries'], 'inventory ids must stay exact and ordered', { expected: EXPECTED_INVENTORY_IDS, actual: inventoryIds });

  for (let index = 0; index < matrix.coverageEntries.length; index += 1) {
    const entry = matrix.coverageEntries[index];
    const check = validateCoverageEntry0(entry, ['coverageEntries', index]);
    if (check.tag === 'reject') return check;
  }
  const finalEntry = matrix.coverageEntries.find((entry) => entry.inventoryEntryId === 'TL-026-Final');
  const packEntry = matrix.coverageEntries.find((entry) => entry.inventoryEntryId === 'TL-027-PACK');
  if (finalEntry?.coverageClass !== 'release-critical-boundary-surface' || packEntry?.coverageClass !== 'release-critical-boundary-surface') return reject0('ReportTheoremCoverageMatrix.ReleaseCriticalCoverage', ['coverageEntries'], 'Final and PACK rows must be release-critical boundary surfaces');

  const nonClaimsCheck = validateStringArray0(matrix.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;
  if (!plain0(matrix.audit)) return reject0('ReportTheoremCoverageMatrix.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = { checker: CHECKER, script: 'pcc-report-theorem-coverage-matrix0.mjs', test: 'audits/report-theorem-coverage-matrix0.test.mjs', expectedAcceptTag: 'accept' };
  for (const [key, expected] of Object.entries(expectedAudit)) if (matrix.audit[key] !== expected) return reject0('ReportTheoremCoverageMatrix.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: matrix.audit[key] });
  return { tag: 'accept' };
}

function validateCoverageEntry0(entry, pathArray) {
  if (!plain0(entry)) return reject0('ReportTheoremCoverageMatrix.EntryShape', pathArray, 'coverage entry must be an object');
  for (const field of ['id', 'inventoryEntryId', 'sourceLabel', 'coverageClass', 'coverageStatus', 'publicEmissionEffect']) if (!nonempty0(entry[field])) return reject0('ReportTheoremCoverageMatrix.EntryField', [...pathArray, field], 'coverage entry field must be non-empty string');
  if (!ALLOWED_CLASSES.includes(entry.coverageClass)) return reject0('ReportTheoremCoverageMatrix.CoverageClass', [...pathArray, 'coverageClass'], 'coverage class not allowed', { actual: entry.coverageClass });
  if (entry.coverageStatus !== 'represented-by-explicit-ledger-surface') return reject0('ReportTheoremCoverageMatrix.CoverageStatus', [...pathArray, 'coverageStatus'], 'coverage status mismatch');
  if (entry.representedByMachineLedger !== true) return reject0('ReportTheoremCoverageMatrix.RepresentedFlag', [...pathArray, 'representedByMachineLedger'], 'coverage entry must be represented by machine ledger');
  if (entry.directCheckerBindingComplete !== false) return reject0('ReportTheoremCoverageMatrix.DirectBindingOverclaim', [...pathArray, 'directCheckerBindingComplete'], 'coverage entry cannot claim direct checker binding complete');
  if (entry.publicEmissionEffect !== 'none' || entry.dischargesPublicTheorem !== false) return reject0('ReportTheoremCoverageMatrix.EntryPublicEmission', pathArray, 'coverage entry cannot discharge public theorem');
  const obligationsCheck = validateStringArray0(entry.relatedObligations, [...pathArray, 'relatedObligations'], true);
  if (obligationsCheck.tag === 'reject') return obligationsCheck;
  const gapsCheck = validateStringArray0(entry.relatedGaps, [...pathArray, 'relatedGaps'], false);
  if (gapsCheck.tag === 'reject') return gapsCheck;
  const evidenceCheck = validateStringArray0(entry.evidenceFiles, [...pathArray, 'evidenceFiles'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;
  return { tag: 'accept' };
}

function validateLinked0({ matrix, inventory, bindings, policy, status }) {
  if (!plain0(inventory) || inventory.kind !== 'PNPReportTheoremInventory0') return reject0('ReportTheoremCoverageMatrix.InventoryKind', [INVENTORY_PATH], 'report theorem inventory kind mismatch');
  if (inventory.coordinate !== EXPECTED_INVENTORY_COORDINATE) return reject0('ReportTheoremCoverageMatrix.InventoryCoordinate', [INVENTORY_PATH, 'coordinate'], 'inventory coordinate mismatch');
  const inventoryIds = Array.isArray(inventory.inventoryEntries) ? inventory.inventoryEntries.map((entry) => entry.id) : [];
  if (!sameArray0(inventoryIds, EXPECTED_INVENTORY_IDS)) return reject0('ReportTheoremCoverageMatrix.InventoryEntryIds', [INVENTORY_PATH, 'inventoryEntries'], 'inventory entry ids mismatch');
  for (let index = 0; index < matrix.coverageEntries.length; index += 1) {
    if (matrix.coverageEntries[index].sourceLabel !== inventory.inventoryEntries[index].sourceLabel) return reject0('ReportTheoremCoverageMatrix.SourceLabelMismatch', ['coverageEntries', index, 'sourceLabel'], 'coverage source label must match inventory source label');
  }
  if (!plain0(bindings) || bindings.kind !== 'PNPReportTheoremBindings0') return reject0('ReportTheoremCoverageMatrix.BindingsKind', [BINDINGS_PATH], 'theorem bindings ledger kind mismatch');
  if (Array.isArray(bindings.theoremBindings) && bindings.theoremBindings.some((entry) => entry.dischargesPublicTheorem !== false || entry.publicEmissionEffect !== 'none')) return reject0('ReportTheoremCoverageMatrix.BindingPublicEmission', [BINDINGS_PATH], 'theorem bindings cannot discharge public theorem');
  if (!plain0(policy) || policy.kind !== 'PNPNoProseOnlyTheoremPolicy0') return reject0('ReportTheoremCoverageMatrix.PolicyKind', [POLICY_PATH], 'no-prose-only policy kind mismatch');
  if (policy.publicTheoremEmissionAllowedByPolicy !== false || policy.proseOnlyTheoremActivationAllowed !== false) return reject0('ReportTheoremCoverageMatrix.PolicyEmission', [POLICY_PATH], 'policy cannot allow public emission or prose-only activation');
  if (!plain0(status) || status.kind !== 'PNPStatus0') return reject0('ReportTheoremCoverageMatrix.StatusKind', [STATUS_PATH], 'status kind mismatch');
  if (status.reportTheoremCoverageMatrixCoordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremCoverageMatrix.StatusCoordinate', [STATUS_PATH, 'reportTheoremCoverageMatrixCoordinate'], 'status must bind coverage matrix coordinate');
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReportTheoremCoverageMatrix.StatusBoundary', [STATUS_PATH], 'status boundary mismatch');
  return { tag: 'accept' };
}

async function digestCoverageEvidence0(root, coverageEntries) {
  const coverageDigests = [];
  const evidenceMap = new Map();
  for (const entry of coverageEntries) {
    const evidenceFiles = [];
    for (const relativePath of entry.evidenceFiles) {
      let file = evidenceMap.get(relativePath);
      if (!file) {
        file = await digestFile0(root, relativePath, ['coverageEntries', entry.id, 'evidenceFiles']);
        if (file.tag === 'reject') return file;
        evidenceMap.set(relativePath, file);
      }
      evidenceFiles.push(file);
    }
    coverageDigests.push({ id: entry.id, inventoryEntryId: entry.inventoryEntryId, coverageClass: entry.coverageClass, evidenceDigest: sha256Text0(stableStringify0(evidenceFiles)), evidenceFiles });
  }
  return { tag: 'accept', coverageDigests, evidenceFiles: [...evidenceMap.values()].sort((a, b) => a.path.localeCompare(b.path)) };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('ReportTheoremCoverageMatrix.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('ReportTheoremCoverageMatrix.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('ReportTheoremCoverageMatrix.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateBoundary0(boundary, pathArray) {
  if (!plain0(boundary)) return reject0('ReportTheoremCoverageMatrix.BoundaryShape', pathArray, 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ReportTheoremCoverageMatrix.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ReportTheoremCoverageMatrix.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('ReportTheoremCoverageMatrix.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReportTheoremCoverageMatrix.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('ReportTheoremCoverageMatrix.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('ReportTheoremCoverageMatrix.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('ReportTheoremCoverageMatrix.StringArrayEntry', [...pathArray, index], 'array entry must be non-empty string');
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
    else if (arg === '--matrix') options.matrixPath = requireValue0(argv, ++index, '--matrix');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}
function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node pcc-report-theorem-coverage-matrix0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/report-theorem-coverage-matrix/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --matrix <path>    Matrix JSON path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad theorem coverage matrix CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckReportTheoremCoverageMatrix0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
