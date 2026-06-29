#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckBaseDirectBindingSeed0';
const VERSION = 0;
const MANIFEST_PATH = 'report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json';
const INVENTORY_PATH = 'report-bindings/REPORT_THEOREM_INVENTORY.json';
const MATRIX_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json';
const CLOSURE_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json';
const SEMANTICS_PATH = 'semantics/nand-direct-wire-spec.json';
const OBLIGATIONS_PATH = 'proof-obligations/OBLIGATION_LEDGER.json';
const GAPS_PATH = 'proof-obligations/GAP_LEDGER.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/direct-bind-base-semantics/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-DIRECT-BIND-BASE-SEMANTICS-SEED-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COMPONENT_IDS = ['Base.DirectWireNANDSyntax', 'Base.OpenFunctionEvaluation', 'Base.CompatibleReplacementSemantics', 'Base.SlackLawLedgerSurface'];

export async function CheckBaseDirectBindingSeed0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? MANIFEST_PATH, options.manifestOverride, 'Base direct-binding seed manifest');
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);
    const inventoryRead = await readJson0(root, options.inventoryPath ?? INVENTORY_PATH, options.inventoryOverride, 'report theorem inventory');
    if (inventoryRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventoryRead);
    const matrixRead = await readJson0(root, options.matrixPath ?? MATRIX_PATH, options.matrixOverride, 'report theorem coverage matrix');
    if (matrixRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, matrixRead);
    const closureRead = await readJson0(root, options.closurePath ?? CLOSURE_PATH, options.closureOverride, 'report theorem coverage closure plan');
    if (closureRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, closureRead);
    const semanticsRead = await readJson0(root, options.semanticsPath ?? SEMANTICS_PATH, options.semanticsOverride, 'NAND direct-wire semantics spec');
    if (semanticsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, semanticsRead);
    const obligationsRead = await readJson0(root, options.obligationsPath ?? OBLIGATIONS_PATH, options.obligationsOverride, 'proof obligation ledger');
    if (obligationsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, obligationsRead);
    const gapsRead = await readJson0(root, options.gapsPath ?? GAPS_PATH, options.gapsOverride, 'gap ledger');
    if (gapsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, gapsRead);
    const statusRead = await readJson0(root, options.statusPath ?? STATUS_PATH, options.statusOverride, 'PNP status');
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    for (const check of [
      validateManifest0(manifestRead.value),
      validateInventory0(inventoryRead.value),
      validateMatrix0(matrixRead.value),
      validateClosure0(closureRead.value),
      validateSemantics0(semanticsRead.value),
      validateObligations0(obligationsRead.value),
      validateGaps0(gapsRead.value),
      validateStatus0(statusRead.value),
    ]) {
      if (check.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, check);
    }

    const evidence = await digestEvidence0(root, manifestRead.value.evidenceSurfaces);
    if (evidence.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, evidence);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'base-direct-binding-seed-accepted-under-public-review-boundary',
      manifestPath: options.manifestPath ?? MANIFEST_PATH,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      inventorySha256: sha256Hex0(inventoryRead.bytes),
      matrixSha256: sha256Hex0(matrixRead.bytes),
      closurePlanSha256: sha256Hex0(closureRead.bytes),
      semanticsSha256: sha256Hex0(semanticsRead.bytes),
      proofObligationLedgerSha256: sha256Hex0(obligationsRead.bytes),
      gapLedgerSha256: sha256Hex0(gapsRead.bytes),
      statusSha256: sha256Hex0(statusRead.bytes),
      baseDirectBindingSeedReady: true,
      boundInventoryEntryId: 'TL-001-Base',
      boundCoverageEntryId: 'COV-001-Base',
      boundClosureEntryId: 'DCC-001-Base',
      coveredBaseComponents: [...EXPECTED_COMPONENT_IDS],
      directCheckerBindingComplete: false,
      fullHistoricalBaseTheoremDischarged: false,
      publicTheoremEmissionAllowedByBinding: false,
      evidenceFileCount: evidence.files.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.files)),
      evidenceFiles: evidence.files,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };
    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('BaseDirectBindingSeed.UnhandledException', [], 'Base direct-binding seed checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readJson0(root, filePath, override, label) {
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, filePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('BaseDirectBindingSeed.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('BaseDirectBindingSeed.ManifestShape', [], 'manifest must be an object');
  const exact = {
    kind: 'PNPBaseDirectBindingSeed0',
    version: VERSION,
    coordinate: EXPECTED_COORDINATE,
    status: 'base-direct-binding-seed-ready',
    baseDirectBindingSeedReady: true,
    releaseCriticalRow: false,
    directCheckerBindingComplete: false,
    fullHistoricalBaseTheoremDischarged: false,
    publicTheoremEmissionAllowedByBinding: false,
  };
  for (const [field, expected] of Object.entries(exact)) if (manifest[field] !== expected) return reject0(`BaseDirectBindingSeed.Manifest.${field}`, [field], 'manifest field mismatch', { expected, actual: manifest[field] });
  const boundary = validateBoundary0(manifest.claimBoundary, ['claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  const links = manifest.linkedCoordinates;
  const expectedLinks = {
    reportTheoremInventory: 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01',
    reportTheoremCoverageMatrix: 'PNP-REPORT-THEOREM-COVERAGE-MATRIX-2026-06-27-01',
    reportTheoremCoverageClosurePlan: 'PNP-REPORT-THEOREM-COVERAGE-CLOSURE-PLAN-2026-06-27-01',
    nandDirectWireSemantics: 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01',
    proofObligationLedger: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01',
    gapLedger: 'PNP-GAP-LEDGER-2026-06-27-01',
  };
  if (!plain0(links)) return reject0('BaseDirectBindingSeed.LinkedShape', ['linkedCoordinates'], 'linkedCoordinates must be an object');
  for (const [field, expected] of Object.entries(expectedLinks)) if (links[field] !== expected) return reject0('BaseDirectBindingSeed.LinkedCoordinate', ['linkedCoordinates', field], 'linked coordinate mismatch', { expected, actual: links[field] });
  const bound = manifest.boundInventoryEntry;
  if (!plain0(bound) || bound.inventoryEntryId !== 'TL-001-Base' || bound.coverageEntryId !== 'COV-001-Base' || bound.closureEntryId !== 'DCC-001-Base' || bound.sourceLabel !== 'Base' || bound.expectedCoverageClass !== 'semantics-seed-surface' || bound.expectedClosureStatus !== 'direct-binding-seed-upgrade-needed') return reject0('BaseDirectBindingSeed.BoundEntry', ['boundInventoryEntry'], 'bound inventory entry mismatch');
  const componentIds = Array.isArray(manifest.coveredBaseComponents) ? manifest.coveredBaseComponents.map((entry) => entry?.id) : [];
  if (!sameArray0(componentIds, EXPECTED_COMPONENT_IDS)) return reject0('BaseDirectBindingSeed.ComponentIds', ['coveredBaseComponents'], 'covered component ids must stay exact and ordered', { expected: EXPECTED_COMPONENT_IDS, actual: componentIds });
  for (const entry of manifest.coveredBaseComponents) if (!plain0(entry) || !nonempty0(entry.status) || !nonempty0(entry.evidence)) return reject0('BaseDirectBindingSeed.ComponentShape', ['coveredBaseComponents'], 'component entries must declare status and evidence');
  const evidenceCheck = validateStringArray0(manifest.evidenceSurfaces, ['evidenceSurfaces'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;
  const nonClaimsCheck = validateStringArray0(manifest.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;
  const expectedAudit = { checker: CHECKER, script: 'pcc-direct-bind-base-semantics0.mjs', test: 'audits/direct-bind-base-semantics0.test.mjs', expectedAcceptTag: 'accept' };
  if (!plain0(manifest.audit)) return reject0('BaseDirectBindingSeed.AuditShape', ['audit'], 'audit must be an object');
  for (const [field, expected] of Object.entries(expectedAudit)) if (manifest.audit[field] !== expected) return reject0('BaseDirectBindingSeed.AuditField', ['audit', field], 'audit field mismatch', { expected, actual: manifest.audit[field] });
  return { tag: 'accept' };
}

function validateInventory0(inventory) {
  if (!plain0(inventory) || inventory.kind !== 'PNPReportTheoremInventory0') return reject0('BaseDirectBindingSeed.InventoryKind', [INVENTORY_PATH], 'inventory kind mismatch');
  const entry = Array.isArray(inventory.inventoryEntries) ? inventory.inventoryEntries.find((item) => item.id === 'TL-001-Base') : null;
  if (!plain0(entry)) return reject0('BaseDirectBindingSeed.InventoryBaseMissing', [INVENTORY_PATH, 'inventoryEntries'], 'TL-001-Base entry missing');
  if (entry.sourceLabel !== 'Base' || !String(entry.content).includes('Direct-wire NAND semantics') || entry.publicEmissionEffect !== 'none' || entry.dischargesPublicTheorem !== false) return reject0('BaseDirectBindingSeed.InventoryBaseMismatch', [INVENTORY_PATH, 'TL-001-Base'], 'Base inventory row mismatch');
  return { tag: 'accept' };
}

function validateMatrix0(matrix) {
  if (!plain0(matrix) || matrix.kind !== 'PNPReportTheoremCoverageMatrix0') return reject0('BaseDirectBindingSeed.MatrixKind', [MATRIX_PATH], 'coverage matrix kind mismatch');
  const row = Array.isArray(matrix.coverageEntries) ? matrix.coverageEntries.find((entry) => entry.id === 'COV-001-Base') : null;
  if (!plain0(row)) return reject0('BaseDirectBindingSeed.MatrixBaseMissing', [MATRIX_PATH, 'coverageEntries'], 'COV-001-Base row missing');
  if (row.inventoryEntryId !== 'TL-001-Base' || row.sourceLabel !== 'Base' || row.coverageClass !== 'semantics-seed-surface' || row.representedByMachineLedger !== true || row.directCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('BaseDirectBindingSeed.MatrixBaseMismatch', [MATRIX_PATH, 'COV-001-Base'], 'Base coverage row mismatch');
  return { tag: 'accept' };
}

function validateClosure0(closure) {
  if (!plain0(closure) || closure.kind !== 'PNPReportTheoremCoverageClosurePlan0') return reject0('BaseDirectBindingSeed.ClosureKind', [CLOSURE_PATH], 'coverage closure plan kind mismatch');
  const row = Array.isArray(closure.closureEntries) ? closure.closureEntries.find((entry) => entry.id === 'DCC-001-Base') : null;
  if (!plain0(row)) return reject0('BaseDirectBindingSeed.ClosureBaseMissing', [CLOSURE_PATH, 'closureEntries'], 'DCC-001-Base row missing');
  if (row.coverageEntryId !== 'COV-001-Base' || row.inventoryEntryId !== 'TL-001-Base' || row.sourceLabel !== 'Base' || row.currentCoverageClass !== 'semantics-seed-surface' || row.closureStatus !== 'direct-binding-seed-upgrade-needed' || row.nextDirectBindingSurface !== 'pcc-direct-bind-base-semantics0.mjs' || row.mayFlipDirectCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('BaseDirectBindingSeed.ClosureBaseMismatch', [CLOSURE_PATH, 'DCC-001-Base'], 'Base closure row mismatch');
  return { tag: 'accept' };
}

function validateSemantics0(semantics) {
  if (!plain0(semantics) || semantics.kind !== 'PNPNANDDirectWireSemantics0' || semantics.coordinate !== 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01' || semantics.semanticsReady !== true || semantics.fullSemanticsCoverageProved !== false) return reject0('BaseDirectBindingSeed.SemanticsMismatch', [SEMANTICS_PATH], 'NAND direct-wire semantics seed mismatch');
  for (const required of ['NAND gate syntax', 'truth-table evaluation', 'compatible replacement semantics for same boundary and output arity']) {
    if (!Array.isArray(semantics.coveredConcepts) || !semantics.coveredConcepts.includes(required)) return reject0('BaseDirectBindingSeed.SemanticsConceptMissing', [SEMANTICS_PATH, 'coveredConcepts'], 'required semantics concept missing', { required });
  }
  return { tag: 'accept' };
}

function validateObligations0(ledger) {
  if (!plain0(ledger) || ledger.kind !== 'PNPProofObligationLedger0' || ledger.publicTheoremEmissionAllowedByLedger !== false || ledger.fullProofObligationDischargeProved !== false) return reject0('BaseDirectBindingSeed.ObligationLedgerMismatch', [OBLIGATIONS_PATH], 'proof obligation ledger mismatch');
  const ids = new Set(Array.isArray(ledger.obligations) ? ledger.obligations.map((entry) => entry.id) : []);
  for (const required of ['OBL-007-NANDDirectWireSemantics', 'OBL-016-BaseDirectBindingSeed']) if (!ids.has(required)) return reject0('BaseDirectBindingSeed.ObligationMissing', [OBLIGATIONS_PATH, 'obligations'], 'required obligation missing', { required });
  return { tag: 'accept' };
}

function validateGaps0(gaps) {
  if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0' || gaps.gapLedgerClaimsNoRemainingGaps !== false || gaps.fullGapClosureProved !== false || gaps.publicTheoremEmissionAllowedByLedger !== false) return reject0('BaseDirectBindingSeed.GapLedgerMismatch', [GAPS_PATH], 'gap ledger cannot overclaim closure');
  return { tag: 'accept' };
}

function validateStatus0(status) {
  if (!plain0(status) || status.kind !== 'PNPStatus0') return reject0('BaseDirectBindingSeed.StatusKind', [STATUS_PATH], 'status kind mismatch');
  if (status.baseDirectBindingSeedCoordinate !== EXPECTED_COORDINATE) return reject0('BaseDirectBindingSeed.StatusCoordinate', ['baseDirectBindingSeedCoordinate'], 'status must bind Base direct-binding seed coordinate');
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('BaseDirectBindingSeed.StatusBoundary', [STATUS_PATH], 'status boundary mismatch');
  return { tag: 'accept' };
}

async function digestEvidence0(root, paths) {
  const files = [];
  for (const relativePath of paths) {
    const file = await digestFile0(root, relativePath, ['evidenceSurfaces']);
    if (file.tag === 'reject') return file;
    files.push(file);
  }
  return { tag: 'accept', files };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('BaseDirectBindingSeed.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('BaseDirectBindingSeed.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('BaseDirectBindingSeed.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateBoundary0(boundary, pathArray) {
  if (!plain0(boundary)) return reject0('BaseDirectBindingSeed.BoundaryShape', pathArray, 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('BaseDirectBindingSeed.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('BaseDirectBindingSeed.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('BaseDirectBindingSeed.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('BaseDirectBindingSeed.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

function validateStringArray0(value, pathArray, nonEmpty) { if (!Array.isArray(value)) return reject0('BaseDirectBindingSeed.StringArrayShape', pathArray, 'field must be an array of strings'); if (nonEmpty && value.length === 0) return reject0('BaseDirectBindingSeed.StringArrayEmpty', pathArray, 'field must not be empty'); for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('BaseDirectBindingSeed.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
function safeJoin0(root, relativePath) { if (!nonempty0(relativePath) || path.isAbsolute(relativePath)) return null; const resolvedRoot = path.resolve(root); const resolved = path.resolve(resolvedRoot, relativePath); const relative = path.relative(resolvedRoot, resolved); if (relative.startsWith('..') || path.isAbsolute(relative)) return null; return resolved; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS] }; }
async function writeAndReturn0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const absoluteOutputPath = path.join(root, outputPath); await mkdir(path.dirname(absoluteOutputPath), { recursive: true }); await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function stableStringify0(value) { if (value === null || typeof value !== 'object') return JSON.stringify(value); if (Array.isArray(value)) return `[${value.map((entry) => stableStringify0(entry)).join(',')}]`; return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const options = { root: process.cwd(), outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false }; for (let index = 0; index < argv.length; index += 1) { const arg = argv[index]; if (arg === '--json') options.json = true; else if (arg === '--no-write') options.writeOutput = false; else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root'); else if (arg === '--manifest') options.manifestPath = requireValue0(argv, ++index, '--manifest'); else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output'); else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); } else throw new Error(`unknown argument: ${arg}`); } return options; }
function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node pcc-direct-bind-base-semantics0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/direct-bind-base-semantics/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --manifest <path>  Manifest JSON path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad Base direct-binding seed CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckBaseDirectBindingSeed0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
