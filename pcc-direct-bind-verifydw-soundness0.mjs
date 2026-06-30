#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckEDirectBindingSeed0';
const VERSION = 0;
const MANIFEST_PATH = 'report-bindings/direct-bindings/E_DIRECT_BINDING_SEED.json';
const INVENTORY_PATH = 'report-bindings/REPORT_THEOREM_INVENTORY.json';
const MATRIX_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json';
const CLOSURE_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json';
const OBLIGATIONS_PATH = 'proof-obligations/OBLIGATION_LEDGER.json';
const GAPS_PATH = 'proof-obligations/GAP_LEDGER.json';
const ORACLE_AUDIT_PATH = 'oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/direct-bind-verifydw-soundness/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-DIRECT-BIND-E-VERIFYDW-SOUNDNESS-SEED-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_COMPONENT_IDS = ['E.VerifyDWSoundnessSurface', 'E.ObligationFlatteningSurface', 'E.NoHiddenOracleExecutableBoundary', 'E.NoHiddenOracleSemanticCompletenessGap'];

export async function CheckEDirectBindingSeed0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? MANIFEST_PATH, options.manifestOverride, 'E direct-binding seed manifest');
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);
    const inventoryRead = await readJson0(root, options.inventoryPath ?? INVENTORY_PATH, options.inventoryOverride, 'report theorem inventory');
    if (inventoryRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventoryRead);
    const matrixRead = await readJson0(root, options.matrixPath ?? MATRIX_PATH, options.matrixOverride, 'report theorem coverage matrix');
    if (matrixRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, matrixRead);
    const closureRead = await readJson0(root, options.closurePath ?? CLOSURE_PATH, options.closureOverride, 'report theorem coverage closure plan');
    if (closureRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, closureRead);
    const obligationsRead = await readJson0(root, options.obligationsPath ?? OBLIGATIONS_PATH, options.obligationsOverride, 'proof obligation ledger');
    if (obligationsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, obligationsRead);
    const gapsRead = await readJson0(root, options.gapsPath ?? GAPS_PATH, options.gapsOverride, 'gap ledger');
    if (gapsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, gapsRead);
    const oracleRead = await readJson0(root, options.oraclePath ?? ORACLE_AUDIT_PATH, options.oracleOverride, 'no-hidden-oracle audit');
    if (oracleRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, oracleRead);
    const statusRead = await readJson0(root, options.statusPath ?? STATUS_PATH, options.statusOverride, 'PNP status');
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    for (const check of [validateManifest0(manifestRead.value), validateInventory0(inventoryRead.value), validateMatrix0(matrixRead.value), validateClosure0(closureRead.value), validateObligations0(obligationsRead.value), validateGaps0(gapsRead.value), validateOracleAudit0(oracleRead.value), validateStatus0(statusRead.value)]) {
      if (check.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, check);
    }
    const evidence = await digestEvidence0(root, manifestRead.value.evidenceSurfaces);
    if (evidence.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, evidence);

    return writeAndReturn0(root, outputPath, writeOutput, {
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: EXPECTED_COORDINATE,
      claimStatus: 'e-direct-binding-seed-accepted-under-public-review-boundary', manifestPath: options.manifestPath ?? MANIFEST_PATH,
      manifestSha256: sha256Hex0(manifestRead.bytes), inventorySha256: sha256Hex0(inventoryRead.bytes), matrixSha256: sha256Hex0(matrixRead.bytes), closurePlanSha256: sha256Hex0(closureRead.bytes), proofObligationLedgerSha256: sha256Hex0(obligationsRead.bytes), gapLedgerSha256: sha256Hex0(gapsRead.bytes), noHiddenOracleAuditSha256: sha256Hex0(oracleRead.bytes), statusSha256: sha256Hex0(statusRead.bytes),
      eDirectBindingSeedReady: true, boundInventoryEntryId: 'TL-004-E', boundCoverageEntryId: 'COV-004-E', boundClosureEntryId: 'DCC-004-E', coveredEComponents: [...EXPECTED_COMPONENT_IDS], directCheckerBindingComplete: false, fullHistoricalETheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false,
      evidenceFileCount: evidence.files.length, evidenceDigestSha256: sha256Text0(stableStringify0(evidence.files)), evidenceFiles: evidence.files,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS], outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('EDirectBindingSeed.UnhandledException', [], 'E direct-binding seed checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readJson0(root, filePath, override, label) {
  if (override !== undefined) return { tag: 'accept', value: override, bytes: Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8') };
  try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('EDirectBindingSeed.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('EDirectBindingSeed.ManifestShape', [], 'manifest must be an object');
  const exact = { kind: 'PNPEDirectBindingSeed0', version: VERSION, coordinate: EXPECTED_COORDINATE, status: 'e-direct-binding-seed-ready', eDirectBindingSeedReady: true, releaseCriticalRow: false, directCheckerBindingComplete: false, fullHistoricalETheoremDischarged: false, publicTheoremEmissionAllowedByBinding: false };
  for (const [field, expected] of Object.entries(exact)) if (manifest[field] !== expected) return reject0(`EDirectBindingSeed.Manifest.${field}`, [field], 'manifest field mismatch', { expected, actual: manifest[field] });
  const boundary = validateBoundary0(manifest.claimBoundary, ['claimBoundary']); if (boundary.tag === 'reject') return boundary;
  const expectedLinks = { reportTheoremInventory: 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01', reportTheoremCoverageMatrix: 'PNP-REPORT-THEOREM-COVERAGE-MATRIX-2026-06-27-01', reportTheoremCoverageClosurePlan: 'PNP-REPORT-THEOREM-COVERAGE-CLOSURE-PLAN-2026-06-27-01', proofObligationLedger: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01', gapLedger: 'PNP-GAP-LEDGER-2026-06-27-01', noHiddenOracleAudit: 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01' };
  if (!plain0(manifest.linkedCoordinates)) return reject0('EDirectBindingSeed.LinkedShape', ['linkedCoordinates'], 'linkedCoordinates must be an object');
  for (const [field, expected] of Object.entries(expectedLinks)) if (manifest.linkedCoordinates[field] !== expected) return reject0('EDirectBindingSeed.LinkedCoordinate', ['linkedCoordinates', field], 'linked coordinate mismatch', { expected, actual: manifest.linkedCoordinates[field] });
  const bound = manifest.boundInventoryEntry;
  if (!plain0(bound) || bound.inventoryEntryId !== 'TL-004-E' || bound.coverageEntryId !== 'COV-004-E' || bound.closureEntryId !== 'DCC-004-E' || bound.sourceLabel !== 'E' || bound.expectedCoverageClass !== 'obligation-ledger-surface' || bound.expectedClosureStatus !== 'direct-binding-needed' || bound.expectedNextDirectBindingSurface !== 'pcc-direct-bind-verifydw-soundness0.mjs') return reject0('EDirectBindingSeed.BoundEntry', ['boundInventoryEntry'], 'bound inventory entry mismatch');
  const componentIds = Array.isArray(manifest.coveredEComponents) ? manifest.coveredEComponents.map((entry) => entry?.id) : [];
  if (!sameArray0(componentIds, EXPECTED_COMPONENT_IDS)) return reject0('EDirectBindingSeed.ComponentIds', ['coveredEComponents'], 'covered component ids must stay exact and ordered', { expected: EXPECTED_COMPONENT_IDS, actual: componentIds });
  for (const entry of manifest.coveredEComponents) if (!plain0(entry) || !nonempty0(entry.status) || !nonempty0(entry.evidence)) return reject0('EDirectBindingSeed.ComponentShape', ['coveredEComponents'], 'component entries must declare status and evidence');
  for (const [field, nonEmpty] of [['evidenceSurfaces', true], ['nonClaims', true]]) { const check = validateStringArray0(manifest[field], [field], nonEmpty); if (check.tag === 'reject') return check; }
  const expectedAudit = { checker: CHECKER, script: 'pcc-direct-bind-verifydw-soundness0.mjs', test: 'audits/direct-bind-verifydw-soundness0.test.mjs', expectedAcceptTag: 'accept' };
  if (!plain0(manifest.audit)) return reject0('EDirectBindingSeed.AuditShape', ['audit'], 'audit must be an object');
  for (const [field, expected] of Object.entries(expectedAudit)) if (manifest.audit[field] !== expected) return reject0('EDirectBindingSeed.AuditField', ['audit', field], 'audit field mismatch', { expected, actual: manifest.audit[field] });
  return { tag: 'accept' };
}

function validateInventory0(inventory) { const entry = Array.isArray(inventory?.inventoryEntries) ? inventory.inventoryEntries.find((item) => item.id === 'TL-004-E') : null; if (!plain0(inventory) || inventory.kind !== 'PNPReportTheoremInventory0') return reject0('EDirectBindingSeed.InventoryKind', [INVENTORY_PATH], 'inventory kind mismatch'); if (!plain0(entry)) return reject0('EDirectBindingSeed.InventoryEMissing', [INVENTORY_PATH, 'inventoryEntries'], 'TL-004-E entry missing'); if (entry.sourceLabel !== 'E' || !String(entry.content).includes('VerifyDW soundness') || !String(entry.content).includes('obligation flattening') || !String(entry.content).includes('no hidden minimization') || entry.publicEmissionEffect !== 'none' || entry.dischargesPublicTheorem !== false) return reject0('EDirectBindingSeed.InventoryEMismatch', [INVENTORY_PATH, 'TL-004-E'], 'E inventory row mismatch'); return { tag: 'accept' }; }
function validateMatrix0(matrix) { const row = Array.isArray(matrix?.coverageEntries) ? matrix.coverageEntries.find((entry) => entry.id === 'COV-004-E') : null; if (!plain0(matrix) || matrix.kind !== 'PNPReportTheoremCoverageMatrix0') return reject0('EDirectBindingSeed.MatrixKind', [MATRIX_PATH], 'coverage matrix kind mismatch'); if (!plain0(row)) return reject0('EDirectBindingSeed.MatrixEMissing', [MATRIX_PATH, 'coverageEntries'], 'COV-004-E row missing'); if (row.inventoryEntryId !== 'TL-004-E' || row.sourceLabel !== 'E' || row.coverageClass !== 'obligation-ledger-surface' || row.representedByMachineLedger !== true || row.directCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('EDirectBindingSeed.MatrixEMismatch', [MATRIX_PATH, 'COV-004-E'], 'E coverage row mismatch'); if (!Array.isArray(row.relatedObligations) || !row.relatedObligations.includes('OBL-006-CheckerSoundnessSeedAudits') || !row.relatedObligations.includes('OBL-011-NoHiddenOracleSourceSurface')) return reject0('EDirectBindingSeed.MatrixObligationMissing', [MATRIX_PATH, 'COV-004-E', 'relatedObligations'], 'E coverage row must cite checker and no-hidden-oracle obligations'); return { tag: 'accept' }; }
function validateClosure0(closure) { const row = Array.isArray(closure?.closureEntries) ? closure.closureEntries.find((entry) => entry.id === 'DCC-004-E') : null; if (!plain0(closure) || closure.kind !== 'PNPReportTheoremCoverageClosurePlan0') return reject0('EDirectBindingSeed.ClosureKind', [CLOSURE_PATH], 'coverage closure plan kind mismatch'); if (!plain0(row)) return reject0('EDirectBindingSeed.ClosureEMissing', [CLOSURE_PATH, 'closureEntries'], 'DCC-004-E row missing'); if (row.coverageEntryId !== 'COV-004-E' || row.inventoryEntryId !== 'TL-004-E' || row.sourceLabel !== 'E' || row.currentCoverageClass !== 'obligation-ledger-surface' || row.closureStatus !== 'direct-binding-needed' || row.nextDirectBindingSurface !== 'pcc-direct-bind-verifydw-soundness0.mjs' || row.mayFlipDirectCheckerBindingComplete !== false || row.publicEmissionEffect !== 'none' || row.dischargesPublicTheorem !== false) return reject0('EDirectBindingSeed.ClosureEMismatch', [CLOSURE_PATH, 'DCC-004-E'], 'E closure row mismatch'); if (!Array.isArray(row.blockingGaps) || !row.blockingGaps.includes('GAP-005-NoHiddenOracleSemanticCompleteness')) return reject0('EDirectBindingSeed.ClosureGapMissing', [CLOSURE_PATH, 'DCC-004-E', 'blockingGaps'], 'E closure row must cite the no-hidden-oracle semantic-completeness gap'); return { tag: 'accept' }; }
function validateObligations0(ledger) { if (!plain0(ledger) || ledger.kind !== 'PNPProofObligationLedger0' || ledger.publicTheoremEmissionAllowedByLedger !== false || ledger.fullProofObligationDischargeProved !== false) return reject0('EDirectBindingSeed.ObligationLedgerMismatch', [OBLIGATIONS_PATH], 'proof obligation ledger mismatch'); const ids = new Set(Array.isArray(ledger.obligations) ? ledger.obligations.map((entry) => entry.id) : []); for (const required of ['OBL-006-CheckerSoundnessSeedAudits', 'OBL-011-NoHiddenOracleSourceSurface', 'OBL-019-EDirectBindingSeed']) if (!ids.has(required)) return reject0('EDirectBindingSeed.ObligationMissing', [OBLIGATIONS_PATH, 'obligations'], 'required obligation missing', { required }); return { tag: 'accept' }; }
function validateGaps0(gaps) { if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0' || gaps.gapLedgerClaimsNoRemainingGaps !== false || gaps.fullGapClosureProved !== false || gaps.publicTheoremEmissionAllowedByLedger !== false) return reject0('EDirectBindingSeed.GapLedgerMismatch', [GAPS_PATH], 'gap ledger cannot overclaim closure'); const gap = Array.isArray(gaps.gaps) ? gaps.gaps.find((entry) => entry.id === 'GAP-005-NoHiddenOracleSemanticCompleteness') : null; if (!plain0(gap) || gap.status !== 'represented-not-discharged' || gap.publicTheoremEmissionAllowedByGap !== false) return reject0('EDirectBindingSeed.Gap005Mismatch', [GAPS_PATH, 'GAP-005-NoHiddenOracleSemanticCompleteness'], 'GAP-005 must remain represented but not discharged'); return { tag: 'accept' }; }
function validateOracleAudit0(audit) { if (!plain0(audit) || audit.kind !== 'PNPNoHiddenOracleAudit0' || audit.coordinate !== 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01' || audit.noHiddenOracleAuditReady !== true || audit.fullNoHiddenOracleProved !== false || audit.publicTheoremEmissionAllowedByAudit !== false) return reject0('EDirectBindingSeed.NoHiddenOracleAuditMismatch', [ORACLE_AUDIT_PATH], 'no-hidden-oracle audit mismatch'); return { tag: 'accept' }; }
function validateStatus0(status) { if (!plain0(status) || status.kind !== 'PNPStatus0') return reject0('EDirectBindingSeed.StatusKind', [STATUS_PATH], 'status kind mismatch'); if (status.eDirectBindingSeedCoordinate !== EXPECTED_COORDINATE) return reject0('EDirectBindingSeed.StatusCoordinate', ['eDirectBindingSeedCoordinate'], 'status must bind E direct-binding seed coordinate'); if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('EDirectBindingSeed.StatusBoundary', [STATUS_PATH], 'status boundary mismatch'); return { tag: 'accept' }; }

async function digestEvidence0(root, paths) { const files = []; for (const relativePath of paths) { const file = await digestFile0(root, relativePath, ['evidenceSurfaces']); if (file.tag === 'reject') return file; files.push(file); } return { tag: 'accept', files }; }
async function digestFile0(root, relativePath, pathArray) { const safePath = safeJoin0(root, relativePath); if (safePath === null) return reject0('EDirectBindingSeed.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root'); try { const info = await stat(safePath); if (!info.isFile()) return reject0('EDirectBindingSeed.PathNotFile', [...pathArray, relativePath], 'path must be a file'); const bytes = await readFile(safePath); return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length }; } catch (error) { return reject0('EDirectBindingSeed.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error)); } }
function validateBoundary0(boundary, pathArray) { if (!plain0(boundary)) return reject0('EDirectBindingSeed.BoundaryShape', pathArray, 'boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false) return reject0('EDirectBindingSeed.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled'); if (boundary.finalTheoremReady !== false) return reject0('EDirectBindingSeed.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled'); if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('EDirectBindingSeed.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must remain empty'); if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('EDirectBindingSeed.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact'); return { tag: 'accept' }; }
function validateStringArray0(value, pathArray, nonEmpty) { if (!Array.isArray(value)) return reject0('EDirectBindingSeed.StringArrayShape', pathArray, 'field must be an array of strings'); if (nonEmpty && value.length === 0) return reject0('EDirectBindingSeed.StringArrayEmpty', pathArray, 'field must not be empty'); for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('EDirectBindingSeed.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
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
function printHelp0() { console.log(`Usage: node pcc-direct-bind-verifydw-soundness0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/direct-bind-verifydw-soundness/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --manifest <path>  Manifest JSON path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad E direct-binding seed CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckEDirectBindingSeed0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
