#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckReportTheoremCoverageClosurePlan0';
const VERSION = 0;
const PLAN_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json';
const MATRIX_PATH = 'report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/report-theorem-coverage-closure-plan/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-REPORT-THEOREM-COVERAGE-CLOSURE-PLAN-2026-06-27-01';
const EXPECTED_MATRIX_COORDINATE = 'PNP-REPORT-THEOREM-COVERAGE-MATRIX-2026-06-27-01';
const EXPECTED_INVENTORY_COORDINATE = 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_LABELS = ['Base', 'CHG', 'Mode', 'E', 'N', 'FT', 'X', 'BC', 'UN', 'HN', 'HResolve', 'BUD', 'NOR/FF', 'RW', 'BN2', 'BN3', 'BN4', 'BN5', 'PkgC', 'BN6', 'Packet', 'R', 'HB', 'O', 'G', 'Final', 'PACK'];
const EXPECTED_CLOSURE_IDS = EXPECTED_LABELS.map((label, index) => `DCC-${String(index + 1).padStart(3, '0')}-${label.replace('/', '-')}`);
const EXPECTED_COVERAGE_IDS = EXPECTED_LABELS.map((label, index) => `COV-${String(index + 1).padStart(3, '0')}-${label.replace('/', '-')}`);
const EXPECTED_INVENTORY_IDS = EXPECTED_LABELS.map((label, index) => `TL-${String(index + 1).padStart(3, '0')}-${label.replace('/', '-')}`);
const ALLOWED_CLOSURE_STATUSES = ['direct-binding-needed', 'direct-binding-seed-upgrade-needed', 'blocked-by-unrestricted-final-soundness', 'release-boundary-blocked'];
const EXPECTED_RULE_IDS = ['DCP-001-NoSilentDirectBinding', 'DCP-002-ExactCoverageRowAlignment', 'DCP-003-ReleaseCriticalRowsBlocked', 'DCP-004-UniformityRowsBlocked', 'DCP-005-NoPublicEmissionFromClosure'];

export async function CheckReportTheoremCoverageClosurePlan0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const planRead = await readJson0({ root, filePath: options.planPath ?? PLAN_PATH, override: options.planOverride, label: 'coverage closure plan' });
    if (planRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, planRead);
    const matrixRead = await readJson0({ root, filePath: options.matrixPath ?? MATRIX_PATH, override: options.matrixOverride, label: 'coverage matrix' });
    if (matrixRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, matrixRead);
    const statusRead = await readJson0({ root, filePath: options.statusPath ?? STATUS_PATH, override: options.statusOverride, label: 'PNP status' });
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    const planValidation = validatePlan0(planRead.value);
    if (planValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, planValidation);
    const linkedValidation = validateLinked0({ plan: planRead.value, matrix: matrixRead.value, status: statusRead.value });
    if (linkedValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, linkedValidation);
    const digest = await digestEvidence0(root, planRead.value);
    if (digest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, digest);

    const closureStatusCounts = countBy0(planRead.value.closureEntries.map((entry) => entry.closureStatus));
    const releaseBlockedCount = planRead.value.closureEntries.filter((entry) => entry.closureStatus === 'release-boundary-blocked').length;
    const unrestrictedBlockedCount = planRead.value.closureEntries.filter((entry) => entry.closureStatus === 'blocked-by-unrestricted-final-soundness').length;

    return writeAndReturn0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'report-theorem-coverage-closure-plan-accepted-under-public-review-boundary',
      planPath: options.planPath ?? PLAN_PATH,
      matrixPath: options.matrixPath ?? MATRIX_PATH,
      planSha256: sha256Hex0(planRead.bytes),
      matrixSha256: sha256Hex0(matrixRead.bytes),
      statusSha256: sha256Hex0(statusRead.bytes),
      closurePlanReady: true,
      allCoverageRowsHaveClosureEntries: true,
      allInventoryRowsDirectCheckerBound: false,
      directCheckerBindingCompleteCount: 0,
      fullHistoricalReportTheoremCoverageProved: false,
      publicTheoremEmissionAllowedByClosurePlan: false,
      closureEntryCount: planRead.value.closureEntries.length,
      directBindingTargetCount: planRead.value.coverageClosureScope.directBindingTargetCount,
      closureStatusCounts,
      releaseBoundaryBlockedCount: releaseBlockedCount,
      unrestrictedFinalSoundnessBlockedCount: unrestrictedBlockedCount,
      evidenceFileCount: digest.evidenceFiles.length,
      closureDigestSha256: sha256Text0(stableStringify0(digest.closureDigests)),
      evidenceDigestSha256: sha256Text0(stableStringify0(digest.evidenceFiles)),
      closureDigests: digest.closureDigests,
      evidenceFiles: digest.evidenceFiles,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('ReportTheoremCoverageClosurePlan.UnhandledException', [], 'coverage closure plan checker threw unexpectedly', normalizeError0(error)));
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
    return reject0('ReportTheoremCoverageClosurePlan.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validatePlan0(plan) {
  if (!plain0(plan)) return reject0('ReportTheoremCoverageClosurePlan.Shape', [], 'plan must be an object');
  if (plan.kind !== 'PNPReportTheoremCoverageClosurePlan0') return reject0('ReportTheoremCoverageClosurePlan.Kind', ['kind'], 'plan kind mismatch');
  if (plan.version !== VERSION) return reject0('ReportTheoremCoverageClosurePlan.Version', ['version'], 'plan version mismatch');
  if (plan.coordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremCoverageClosurePlan.Coordinate', ['coordinate'], 'plan coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: plan.coordinate });
  if (plan.status !== 'report-theorem-coverage-closure-plan-ready') return reject0('ReportTheoremCoverageClosurePlan.Status', ['status'], 'plan status mismatch');

  const flagExpectations = {
    closurePlanReady: true,
    allCoverageRowsHaveClosureEntries: true,
    allInventoryRowsDirectCheckerBound: false,
    directCheckerBindingCompleteCount: 0,
    fullHistoricalReportTheoremCoverageProved: false,
    publicTheoremEmissionAllowedByClosurePlan: false,
  };
  for (const [field, expected] of Object.entries(flagExpectations)) if (plan[field] !== expected) return reject0('ReportTheoremCoverageClosurePlan.Flag', [field], 'closure plan flag mismatch', { expected, actual: plan[field] });
  const boundary = validateBoundary0(plan.claimBoundary, ['claimBoundary']);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(plan.coverageClosureScope)) return reject0('ReportTheoremCoverageClosurePlan.ScopeShape', ['coverageClosureScope'], 'coverageClosureScope must be an object');
  const scope = plan.coverageClosureScope;
  if (scope.mode !== 'row-by-row-direct-checker-binding-backlog') return reject0('ReportTheoremCoverageClosurePlan.ScopeMode', ['coverageClosureScope', 'mode'], 'scope mode mismatch');
  if (scope.coverageMatrixCoordinate !== EXPECTED_MATRIX_COORDINATE || scope.inventoryCoordinate !== EXPECTED_INVENTORY_COORDINATE) return reject0('ReportTheoremCoverageClosurePlan.ScopeCoordinate', ['coverageClosureScope'], 'linked scope coordinate mismatch');
  if (scope.expectedClosureEntryCount !== EXPECTED_CLOSURE_IDS.length || scope.directBindingTargetCount !== EXPECTED_CLOSURE_IDS.length) return reject0('ReportTheoremCoverageClosurePlan.ScopeCounts', ['coverageClosureScope'], 'scope counts mismatch');
  if (scope.closurePlanIsActivationSafe !== true || scope.futureDirectBindingPRsRequired !== true) return reject0('ReportTheoremCoverageClosurePlan.ScopePolicyFlags', ['coverageClosureScope'], 'scope policy flags mismatch');

  if (!sameArray0(plan.allowedClosureStatuses, ALLOWED_CLOSURE_STATUSES)) return reject0('ReportTheoremCoverageClosurePlan.AllowedStatuses', ['allowedClosureStatuses'], 'allowed closure statuses mismatch', { expected: ALLOWED_CLOSURE_STATUSES, actual: plan.allowedClosureStatuses });
  if (!Array.isArray(plan.closureRules)) return reject0('ReportTheoremCoverageClosurePlan.RulesShape', ['closureRules'], 'closureRules must be an array');
  const ruleIds = plan.closureRules.map((rule) => rule?.id);
  if (!sameArray0(ruleIds, EXPECTED_RULE_IDS)) return reject0('ReportTheoremCoverageClosurePlan.RuleIds', ['closureRules'], 'closure rule ids mismatch', { expected: EXPECTED_RULE_IDS, actual: ruleIds });
  for (let index = 0; index < plan.closureRules.length; index += 1) {
    const rule = plan.closureRules[index];
    if (!plain0(rule) || !nonempty0(rule.description) || rule.enforcedBy !== 'pcc-report-theorem-coverage-closure-plan0.mjs') return reject0('ReportTheoremCoverageClosurePlan.RuleShape', ['closureRules', index], 'closure rule must have description and expected checker');
  }

  if (!Array.isArray(plan.closureEntries)) return reject0('ReportTheoremCoverageClosurePlan.EntriesShape', ['closureEntries'], 'closureEntries must be an array');
  const ids = plan.closureEntries.map((entry) => entry?.id);
  if (!sameArray0(ids, EXPECTED_CLOSURE_IDS)) return reject0('ReportTheoremCoverageClosurePlan.ClosureIds', ['closureEntries'], 'closure ids must stay exact and ordered', { expected: EXPECTED_CLOSURE_IDS, actual: ids });
  for (let index = 0; index < plan.closureEntries.length; index += 1) {
    const check = validateClosureEntry0(plan.closureEntries[index], ['closureEntries', index], index);
    if (check.tag === 'reject') return check;
  }

  const nonClaimsCheck = validateStringArray0(plan.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;
  if (!plain0(plan.audit)) return reject0('ReportTheoremCoverageClosurePlan.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = { checker: CHECKER, script: 'pcc-report-theorem-coverage-closure-plan0.mjs', test: 'audits/report-theorem-coverage-closure-plan0.test.mjs', expectedAcceptTag: 'accept' };
  for (const [key, expected] of Object.entries(expectedAudit)) if (plan.audit[key] !== expected) return reject0('ReportTheoremCoverageClosurePlan.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: plan.audit[key] });
  return { tag: 'accept' };
}

function validateClosureEntry0(entry, pathArray, index) {
  if (!plain0(entry)) return reject0('ReportTheoremCoverageClosurePlan.EntryShape', pathArray, 'closure entry must be an object');
  const expected = { coverageEntryId: EXPECTED_COVERAGE_IDS[index], inventoryEntryId: EXPECTED_INVENTORY_IDS[index], sourceLabel: EXPECTED_LABELS[index] };
  for (const [field, expectedValue] of Object.entries(expected)) if (entry[field] !== expectedValue) return reject0('ReportTheoremCoverageClosurePlan.EntryAlignment', [...pathArray, field], 'closure entry alignment mismatch', { expected: expectedValue, actual: entry[field] });
  for (const field of ['currentCoverageClass', 'closureStatus', 'nextDirectBindingSurface', 'publicEmissionEffect']) if (!nonempty0(entry[field])) return reject0('ReportTheoremCoverageClosurePlan.EntryField', [...pathArray, field], 'closure entry field must be a non-empty string');
  if (!ALLOWED_CLOSURE_STATUSES.includes(entry.closureStatus)) return reject0('ReportTheoremCoverageClosurePlan.ClosureStatus', [...pathArray, 'closureStatus'], 'closure status is not allowed', { actual: entry.closureStatus });
  const requiredCheck = validateStringArray0(entry.requiredNewSurfaces, [...pathArray, 'requiredNewSurfaces'], true);
  if (requiredCheck.tag === 'reject') return requiredCheck;
  const gapCheck = validateStringArray0(entry.blockingGaps, [...pathArray, 'blockingGaps'], false);
  if (gapCheck.tag === 'reject') return gapCheck;
  if (entry.mayFlipDirectCheckerBindingComplete !== false) return reject0('ReportTheoremCoverageClosurePlan.FlipFlag', [...pathArray, 'mayFlipDirectCheckerBindingComplete'], 'closure entries cannot allow direct binding flip in this plan');
  if (entry.publicEmissionEffect !== 'none' || entry.dischargesPublicTheorem !== false) return reject0('ReportTheoremCoverageClosurePlan.EntryPublicEmission', pathArray, 'closure entries cannot discharge public theorem');
  if (entry.currentCoverageClass === 'release-critical-boundary-surface' && entry.closureStatus !== 'release-boundary-blocked') return reject0('ReportTheoremCoverageClosurePlan.ReleaseBoundaryStatus', pathArray, 'release-critical rows must be release-boundary-blocked');
  if (entry.closureStatus === 'blocked-by-unrestricted-final-soundness' && !entry.blockingGaps.includes('GAP-001-UnrestrictedFinalSoundness')) return reject0('ReportTheoremCoverageClosurePlan.UnrestrictedGapMissing', pathArray, 'unrestricted final soundness blocked entries must cite GAP-001');
  if (entry.sourceLabel === 'Final' || entry.sourceLabel === 'PACK') {
    if (entry.closureStatus !== 'release-boundary-blocked' || !entry.blockingGaps.includes('GAP-002-ExternalReviewAcceptance')) return reject0('ReportTheoremCoverageClosurePlan.FinalPackBoundary', pathArray, 'Final and PACK must remain release-boundary-blocked with external review blocker');
  }
  return { tag: 'accept' };
}

function validateLinked0({ plan, matrix, status }) {
  if (!plain0(matrix) || matrix.kind !== 'PNPReportTheoremCoverageMatrix0') return reject0('ReportTheoremCoverageClosurePlan.MatrixKind', [MATRIX_PATH], 'coverage matrix kind mismatch');
  if (matrix.coordinate !== EXPECTED_MATRIX_COORDINATE) return reject0('ReportTheoremCoverageClosurePlan.MatrixCoordinate', [MATRIX_PATH, 'coordinate'], 'coverage matrix coordinate mismatch');
  if (!Array.isArray(matrix.coverageEntries)) return reject0('ReportTheoremCoverageClosurePlan.MatrixEntriesShape', [MATRIX_PATH, 'coverageEntries'], 'coverage matrix entries must be an array');
  if (matrix.coverageEntries.length !== plan.closureEntries.length) return reject0('ReportTheoremCoverageClosurePlan.MatrixEntryCount', [MATRIX_PATH, 'coverageEntries'], 'matrix and closure entry counts must match');
  for (let index = 0; index < plan.closureEntries.length; index += 1) {
    const closure = plan.closureEntries[index];
    const coverage = matrix.coverageEntries[index];
    if (closure.coverageEntryId !== coverage.id || closure.inventoryEntryId !== coverage.inventoryEntryId || closure.sourceLabel !== coverage.sourceLabel || closure.currentCoverageClass !== coverage.coverageClass) return reject0('ReportTheoremCoverageClosurePlan.MatrixAlignment', ['closureEntries', index], 'closure entry must align with coverage matrix row');
    if (coverage.directCheckerBindingComplete !== false || coverage.publicEmissionEffect !== 'none' || coverage.dischargesPublicTheorem !== false) return reject0('ReportTheoremCoverageClosurePlan.MatrixOverclaim', [MATRIX_PATH, 'coverageEntries', index], 'coverage matrix row cannot overclaim direct binding or public theorem');
  }
  if (matrix.allInventoryEntriesDirectCheckerBound !== false || matrix.fullHistoricalReportTheoremCoverageProved !== false || matrix.publicTheoremEmissionAllowedByCoverage !== false) return reject0('ReportTheoremCoverageClosurePlan.MatrixFlags', [MATRIX_PATH], 'coverage matrix cannot overclaim under closure plan');

  if (!plain0(status) || status.kind !== 'PNPStatus0') return reject0('ReportTheoremCoverageClosurePlan.StatusKind', [STATUS_PATH], 'status kind mismatch');
  if (status.reportTheoremCoverageClosurePlanCoordinate !== EXPECTED_COORDINATE) return reject0('ReportTheoremCoverageClosurePlan.StatusCoordinate', [STATUS_PATH, 'reportTheoremCoverageClosurePlanCoordinate'], 'status must bind coverage closure plan coordinate');
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false || !sameArray0(status.activeFinalNodeIds, []) || !sameArray0(status.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReportTheoremCoverageClosurePlan.StatusBoundary', [STATUS_PATH], 'status boundary mismatch');
  return { tag: 'accept' };
}

async function digestEvidence0(root, plan) {
  const evidenceMap = new Map();
  const always = [PLAN_PATH, MATRIX_PATH, STATUS_PATH, 'report-bindings/REPORT_THEOREM_INVENTORY.json', 'proof-obligations/GAP_LEDGER.json', 'proof-obligations/OBLIGATION_LEDGER.json'];
  for (const relativePath of always) {
    const file = await digestFile0(root, relativePath, ['evidence']);
    if (file.tag === 'reject') return file;
    evidenceMap.set(relativePath, file);
  }
  const closureDigests = [];
  for (const entry of plan.closureEntries) {
    const localEvidence = [];
    const candidateEvidence = ['report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json', 'report-bindings/REPORT_THEOREM_INVENTORY.json', ...entry.blockingGaps.length > 0 ? ['proof-obligations/GAP_LEDGER.json'] : []];
    for (const relativePath of candidateEvidence) {
      let file = evidenceMap.get(relativePath);
      if (!file) {
        file = await digestFile0(root, relativePath, ['closureEntries', entry.id, 'evidence']);
        if (file.tag === 'reject') return file;
        evidenceMap.set(relativePath, file);
      }
      localEvidence.push(file);
    }
    closureDigests.push({ id: entry.id, coverageEntryId: entry.coverageEntryId, closureStatus: entry.closureStatus, blockingGaps: entry.blockingGaps, evidenceDigest: sha256Text0(stableStringify0(localEvidence)) });
  }
  return { tag: 'accept', closureDigests, evidenceFiles: [...evidenceMap.values()].sort((a, b) => a.path.localeCompare(b.path)) };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('ReportTheoremCoverageClosurePlan.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('ReportTheoremCoverageClosurePlan.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('ReportTheoremCoverageClosurePlan.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateBoundary0(boundary, pathArray) {
  if (!plain0(boundary)) return reject0('ReportTheoremCoverageClosurePlan.BoundaryShape', pathArray, 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ReportTheoremCoverageClosurePlan.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ReportTheoremCoverageClosurePlan.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('ReportTheoremCoverageClosurePlan.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReportTheoremCoverageClosurePlan.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('ReportTheoremCoverageClosurePlan.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('ReportTheoremCoverageClosurePlan.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('ReportTheoremCoverageClosurePlan.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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
function countBy0(values) { const map = new Map(); for (const value of values) map.set(value, (map.get(value) ?? 0) + 1); return Object.fromEntries([...map.entries()].sort(([a], [b]) => a.localeCompare(b))); }
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
    else if (arg === '--plan') options.planPath = requireValue0(argv, ++index, '--plan');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}
function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node pcc-report-theorem-coverage-closure-plan0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/report-theorem-coverage-closure-plan/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --plan <path>      Closure plan JSON path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('Cli.BadArgument', [], 'bad theorem coverage closure plan CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckReportTheoremCoverageClosurePlan0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
