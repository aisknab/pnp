#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckNoProseOnlyTheoremPolicy0';
const VERSION = 0;
const POLICY_PATH = 'report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json';
const BINDINGS_PATH = 'report-bindings/REPORT_THEOREM_BINDINGS.json';
const OBLIGATIONS_PATH = 'proof-obligations/OBLIGATION_LEDGER.json';
const GAPS_PATH = 'proof-obligations/GAP_LEDGER.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/no-prose-only-theorem-policy/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-NO-PROSE-ONLY-THEOREM-POLICY-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_RULE_IDS = [
  'NPT-001-BoundTheoremEntries',
  'NPT-002-NoPublicEmissionFromBindings',
  'NPT-003-ObligationsAndGapsRepresentReleaseCriticalSpine',
  'NPT-004-HistoricalTheoremLanguageFenced',
  'NPT-005-ExhaustivenessNotOverclaimed',
];

export async function CheckNoProseOnlyTheoremPolicy0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const policyRead = await readJson0({ root, filePath: options.policyPath ?? POLICY_PATH, override: options.policyOverride, label: 'no-prose-only theorem policy' });
    if (policyRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, policyRead);
    const bindingsRead = await readJson0({ root, filePath: options.bindingsPath ?? BINDINGS_PATH, override: options.bindingsOverride, label: 'theorem bindings ledger' });
    if (bindingsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, bindingsRead);
    const obligationsRead = await readJson0({ root, filePath: options.obligationsPath ?? OBLIGATIONS_PATH, override: options.obligationsOverride, label: 'proof obligation ledger' });
    if (obligationsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, obligationsRead);
    const gapsRead = await readJson0({ root, filePath: options.gapsPath ?? GAPS_PATH, override: options.gapsOverride, label: 'gap ledger' });
    if (gapsRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, gapsRead);
    const statusRead = await readJson0({ root, filePath: options.statusPath ?? STATUS_PATH, override: options.statusOverride, label: 'PNP status' });
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    const policyValidation = validatePolicy0(policyRead.value);
    if (policyValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, policyValidation);
    const bindingValidation = validateBindings0(bindingsRead.value, policyRead.value);
    if (bindingValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, bindingValidation);
    const obligationValidation = validateObligations0(obligationsRead.value, policyRead.value);
    if (obligationValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, obligationValidation);
    const gapValidation = validateGaps0(gapsRead.value);
    if (gapValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, gapValidation);
    const statusValidation = validateStatus0(statusRead.value);
    if (statusValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusValidation);

    const evidenceDigest = await digestEvidence0({ root, paths: policyRead.value.requiredEvidenceFiles });
    if (evidenceDigest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, evidenceDigest);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'no-prose-only-theorem-policy-accepted-under-public-review-boundary',
      policyPath: options.policyPath ?? POLICY_PATH,
      policySha256: sha256Hex0(policyRead.bytes),
      theoremBindingLedgerSha256: sha256Hex0(bindingsRead.bytes),
      proofObligationLedgerSha256: sha256Hex0(obligationsRead.bytes),
      gapLedgerSha256: sha256Hex0(gapsRead.bytes),
      statusSha256: sha256Hex0(statusRead.bytes),
      policyReady: true,
      releaseCriticalTheoremSpineCovered: true,
      allNumberedReportTheoremsCovered: false,
      fullReportTheoremInventoryExhaustive: false,
      proseOnlyTheoremActivationAllowed: false,
      publicTheoremEmissionAllowedByPolicy: false,
      theoremBindingCount: bindingsRead.value.theoremBindings.length,
      proofObligationCount: obligationsRead.value.obligations.length,
      gapCount: gapsRead.value.gaps.length,
      ruleCount: policyRead.value.policyRules.length,
      evidenceFileCount: evidenceDigest.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidenceDigest.evidence)),
      evidence: evidenceDigest.evidence,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('NoProseOnlyTheoremPolicy.UnhandledException', [], 'policy checker threw unexpectedly', normalizeError0(error)));
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
    return reject0('NoProseOnlyTheoremPolicy.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validatePolicy0(policy) {
  if (!plain0(policy)) return reject0('NoProseOnlyTheoremPolicy.PolicyShape', [], 'policy must be an object');
  if (policy.kind !== 'PNPNoProseOnlyTheoremPolicy0') return reject0('NoProseOnlyTheoremPolicy.PolicyKind', ['kind'], 'policy kind mismatch');
  if (policy.version !== VERSION) return reject0('NoProseOnlyTheoremPolicy.PolicyVersion', ['version'], 'policy version mismatch');
  if (policy.coordinate !== EXPECTED_COORDINATE) return reject0('NoProseOnlyTheoremPolicy.PolicyCoordinate', ['coordinate'], 'policy coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: policy.coordinate });
  if (policy.status !== 'no-prose-only-theorem-policy-ready') return reject0('NoProseOnlyTheoremPolicy.PolicyStatus', ['status'], 'policy status mismatch');
  if (policy.policyReady !== true) return reject0('NoProseOnlyTheoremPolicy.ReadyFlag', ['policyReady'], 'policyReady must be true');
  if (policy.releaseCriticalTheoremSpineCovered !== true) return reject0('NoProseOnlyTheoremPolicy.ReleaseCriticalFlag', ['releaseCriticalTheoremSpineCovered'], 'release-critical theorem spine must be covered');
  if (policy.allNumberedReportTheoremsCovered !== false) return reject0('NoProseOnlyTheoremPolicy.AllNumberedOverclaim', ['allNumberedReportTheoremsCovered'], 'policy cannot claim all numbered report theorems are covered yet');
  if (policy.fullReportTheoremInventoryExhaustive !== false) return reject0('NoProseOnlyTheoremPolicy.ExhaustiveInventoryOverclaim', ['fullReportTheoremInventoryExhaustive'], 'policy cannot claim exhaustive report theorem inventory yet');
  if (policy.proseOnlyTheoremActivationAllowed !== false) return reject0('NoProseOnlyTheoremPolicy.ProseActivationFlag', ['proseOnlyTheoremActivationAllowed'], 'prose-only theorem activation must be forbidden');
  if (policy.publicTheoremEmissionAllowedByPolicy !== false) return reject0('NoProseOnlyTheoremPolicy.PublicEmissionByPolicy', ['publicTheoremEmissionAllowedByPolicy'], 'policy cannot allow public theorem emission');

  const boundary = validateBoundary0(policy.claimBoundary, ['claimBoundary']);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(policy.coverageScope)) return reject0('NoProseOnlyTheoremPolicy.CoverageShape', ['coverageScope'], 'coverageScope must be an object');
  if (policy.coverageScope.mode !== 'release-critical-spine') return reject0('NoProseOnlyTheoremPolicy.CoverageMode', ['coverageScope', 'mode'], 'coverage mode must be release-critical-spine');
  if (policy.coverageScope.expectedTheoremBindingCount !== 20) return reject0('NoProseOnlyTheoremPolicy.BindingCountConfig', ['coverageScope', 'expectedTheoremBindingCount'], 'expected theorem binding count must be 20');
  if (policy.coverageScope.minimumProofObligationCount < 15) return reject0('NoProseOnlyTheoremPolicy.ObligationCountConfig', ['coverageScope', 'minimumProofObligationCount'], 'minimum proof obligation count must be at least 15');
  if (policy.coverageScope.minimumGapCount < 12) return reject0('NoProseOnlyTheoremPolicy.GapCountConfig', ['coverageScope', 'minimumGapCount'], 'minimum gap count must be at least 12');
  if (policy.coverageScope.finiteToUnboundedFamilyAuditCoordinate !== 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01') return reject0('NoProseOnlyTheoremPolicy.FiniteAuditCoordinate', ['coverageScope', 'finiteToUnboundedFamilyAuditCoordinate'], 'finite-to-unbounded audit coordinate mismatch');

  const evidenceCheck = validateStringArray0(policy.requiredEvidenceFiles, ['requiredEvidenceFiles'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;

  if (!Array.isArray(policy.policyRules)) return reject0('NoProseOnlyTheoremPolicy.PolicyRulesShape', ['policyRules'], 'policyRules must be an array');
  const actualRuleIds = policy.policyRules.map((rule) => rule?.id);
  if (!sameArray0(actualRuleIds, EXPECTED_RULE_IDS)) return reject0('NoProseOnlyTheoremPolicy.PolicyRuleIds', ['policyRules'], 'policy rule ids must stay exact and ordered', { expected: EXPECTED_RULE_IDS, actual: actualRuleIds });
  for (let index = 0; index < policy.policyRules.length; index += 1) {
    const rule = policy.policyRules[index];
    if (!plain0(rule) || !nonempty0(rule.description) || rule.enforcedBy !== 'pcc-no-prose-only-theorem-policy0.mjs') return reject0('NoProseOnlyTheoremPolicy.PolicyRuleShape', ['policyRules', index], 'policy rule must have description and expected checker');
  }

  if (!plain0(policy.currentVerdict)) return reject0('NoProseOnlyTheoremPolicy.CurrentVerdictShape', ['currentVerdict'], 'currentVerdict must be an object');
  if (policy.currentVerdict.noReleaseCriticalProseOnlyActivation !== true) return reject0('NoProseOnlyTheoremPolicy.CurrentVerdictActivation', ['currentVerdict', 'noReleaseCriticalProseOnlyActivation'], 'noReleaseCriticalProseOnlyActivation must be true');
  if (policy.currentVerdict.exhaustiveHistoricalReportCoverage !== false) return reject0('NoProseOnlyTheoremPolicy.CurrentVerdictExhaustiveOverclaim', ['currentVerdict', 'exhaustiveHistoricalReportCoverage'], 'current verdict cannot overclaim exhaustive historical coverage');
  if (policy.currentVerdict.activationBlockersCleared !== false) return reject0('NoProseOnlyTheoremPolicy.CurrentVerdictBlockersOverclaim', ['currentVerdict', 'activationBlockersCleared'], 'current verdict cannot clear activation blockers');
  if (!nonempty0(policy.currentVerdict.reason)) return reject0('NoProseOnlyTheoremPolicy.CurrentVerdictReason', ['currentVerdict', 'reason'], 'current verdict reason must be non-empty');

  const nonClaimsCheck = validateStringArray0(policy.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;

  if (!plain0(policy.audit)) return reject0('NoProseOnlyTheoremPolicy.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = { checker: CHECKER, script: 'pcc-no-prose-only-theorem-policy0.mjs', test: 'audits/no-prose-only-theorem-policy0.test.mjs', expectedAcceptTag: 'accept' };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (policy.audit[key] !== expected) return reject0('NoProseOnlyTheoremPolicy.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: policy.audit[key] });
  }
  return { tag: 'accept' };
}

function validateBindings0(bindings, policy) {
  if (!plain0(bindings) || bindings.kind !== 'PNPReportTheoremBindings0') return reject0('NoProseOnlyTheoremPolicy.BindingsKind', [BINDINGS_PATH], 'theorem bindings ledger kind mismatch');
  if (bindings.coordinate !== policy.coverageScope.theoremBindingLedgerCoordinate) return reject0('NoProseOnlyTheoremPolicy.BindingsCoordinate', ['theoremBindingLedgerCoordinate'], 'theorem binding coordinate mismatch');
  if (!Array.isArray(bindings.theoremBindings)) return reject0('NoProseOnlyTheoremPolicy.BindingsShape', ['theoremBindings'], 'theoremBindings must be an array');
  if (bindings.theoremBindings.length !== policy.coverageScope.expectedTheoremBindingCount) return reject0('NoProseOnlyTheoremPolicy.BindingsCount', ['theoremBindings'], 'theorem binding count mismatch', { expected: policy.coverageScope.expectedTheoremBindingCount, actual: bindings.theoremBindings.length });
  if (!String(bindings.coverageScope).includes('release-critical theorem spine')) return reject0('NoProseOnlyTheoremPolicy.BindingsCoverageScope', ['coverageScope'], 'theorem binding ledger must state release-critical scope');
  if (!String(bindings.coverageScope).includes('future')) return reject0('NoProseOnlyTheoremPolicy.BindingsFutureScope', ['coverageScope'], 'theorem binding ledger must preserve future exhaustive expansion note');

  const groupMap = bindings.bindingGroups ?? {};
  for (let index = 0; index < bindings.theoremBindings.length; index += 1) {
    const entry = bindings.theoremBindings[index];
    const entryPath = ['theoremBindings', index];
    if (!plain0(entry) || !nonempty0(entry.id) || !nonempty0(entry.theoremNumber) || !nonempty0(entry.reportTheoremName)) return reject0('NoProseOnlyTheoremPolicy.BindingEntryShape', entryPath, 'theorem binding entry must have id, theoremNumber, and name');
    if (!Array.isArray(entry.bindingGroupIds) || entry.bindingGroupIds.length === 0) return reject0('NoProseOnlyTheoremPolicy.BindingGroupsMissing', [...entryPath, 'bindingGroupIds'], 'theorem binding must cite at least one binding group');
    if (entry.claimEffect !== 'audit-ledger-only') return reject0('NoProseOnlyTheoremPolicy.BindingClaimEffect', [...entryPath, 'claimEffect'], 'binding entries must be audit-ledger-only');
    if (entry.publicEmissionEffect !== 'none') return reject0('NoProseOnlyTheoremPolicy.BindingPublicEmissionEffect', [...entryPath, 'publicEmissionEffect'], 'binding entries cannot have public emission effect');
    if (entry.dischargesPublicTheorem !== false) return reject0('NoProseOnlyTheoremPolicy.BindingDischargesPublicTheorem', [...entryPath, 'dischargesPublicTheorem'], 'binding entries cannot discharge public theorem');
    for (const groupId of entry.bindingGroupIds) {
      const group = groupMap[groupId];
      if (!plain0(group)) return reject0('NoProseOnlyTheoremPolicy.BindingGroupMissing', [...entryPath, 'bindingGroupIds'], 'binding group missing', { groupId });
      for (const field of ['checkerFiles', 'proofArtifacts', 'tests']) {
        if (!Array.isArray(group[field]) || group[field].length === 0) return reject0('NoProseOnlyTheoremPolicy.BindingGroupIncomplete', ['bindingGroups', groupId, field], 'binding group must declare checker files, proof artifacts, and tests');
      }
    }
  }
  return { tag: 'accept' };
}

function validateObligations0(obligations, policy) {
  if (!plain0(obligations) || obligations.kind !== 'PNPProofObligationLedger0') return reject0('NoProseOnlyTheoremPolicy.ObligationsKind', [OBLIGATIONS_PATH], 'proof obligation ledger kind mismatch');
  if (obligations.coordinate !== policy.coverageScope.proofObligationLedgerCoordinate) return reject0('NoProseOnlyTheoremPolicy.ObligationsCoordinate', ['proofObligationLedgerCoordinate'], 'proof obligation coordinate mismatch');
  if (!Array.isArray(obligations.obligations) || obligations.obligations.length < policy.coverageScope.minimumProofObligationCount) return reject0('NoProseOnlyTheoremPolicy.ObligationCount', ['obligations'], 'insufficient proof obligations');
  const ids = new Set(obligations.obligations.map((entry) => entry.id));
  for (const required of ['OBL-004-TheoremToCheckerBindings', 'OBL-014-UnrestrictedFinalSoundnessBlocked', 'OBL-015-FiniteToUnboundedFamilyAudit']) {
    if (!ids.has(required)) return reject0('NoProseOnlyTheoremPolicy.ObligationMissing', ['obligations'], 'required proof obligation missing', { required });
  }
  if (obligations.publicTheoremEmissionAllowedByLedger !== false || obligations.fullProofObligationDischargeProved !== false) return reject0('NoProseOnlyTheoremPolicy.ObligationsOverclaim', [OBLIGATIONS_PATH], 'proof obligation ledger cannot overclaim discharge or public emission');
  return { tag: 'accept' };
}

function validateGaps0(gaps) {
  if (!plain0(gaps) || gaps.kind !== 'PNPGapLedger0') return reject0('NoProseOnlyTheoremPolicy.GapsKind', [GAPS_PATH], 'gap ledger kind mismatch');
  if (gaps.coordinate !== 'PNP-GAP-LEDGER-2026-06-27-01') return reject0('NoProseOnlyTheoremPolicy.GapsCoordinate', ['gapLedgerCoordinate'], 'gap ledger coordinate mismatch');
  if (!Array.isArray(gaps.gaps) || gaps.gaps.length < 12) return reject0('NoProseOnlyTheoremPolicy.GapCount', ['gaps'], 'insufficient gap entries');
  const byId = new Map(gaps.gaps.map((gap) => [gap.id, gap]));
  const gap001 = byId.get('GAP-001-UnrestrictedFinalSoundness');
  const gap004 = byId.get('GAP-004-FiniteToUnboundedUniformity');
  if (!plain0(gap001) || gap001.blocker !== 'Release.UnrestrictedFinalSoundness') return reject0('NoProseOnlyTheoremPolicy.Gap001Blocker', ['gaps', 'GAP-001-UnrestrictedFinalSoundness'], 'GAP-001 must keep unrestricted final soundness blocker');
  if (!plain0(gap004) || gap004.ownerSurface !== 'finite-to-unbounded-family-audit' || gap004.status !== 'represented-not-discharged' || gap004.blocker !== 'Release.UnrestrictedFinalSoundness') return reject0('NoProseOnlyTheoremPolicy.Gap004State', ['gaps', 'GAP-004-FiniteToUnboundedUniformity'], 'GAP-004 must stay represented-not-discharged and release-blocking');
  if (gaps.gapLedgerClaimsNoRemainingGaps !== false || gaps.fullGapClosureProved !== false || gaps.publicTheoremEmissionAllowedByLedger !== false) return reject0('NoProseOnlyTheoremPolicy.GapOverclaim', [GAPS_PATH], 'gap ledger cannot overclaim closure or public emission');
  return { tag: 'accept' };
}

function validateStatus0(status) {
  if (!plain0(status) || status.kind !== 'PNPStatus0') return reject0('NoProseOnlyTheoremPolicy.StatusKind', [STATUS_PATH], 'PNP_STATUS kind mismatch');
  if (status.publicTheoremEmissionAllowed !== false || status.finalTheoremReady !== false) return reject0('NoProseOnlyTheoremPolicy.StatusActivation', [STATUS_PATH], 'status cannot activate theorem under policy');
  if (!sameArray0(status.activeFinalNodeIds, [])) return reject0('NoProseOnlyTheoremPolicy.StatusActiveNodes', ['activeFinalNodeIds'], 'active final nodes must be empty');
  if (!sameArray0(status.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('NoProseOnlyTheoremPolicy.StatusBlockers', ['remainingBlockers'], 'remaining blockers must remain exact');
  if (status.noProseOnlyTheoremPolicyCoordinate !== EXPECTED_COORDINATE) return reject0('NoProseOnlyTheoremPolicy.StatusCoordinate', ['noProseOnlyTheoremPolicyCoordinate'], 'status must bind no-prose-only theorem policy coordinate');
  return { tag: 'accept' };
}

function validateBoundary0(boundary, pathArray) {
  if (!plain0(boundary)) return reject0('NoProseOnlyTheoremPolicy.BoundaryShape', pathArray, 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('NoProseOnlyTheoremPolicy.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('NoProseOnlyTheoremPolicy.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('NoProseOnlyTheoremPolicy.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('NoProseOnlyTheoremPolicy.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const relativePath of paths) {
    const file = await digestFile0(root, relativePath, ['requiredEvidenceFiles']);
    if (file.tag === 'reject') return file;
    evidence.push(file);
  }
  return { tag: 'accept', evidence };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('NoProseOnlyTheoremPolicy.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('NoProseOnlyTheoremPolicy.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('NoProseOnlyTheoremPolicy.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('NoProseOnlyTheoremPolicy.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('NoProseOnlyTheoremPolicy.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('NoProseOnlyTheoremPolicy.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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

function reject0(coord, pathArray, reason, witness = {}) {
  return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS] };
}

async function writeAndReturn0(root, outputPath, writeOutput, verdict) {
  if (writeOutput) {
    const absoluteOutputPath = path.join(root, outputPath);
    await mkdir(path.dirname(absoluteOutputPath), { recursive: true });
    await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
  }
  return { ...verdict, outputPath: writeOutput ? outputPath : null };
}

function stableStringify0(value) {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map((entry) => stableStringify0(entry)).join(',')}]`;
  return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
}

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
    else if (arg === '--policy') options.policyPath = requireValue0(argv, ++index, '--policy');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node pcc-no-prose-only-theorem-policy0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/no-prose-only-theorem-policy/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --policy <path>    Policy path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad no-prose-only theorem policy CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckNoProseOnlyTheoremPolicy0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
