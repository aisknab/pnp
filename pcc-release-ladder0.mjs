#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckReleaseLadder0';
const VERSION = 0;
const LADDER_PATH = 'release/RELEASE_LADDER.json';
const STATUS_PATH = 'PNP_STATUS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/release-ladder/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-RELEASE-LADDER-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_LADDER_IDS = [
  'HistoricalSealedReportExists',
  'PublicReviewBoundaryDeclared',
  'SuccessorReportSealExists',
  'TrustBaseExplicitReady',
  'TrustBaseShrinkPlanReady',
  'OneCommandVerifierReady',
  'MinimalKernelCoordinateReady',
  'MathematicalSemanticsSeedReady',
  'SourceSurfaceHardeningReady',
  'ReproducibilitySeedReady',
  'ReleaseLadderReady',
  'UnrestrictedFinalSoundnessRepresented',
  'InternalTheoremActivationCandidate',
  'PublicTheoremEmissionCandidate',
];
const BLOCKED_IDS = [
  'UnrestrictedFinalSoundnessRepresented',
  'InternalTheoremActivationCandidate',
  'PublicTheoremEmissionCandidate',
];
const EXPECTED_LINKED_COORDINATES = {
  status: 'PNPStatus0',
  successorReportSeal: 'PNP-REPORT-SEAL-2026-06-27-01',
  trustBase: 'PNP-TRUST-BASE-2026-06-27-01',
  trustBaseShrinkPlan: 'PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01',
  minimalKernel: 'PNP-MINIMAL-KERNEL-2026-06-27-01',
  nandSemantics: 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01',
  lockedNANDSATSmallModels: 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01',
  complexityLedger: 'PNP-COMPLEXITY-LEDGER-2026-06-27-01',
  determinismAudit: 'PNP-DETERMINISM-AUDIT-2026-06-27-01',
  regenerationLedger: 'PNP-REGENERATION-LEDGER-2026-06-27-01',
};

export async function CheckReleaseLadder0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const ladderPath = options.ladderPath ?? LADDER_PATH;
  const statusPath = options.statusPath ?? STATUS_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const ladderRead = await readJson0({ root, filePath: ladderPath, override: options.ladderOverride, label: 'ladder' });
    if (ladderRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, ladderRead);

    const ladderValidation = validateLadder0(ladderRead.value);
    if (ladderValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, ladderValidation);

    const statusRead = await readJson0({ root, filePath: statusPath, override: options.statusOverride, label: 'status' });
    if (statusRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusRead);

    const statusValidation = validateStatus0(statusRead.value);
    if (statusValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, statusValidation);

    const completedCount = ladderRead.value.ladder.filter((entry) => entry.state === 'complete').length;
    const blockedCount = ladderRead.value.ladder.filter((entry) => entry.state === 'blocked').length;

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'release-ladder-accepted-under-public-review-boundary',
      ladderPath,
      statusPath,
      ladderSha256: sha256Hex0(ladderRead.bytes),
      statusSha256: sha256Hex0(statusRead.bytes),
      releaseLadderReady: true,
      publicTheoremEmissionAllowedByLadder: false,
      finalTheoremReadyByLadder: false,
      activeFinalNodeIdsByLadder: [],
      ladderEntryCount: ladderRead.value.ladder.length,
      completedEntryCount: completedCount,
      blockedEntryCount: blockedCount,
      blockedEntryIds: BLOCKED_IDS,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('ReleaseLadder.UnhandledException', [], 'release ladder checker threw unexpectedly', normalizeError0(error)));
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
    return reject0('ReleaseLadder.ReadOrParseFailed', [filePath], `could not read or parse ${label} JSON`, normalizeError0(error));
  }
}

function validateLadder0(ladder) {
  if (!plain0(ladder)) return reject0('ReleaseLadder.Shape', [], 'release ladder must be an object');
  if (ladder.kind !== 'PNPReleaseLadder0') return reject0('ReleaseLadder.Kind', ['kind'], 'release ladder kind mismatch');
  if (ladder.version !== VERSION) return reject0('ReleaseLadder.Version', ['version'], 'release ladder version mismatch');
  if (ladder.coordinate !== EXPECTED_COORDINATE) return reject0('ReleaseLadder.Coordinate', ['coordinate'], 'release ladder coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: ladder.coordinate });
  if (ladder.status !== 'release-ladder-ready') return reject0('ReleaseLadder.Status', ['status'], 'release ladder status mismatch');
  if (ladder.releaseLadderReady !== true) return reject0('ReleaseLadder.ReadyFlag', ['releaseLadderReady'], 'releaseLadderReady must be true');
  if (ladder.publicTheoremEmissionAllowedByLadder !== false) return reject0('ReleaseLadder.PublicEmissionByLadder', ['publicTheoremEmissionAllowedByLadder'], 'ladder must not allow public theorem emission');
  if (ladder.finalTheoremReadyByLadder !== false) return reject0('ReleaseLadder.FinalReadyByLadder', ['finalTheoremReadyByLadder'], 'ladder must not mark final theorem ready');
  if (!sameArray0(ladder.activeFinalNodeIdsByLadder, [])) return reject0('ReleaseLadder.ActiveFinalNodesByLadder', ['activeFinalNodeIdsByLadder'], 'ladder active final nodes must be empty');

  const boundary = validateBoundary0(ladder.claimBoundary, ['claimBoundary']);
  if (boundary.tag === 'reject') return boundary;

  const linked = validateLinkedCoordinates0(ladder.linkedCoordinates);
  if (linked.tag === 'reject') return linked;

  if (!plain0(ladder.currentStatus)) return reject0('ReleaseLadder.CurrentStatusShape', ['currentStatus'], 'currentStatus must be an object');
  for (const [key, expected] of Object.entries({
    historicalSealedProofReportExists: true,
    publicReviewDocumentationCoordinateExists: true,
    successorReportSealExists: true,
    publicTheoremEmissionDisabled: true,
    internalProofStackAcceptedUnderCheckerTrustModel: true,
  })) {
    if (ladder.currentStatus[key] !== expected) return reject0('ReleaseLadder.CurrentStatusField', ['currentStatus', key], 'current status field mismatch', { expected, actual: ladder.currentStatus[key] });
  }

  if (!Array.isArray(ladder.ladder)) return reject0('ReleaseLadder.LadderShape', ['ladder'], 'ladder must be an array');
  const ids = ladder.ladder.map((entry) => entry?.id);
  if (!sameArray0(ids, EXPECTED_LADDER_IDS)) return reject0('ReleaseLadder.LadderIds', ['ladder'], 'ladder ids must stay exact and ordered', { expected: EXPECTED_LADDER_IDS, actual: ids });
  const seen = new Set();
  for (let index = 0; index < ladder.ladder.length; index += 1) {
    const entry = ladder.ladder[index];
    const entryPath = ['ladder', index];
    const check = validateEntry0(entry, entryPath, seen, index);
    if (check.tag === 'reject') return check;
    seen.add(entry.id);
  }

  const completedBlocked = ladder.ladder.filter((entry) => BLOCKED_IDS.includes(entry.id) && entry.state === 'complete');
  if (completedBlocked.length !== 0) return reject0('ReleaseLadder.BlockedEntryComplete', ['ladder'], 'blocked ladder entries cannot be complete in current boundary', { completedBlocked });

  const transitionRules = validateStringArray0(ladder.transitionRules, ['transitionRules'], true);
  if (transitionRules.tag === 'reject') return transitionRules;
  const nonClaims = validateStringArray0(ladder.nonClaims, ['nonClaims'], true);
  if (nonClaims.tag === 'reject') return nonClaims;

  if (!plain0(ladder.audit)) return reject0('ReleaseLadder.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-release-ladder0.mjs',
    test: 'audits/release-ladder0.test.mjs',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (ladder.audit[key] !== expected) return reject0('ReleaseLadder.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: ladder.audit[key] });
  }

  return { tag: 'accept' };
}

function validateEntry0(entry, entryPath, seen, index) {
  if (!plain0(entry)) return reject0('ReleaseLadder.EntryShape', entryPath, 'ladder entry must be an object');
  if (!nonempty0(entry.id) || !nonempty0(entry.state) || !nonempty0(entry.activationEffect)) return reject0('ReleaseLadder.EntryFields', entryPath, 'ladder entry id, state, and activationEffect must be non-empty strings');
  if (!['complete', 'blocked'].includes(entry.state)) return reject0('ReleaseLadder.EntryState', [...entryPath, 'state'], 'ladder state must be complete or blocked', { actual: entry.state });
  const depCheck = validateStringArray0(entry.dependencies, [...entryPath, 'dependencies'], false);
  if (depCheck.tag === 'reject') return depCheck;
  for (const dependency of entry.dependencies) {
    if (!seen.has(dependency)) return reject0('ReleaseLadder.ForwardDependency', [...entryPath, 'dependencies'], 'ladder dependencies must point to earlier entries', { dependency, index });
  }
  const shouldBeBlocked = BLOCKED_IDS.includes(entry.id);
  if (shouldBeBlocked && entry.state !== 'blocked') return reject0('ReleaseLadder.BlockedState', [...entryPath, 'state'], 'blocked-status entry must be blocked', { id: entry.id });
  if (!shouldBeBlocked && entry.state !== 'complete') return reject0('ReleaseLadder.CompleteState', [...entryPath, 'state'], 'completed infrastructure entry must be complete', { id: entry.id });
  if (shouldBeBlocked && !EXPECTED_BLOCKERS.includes(entry.blocker)) return reject0('ReleaseLadder.BlockerField', [...entryPath, 'blocker'], 'blocked entry must name an active blocker', { actual: entry.blocker });
  return { tag: 'accept' };
}

function validateStatus0(status) {
  if (!plain0(status)) return reject0('ReleaseLadder.StatusShape', [STATUS_PATH], 'PNP_STATUS.json must be an object');
  const failures = [];
  requireEqual0(status.kind, 'PNPStatus0', failures, ['kind']);
  requireEqual0(status.publicTheoremEmissionAllowed, false, failures, ['publicTheoremEmissionAllowed']);
  requireEqual0(status.finalTheoremReady, false, failures, ['finalTheoremReady']);
  requireArrayEqual0(status.activeFinalNodeIds, [], failures, ['activeFinalNodeIds']);
  requireArrayEqual0(status.remainingBlockers, EXPECTED_BLOCKERS, failures, ['remainingBlockers']);
  requireEqual0(status.releaseLadderCoordinate, EXPECTED_COORDINATE, failures, ['releaseLadderCoordinate']);
  if (failures.length !== 0) return reject0('ReleaseLadder.StatusMismatch', [STATUS_PATH], 'PNP_STATUS.json does not match release ladder boundary', { failures });
  return { tag: 'accept' };
}

function validateBoundary0(boundary, pathArray) {
  if (!plain0(boundary)) return reject0('ReleaseLadder.BoundaryShape', pathArray, 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ReleaseLadder.PublicEmission', [...pathArray, 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ReleaseLadder.FinalReady', [...pathArray, 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('ReleaseLadder.ActiveFinalNodes', [...pathArray, 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ReleaseLadder.RemainingBlockers', [...pathArray, 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

function validateLinkedCoordinates0(linked) {
  if (!plain0(linked)) return reject0('ReleaseLadder.LinkedCoordinatesShape', ['linkedCoordinates'], 'linkedCoordinates must be an object');
  for (const [key, expected] of Object.entries(EXPECTED_LINKED_COORDINATES)) {
    if (linked[key] !== expected) return reject0('ReleaseLadder.LinkedCoordinate', ['linkedCoordinates', key], 'linked coordinate mismatch', { expected, actual: linked[key] });
  }
  return { tag: 'accept' };
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('ReleaseLadder.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('ReleaseLadder.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!nonempty0(value[index])) return reject0('ReleaseLadder.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
  }
  return { tag: 'accept' };
}

function requireEqual0(actual, expected, failures, pathArray) { if (actual !== expected) failures.push({ path: pathArray, expected, actual }); }
function requireArrayEqual0(actual, expected, failures, pathArray) { if (!Array.isArray(actual) || actual.length !== expected.length || actual.some((value, index) => value !== expected[index])) failures.push({ path: pathArray, expected, actual }); }

function reject0(coord, pathArray, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER,
    version: VERSION,
    coord,
    path: pathArray,
    witness: { reason, ...witness },
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    remainingBlockers: [...EXPECTED_BLOCKERS],
  };
}

async function writeAndReturn0(root, outputPath, writeOutput, verdict) {
  if (writeOutput) {
    const absoluteOutputPath = path.join(root, outputPath);
    await mkdir(path.dirname(absoluteOutputPath), { recursive: true });
    await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
  }
  return { ...verdict, outputPath: writeOutput ? outputPath : null };
}

function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), ladderPath: LADDER_PATH, statusPath: STATUS_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--ladder') options.ladderPath = requireValue0(argv, ++index, '--ladder');
    else if (arg === '--status') options.statusPath = requireValue0(argv, ++index, '--status');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

function requireValue0(argv, index, flag) {
  if (index >= argv.length) throw new Error(`${flag} requires a value`);
  return argv[index];
}

function printHelp0() {
  console.log(`Usage: node pcc-release-ladder0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/release-ladder/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --ladder <path>    Release ladder JSON path relative to root.\n  --status <path>    PNP status JSON path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad release ladder CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckReleaseLadder0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
