#!/usr/bin/env node

import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import path from 'node:path';
import process from 'node:process';

import { TRUST_BASE_REQUIRED_ASSUMPTION_IDS0 } from './pcc-trust-base0.mjs';

const CHECKER = 'CheckTrustBaseShrinkPlan0';
const VERSION = 0;
const PLAN_PATH = 'trust-base/SHRINK_PLAN.json';
const TRUST_BASE_PATH = 'trust-base/TRUST_BASE.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/trust-base/shrink-plan/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01';
const EXPECTED_TRUST_BASE_COORDINATE = 'PNP-TRUST-BASE-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_TASK_IDS = ['TB-001', 'TB-002', 'TB-003', 'TB-004', 'TB-005', 'TB-006', 'TB-007'];
const VALID_STATUSES = new Set(['planned', 'represented', 'complete']);

export async function CheckTrustBaseShrinkPlan0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const planPath = options.planPath ?? PLAN_PATH;
  const trustBasePath = options.trustBasePath ?? TRUST_BASE_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const planRead = await readJson0({ root, relativePath: planPath, override: options.planOverride });
    if (planRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, planRead);

    const trustBaseRead = await readJson0({ root, relativePath: trustBasePath, override: options.trustBaseOverride });
    if (trustBaseRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, trustBaseRead);

    const planValidation = validatePlan0(planRead.value, trustBaseRead.value);
    if (planValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, planValidation);

    const represented = await validateRepresentedFiles0({ root, plan: planRead.value });
    if (represented.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, represented);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      trustBaseCoordinate: EXPECTED_TRUST_BASE_COORDINATE,
      claimStatus: 'trust-base-shrink-plan-represented-ready',
      planPath,
      planSha256: sha256Hex0(planRead.bytes),
      trustBasePath,
      trustBaseSha256: sha256Hex0(trustBaseRead.bytes),
      shrinkPlanReady: true,
      shrinksTrustBaseNow: false,
      taskCount: planRead.value.tasks.length,
      taskIds: EXPECTED_TASK_IDS,
      targetedAssumptionCount: TRUST_BASE_REQUIRED_ASSUMPTION_IDS0.length,
      targetedAssumptionIds: TRUST_BASE_REQUIRED_ASSUMPTION_IDS0,
      representedFileCount: represented.representedFileCount,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('TrustBaseShrinkPlan.UnhandledException', [], 'shrink-plan checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readJson0({ root, relativePath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, relativePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('Json.ReadOrParseFailed', [relativePath], 'could not read or parse required JSON file', normalizeError0(error));
  }
}

function validatePlan0(plan, trustBase) {
  if (!isPlainObject0(plan)) return reject0('ShrinkPlan.Shape', [], 'shrink plan must be an object');
  if (plan.kind !== 'PNPTrustBaseShrinkPlan0') return reject0('ShrinkPlan.Kind', ['kind'], 'shrink plan kind mismatch');
  if (plan.version !== VERSION) return reject0('ShrinkPlan.Version', ['version'], 'shrink plan version mismatch');
  if (plan.coordinate !== EXPECTED_COORDINATE) return reject0('ShrinkPlan.Coordinate', ['coordinate'], 'shrink plan coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: plan.coordinate });
  if (plan.trustBaseCoordinate !== EXPECTED_TRUST_BASE_COORDINATE) return reject0('ShrinkPlan.TrustBaseCoordinate', ['trustBaseCoordinate'], 'linked trust-base coordinate mismatch');
  if (plan.status !== 'trust-base-shrink-plan-ready') return reject0('ShrinkPlan.Status', ['status'], 'shrink plan status mismatch');
  if (plan.shrinkPlanReady !== true) return reject0('ShrinkPlan.Flag', ['shrinkPlanReady'], 'shrinkPlanReady must be true');
  if (plan.shrinksTrustBaseNow !== false) return reject0('ShrinkPlan.Flag', ['shrinksTrustBaseNow'], 'shrinksTrustBaseNow must remain false until a task is actually completed');

  const boundary = validateBoundary0(plan.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  const trust = validateTrustBaseLink0(trustBase);
  if (trust.tag === 'reject') return trust;

  if (!Array.isArray(plan.tasks)) return reject0('ShrinkPlan.TasksShape', ['tasks'], 'tasks must be an array');
  const ids = plan.tasks.map((task) => task?.id);
  if (!sameStringArray0(ids, EXPECTED_TASK_IDS)) return reject0('ShrinkPlan.TaskIds', ['tasks'], 'task ids must stay exact and ordered', { expected: EXPECTED_TASK_IDS, actual: ids });

  const seenPriorities = new Set();
  const allTargetedAssumptions = new Set();
  for (let index = 0; index < plan.tasks.length; index += 1) {
    const task = plan.tasks[index];
    const taskPath = ['tasks', index];
    const taskValidation = validateTask0(task, taskPath, ids, seenPriorities, allTargetedAssumptions);
    if (taskValidation.tag === 'reject') return taskValidation;
  }

  for (const assumptionId of TRUST_BASE_REQUIRED_ASSUMPTION_IDS0) {
    if (!allTargetedAssumptions.has(assumptionId)) {
      return reject0('ShrinkPlan.AssumptionUntargeted', ['tasks'], 'every trust-base assumption must be targeted by at least one shrink task', { assumptionId });
    }
  }

  if (!isPlainObject0(plan.audit)) return reject0('ShrinkPlan.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-trust-base-shrink-plan0.mjs',
    command: 'node pcc-trust-base-shrink-plan0.mjs --json',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (plan.audit[key] !== expected) return reject0('ShrinkPlan.AuditField', ['audit', key], 'shrink plan audit field mismatch', { expected, actual: plan.audit[key] });
  }

  return { tag: 'accept' };
}

function validateTrustBaseLink0(trustBase) {
  if (!isPlainObject0(trustBase)) return reject0('ShrinkPlan.TrustBaseShape', ['trust-base'], 'trust base must be an object');
  if (trustBase.kind !== 'PNPTrustBase0') return reject0('ShrinkPlan.TrustBaseKind', ['trust-base', 'kind'], 'linked trust base kind mismatch');
  if (trustBase.coordinate !== EXPECTED_TRUST_BASE_COORDINATE) return reject0('ShrinkPlan.TrustBaseCoordinateMismatch', ['trust-base', 'coordinate'], 'linked trust base coordinate mismatch');
  if (!Array.isArray(trustBase.assumptions)) return reject0('ShrinkPlan.TrustBaseAssumptions', ['trust-base', 'assumptions'], 'linked trust base must contain assumptions');
  const ids = trustBase.assumptions.map((entry) => entry?.id);
  if (!sameStringArray0(ids, TRUST_BASE_REQUIRED_ASSUMPTION_IDS0)) return reject0('ShrinkPlan.TrustBaseAssumptionIds', ['trust-base', 'assumptions'], 'linked trust-base assumption ids mismatch', { expected: TRUST_BASE_REQUIRED_ASSUMPTION_IDS0, actual: ids });
  return { tag: 'accept' };
}

function validateTask0(task, taskPath, allTaskIds, seenPriorities, allTargetedAssumptions) {
  if (!isPlainObject0(task)) return reject0('ShrinkPlan.TaskShape', taskPath, 'task must be an object');
  for (const field of ['id', 'title', 'status']) {
    if (!isNonEmptyString0(task[field])) return reject0('ShrinkPlan.TaskField', [...taskPath, field], 'task field must be a non-empty string');
  }
  if (!VALID_STATUSES.has(task.status)) return reject0('ShrinkPlan.TaskStatus', [...taskPath, 'status'], 'task status must be planned, represented, or complete', { status: task.status });
  if (task.status !== 'planned') return reject0('ShrinkPlan.TaskPrematureCompletion', [...taskPath, 'status'], 'initial shrink plan cannot mark tasks represented or complete');
  if (!Number.isInteger(task.priority) || task.priority < 1) return reject0('ShrinkPlan.TaskPriority', [...taskPath, 'priority'], 'task priority must be a positive integer');
  if (seenPriorities.has(task.priority)) return reject0('ShrinkPlan.TaskPriorityDuplicate', [...taskPath, 'priority'], 'task priorities must be unique', { priority: task.priority });
  seenPriorities.add(task.priority);

  for (const field of ['targetsAssumptions', 'deliverables', 'acceptanceCriteria', 'blockedBy']) {
    const arr = validateStringArray0(task[field], [...taskPath, field], field !== 'blockedBy');
    if (arr.tag === 'reject') return arr;
  }

  for (const assumptionId of task.targetsAssumptions) {
    if (!TRUST_BASE_REQUIRED_ASSUMPTION_IDS0.includes(assumptionId)) {
      return reject0('ShrinkPlan.TaskUnknownAssumption', [...taskPath, 'targetsAssumptions'], 'task targets an unknown trust-base assumption', { assumptionId });
    }
    allTargetedAssumptions.add(assumptionId);
  }

  for (const blockedBy of task.blockedBy) {
    if (!allTaskIds.includes(blockedBy)) return reject0('ShrinkPlan.TaskUnknownDependency', [...taskPath, 'blockedBy'], 'task depends on unknown task id', { blockedBy });
    if (blockedBy === task.id) return reject0('ShrinkPlan.TaskSelfDependency', [...taskPath, 'blockedBy'], 'task cannot depend on itself');
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!isPlainObject0(boundary)) return reject0('ShrinkPlan.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ShrinkPlan.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ShrinkPlan.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameStringArray0(boundary.activeFinalNodeIds, [])) return reject0('ShrinkPlan.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameStringArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ShrinkPlan.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function validateRepresentedFiles0({ root, plan }) {
  const paths = [PLAN_PATH, TRUST_BASE_PATH, 'TRUST_BASE.md', 'trust-base/SHRINK_PLAN.md'];
  for (const relativePath of paths) {
    const absolutePath = safeJoin0(root, relativePath);
    if (absolutePath === null) return reject0('ShrinkPlan.PathUnsafe', [relativePath], 'represented shrink-plan path must stay inside repository root');
    try {
      const info = await stat(absolutePath);
      if (!info.isFile()) return reject0('ShrinkPlan.PathNotFile', [relativePath], 'represented shrink-plan path must be a file');
    } catch (error) {
      return reject0('ShrinkPlan.PathMissing', [relativePath], 'represented shrink-plan file is missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', representedFileCount: paths.length };
}

function validateStringArray0(value, pathArray, nonEmpty = false) {
  if (!Array.isArray(value)) return reject0('ShrinkPlan.StringArray', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('ShrinkPlan.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!isNonEmptyString0(value[index])) return reject0('ShrinkPlan.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
  }
  return { tag: 'accept' };
}

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

function sameStringArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function safeJoin0(root, relativePath) {
  if (!isNonEmptyString0(relativePath) || path.isAbsolute(relativePath)) return null;
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
}

function sha256Hex0(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function isNonEmptyString0(value) {
  return typeof value === 'string' && value.length > 0;
}

function parseArgs0(argv) {
  const options = { root: process.cwd(), planPath: PLAN_PATH, trustBasePath: TRUST_BASE_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') {
      index += 1;
      if (index >= argv.length) throw new Error('--root requires a value');
      options.root = argv[index];
    } else if (arg === '--plan') {
      index += 1;
      if (index >= argv.length) throw new Error('--plan requires a value');
      options.planPath = argv[index];
    } else if (arg === '--trust-base') {
      index += 1;
      if (index >= argv.length) throw new Error('--trust-base requires a value');
      options.trustBasePath = argv[index];
    } else if (arg === '--output') {
      index += 1;
      if (index >= argv.length) throw new Error('--output requires a value');
      options.outputPath = argv[index];
    } else if (arg === '--help' || arg === '-h') {
      printHelp0();
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }
  return options;
}

function printHelp0() {
  console.log(`Usage: node pcc-trust-base-shrink-plan0.mjs [options]\n\nOptions:\n  --json                  Emit verdict JSON.\n  --no-write              Do not write artifacts/trust-base/shrink-plan/latest-verdict.json.\n  --root <path>           Repository root. Defaults to cwd.\n  --plan <path>           Shrink-plan JSON path relative to root.\n  --trust-base <path>     Trust-base JSON path relative to root.\n  --output <path>         Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad trust-base shrink-plan CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await CheckTrustBaseShrinkPlan0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0();
}
