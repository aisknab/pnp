#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'pnp-verify-all0';
const VERSION = 0;
const DEFAULT_OUTPUT_PATH = 'artifacts/pnp-verify-all/latest-verdict.json';
const PNP_STATUS_PATH = 'PNP_STATUS.json';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export async function RunPNPVerifyAll0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  const includeUnitTests = options.includeUnitTests ?? true;
  const includeReleaseAudit = options.includeReleaseAudit ?? true;

  const steps = [];
  const statusStep = await verifyStatusFile0(root);
  steps.push(statusStep);
  if (statusStep.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, makeReject0('StatusFile.Reject', ['PNP_STATUS.json'], 'PNP_STATUS.json failed consistency checks', { statusStep }, steps));

  const nodeSyntaxTargets = [
    'pcc-core.mjs',
    'pcc-trust-base0.mjs',
    'pcc-trust-base-shrink-plan0.mjs',
    'pcc-rule-family-coverage0.mjs',
    'pcc-nand-direct-wire-semantics0.mjs',
    'pcc-nand-small-models0.mjs',
    'pcc-locked-nand-sat-small-models0.mjs',
    'pcc-complexity-ledger0.mjs',
    'semantics/nand-direct-wire-reference.mjs',
    'semantics/nand-small-models.mjs',
    'semantics/locked-nand-sat-small-models.mjs',
    'scripts/cross-verify.mjs',
    'scripts/audit-report-theorem-bindings.mjs',
    'scripts/audit-independent-verifiers-no-shared-code.mjs',
    'scripts/audit-checker-totality.mjs',
    'scripts/audit-negative-checker-mutations.mjs',
    'scripts/generate-checker-dependency-graph.mjs',
    'scripts/audit-checker-cycles.mjs',
    'scripts/audit-no-hidden-oracle.mjs',
    'scripts/pnp-verify-all.mjs',
  ];
  for (const target of nodeSyntaxTargets) {
    const step = await runStep0({ id: `node-syntax:${target}`, command: process.execPath, args: ['--check', target], root, kind: 'process' });
    steps.push(step);
    if (step.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(step, steps));
  }

  if (includeUnitTests) {
    const unitStep = await runStep0({ id: 'node-unit-tests', command: process.execPath, args: ['--test'], root, kind: 'process' });
    steps.push(unitStep);
    if (unitStep.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(unitStep, steps));
  }

  const releaseAuditSteps = includeReleaseAudit
    ? [{ id: 'release-audit', command: process.execPath, args: ['./bin/release-audit0.mjs'], kind: 'process' }]
    : [];

  const requiredSteps = [
    { id: 'theorem-binding-ledger-audit', command: process.execPath, args: ['scripts/audit-report-theorem-bindings.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'trust-base-audit', command: process.execPath, args: ['pcc-trust-base0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'trust-base-tests', command: process.execPath, args: ['--test', 'audits/trust-base0.test.mjs'], kind: 'process' },
    { id: 'trust-base-shrink-plan-audit', command: process.execPath, args: ['pcc-trust-base-shrink-plan0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'trust-base-shrink-plan-tests', command: process.execPath, args: ['--test', 'audits/trust-base-shrink-plan0.test.mjs'], kind: 'process' },
    { id: 'checker-totality-audit', command: process.execPath, args: ['scripts/audit-checker-totality.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'checker-totality-tests', command: process.execPath, args: ['--test', 'audits/checker-totality0.test.mjs'], kind: 'process' },
    { id: 'negative-checker-mutation-audit', command: process.execPath, args: ['scripts/audit-negative-checker-mutations.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'negative-checker-mutation-tests', command: process.execPath, args: ['--test', 'audits/negative-checker-mutations0.test.mjs'], kind: 'process' },
    { id: 'rule-family-coverage-audit', command: process.execPath, args: ['pcc-rule-family-coverage0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'rule-family-coverage-tests', command: process.execPath, args: ['--test', 'audits/rule-family-coverage0.test.mjs'], kind: 'process' },
    { id: 'checker-dependency-graph-generation', command: process.execPath, args: ['scripts/generate-checker-dependency-graph.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'checker-dependency-graph-tests', command: process.execPath, args: ['--test', 'audits/checker-dependency-graph0.test.mjs'], kind: 'process' },
    { id: 'checker-cycle-audit', command: process.execPath, args: ['scripts/audit-checker-cycles.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'checker-cycle-tests', command: process.execPath, args: ['--test', 'audits/checker-cycles0.test.mjs'], kind: 'process' },
    { id: 'nand-direct-wire-semantics-audit', command: process.execPath, args: ['pcc-nand-direct-wire-semantics0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'nand-direct-wire-semantics-tests', command: process.execPath, args: ['--test', 'audits/nand-direct-wire-semantics0.test.mjs'], kind: 'process' },
    { id: 'nand-small-model-audit', command: process.execPath, args: ['pcc-nand-small-models0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'nand-small-model-tests', command: process.execPath, args: ['--test', 'audits/nand-small-models0.test.mjs'], kind: 'process' },
    { id: 'locked-nand-sat-small-model-audit', command: process.execPath, args: ['pcc-locked-nand-sat-small-models0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'locked-nand-sat-small-model-tests', command: process.execPath, args: ['--test', 'audits/locked-nand-sat-small-models0.test.mjs'], kind: 'process' },
    { id: 'complexity-ledger-audit', command: process.execPath, args: ['pcc-complexity-ledger0.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'complexity-ledger-tests', command: process.execPath, args: ['--test', 'audits/complexity-ledger0.test.mjs'], kind: 'process' },
    { id: 'no-hidden-oracle-audit', command: process.execPath, args: ['scripts/audit-no-hidden-oracle.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'no-hidden-oracle-tests', command: process.execPath, args: ['--test', 'audits/no-hidden-oracle0.test.mjs'], kind: 'process' },
    { id: 'minimal-kernel-cross-verify', command: process.execPath, args: ['scripts/cross-verify.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'independent-no-shared-code-audit', command: process.execPath, args: ['scripts/audit-independent-verifiers-no-shared-code.mjs', '--json'], kind: 'json', expectTag: 'accept' },
    { id: 'independent-no-shared-code-tests', command: process.execPath, args: ['--test', 'audits/independent-verifiers-no-shared-code.test.mjs'], kind: 'process' },
    ...releaseAuditSteps,
  ];

  for (const spec of requiredSteps) {
    const step = await runStep0({ ...spec, root });
    steps.push(step);
    if (step.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(step, steps));
    if (spec.kind === 'json' && step.json?.tag !== spec.expectTag) {
      return writeAndReturn0(root, outputPath, writeOutput, makeReject0('JsonStep.UnexpectedTag', [spec.id], 'JSON verifier returned an unexpected tag', { expectedTag: spec.expectTag, actualTag: step.json?.tag ?? null, step }, steps));
    }
  }

  const pythonStep = await runPythonUnitTests0(root, options.python ?? process.env.PYTHON ?? null);
  steps.push(pythonStep);
  if (pythonStep.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(pythonStep, steps));

  const verdict = {
    tag: 'accept',
    kind: 'accept',
    checker: CHECKER,
    version: VERSION,
    claimStatus: 'internal-proof-certificate-stack-accepted-under-public-review-boundary',
    statusPath: PNP_STATUS_PATH,
    statusSha256: statusStep.statusSha256,
    trustBaseCoordinate: 'PNP-TRUST-BASE-2026-06-27-01',
    trustBaseShrinkPlanCoordinate: 'PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01',
    checkerTotalityAuditCoordinate: 'PNP-CHECKER-TOTALITY-AUDIT-2026-06-27-01',
    negativeCheckerMutationCoordinate: 'PNP-NEGATIVE-CHECKER-MUTATIONS-2026-06-27-01',
    ruleFamilyCoverageCoordinate: 'PNP-RULE-FAMILY-COVERAGE-2026-06-27-01',
    checkerDependencyGraphCoordinate: 'PNP-CHECKER-DEPENDENCY-GRAPH-2026-06-27-01',
    checkerAuthorityGraphCoordinate: 'PNP-CHECKER-AUTHORITY-GRAPH-2026-06-27-01',
    nandDirectWireSemanticsCoordinate: 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01',
    nandSmallModelsCoordinate: 'PNP-NAND-SMALL-MODELS-2026-06-27-01',
    lockedNANDSATSmallModelsCoordinate: 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01',
    complexityLedgerCoordinate: 'PNP-COMPLEXITY-LEDGER-2026-06-27-01',
    noHiddenOracleAuditCoordinate: 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01',
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    remainingBlockers: [...EXPECTED_BLOCKERS],
    oneCommand: 'npm run pnp:verify',
    stepCount: steps.length,
    acceptedStepCount: steps.filter((step) => step.tag === 'accept').length,
    steps,
    outputPath: writeOutput ? outputPath : null,
  };

  return writeAndReturn0(root, outputPath, writeOutput, verdict);
}

async function verifyStatusFile0(root) {
  const absolutePath = path.join(root, PNP_STATUS_PATH);
  let bytes;
  let status;
  try {
    bytes = await readFile(absolutePath);
    status = JSON.parse(bytes.toString('utf8'));
  } catch (error) {
    return { tag: 'reject', id: 'status-file-consistency', coord: 'StatusFile.ReadOrParseFailed', path: [PNP_STATUS_PATH], witness: normalizeError0(error) };
  }

  const failures = [];
  requireEqual0(status.project, 'PNP', failures, ['project']);
  requireEqual0(status.internalProofStackAccepted, true, failures, ['internalProofStackAccepted']);
  requireEqual0(status.publicTheoremEmissionAllowed, false, failures, ['publicTheoremEmissionAllowed']);
  requireEqual0(status.finalTheoremReady, false, failures, ['finalTheoremReady']);
  requireArrayEqual0(status.activeFinalNodeIds, [], failures, ['activeFinalNodeIds']);
  requireArrayEqual0(status.remainingBlockers, EXPECTED_BLOCKERS, failures, ['remainingBlockers']);
  requireEqual0(status.pnpVerifyCommand, 'npm run pnp:verify', failures, ['pnpVerifyCommand']);
  requireEqual0(status.minimalKernelCoordinate, 'PNP-MINIMAL-KERNEL-2026-06-27-01', failures, ['minimalKernelCoordinate']);
  requireEqual0(status.theoremBindingLedgerCoordinate, 'REPORT-THEOREM-BINDINGS-2026-06-27-01', failures, ['theoremBindingLedgerCoordinate']);
  requireEqual0(status.trustBaseCoordinate, 'PNP-TRUST-BASE-2026-06-27-01', failures, ['trustBaseCoordinate']);
  requireEqual0(status.trustBaseShrinkPlanCoordinate, 'PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01', failures, ['trustBaseShrinkPlanCoordinate']);
  requireEqual0(status.checkerTotalityAuditCoordinate, 'PNP-CHECKER-TOTALITY-AUDIT-2026-06-27-01', failures, ['checkerTotalityAuditCoordinate']);
  requireEqual0(status.negativeCheckerMutationCoordinate, 'PNP-NEGATIVE-CHECKER-MUTATIONS-2026-06-27-01', failures, ['negativeCheckerMutationCoordinate']);
  requireEqual0(status.ruleFamilyCoverageCoordinate, 'PNP-RULE-FAMILY-COVERAGE-2026-06-27-01', failures, ['ruleFamilyCoverageCoordinate']);
  requireEqual0(status.checkerDependencyGraphCoordinate, 'PNP-CHECKER-DEPENDENCY-GRAPH-2026-06-27-01', failures, ['checkerDependencyGraphCoordinate']);
  requireEqual0(status.checkerAuthorityGraphCoordinate, 'PNP-CHECKER-AUTHORITY-GRAPH-2026-06-27-01', failures, ['checkerAuthorityGraphCoordinate']);
  requireEqual0(status.nandDirectWireSemanticsCoordinate, 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01', failures, ['nandDirectWireSemanticsCoordinate']);
  requireEqual0(status.nandSmallModelsCoordinate, 'PNP-NAND-SMALL-MODELS-2026-06-27-01', failures, ['nandSmallModelsCoordinate']);
  requireEqual0(status.lockedNANDSATSmallModelsCoordinate, 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01', failures, ['lockedNANDSATSmallModelsCoordinate']);
  requireEqual0(status.complexityLedgerCoordinate, 'PNP-COMPLEXITY-LEDGER-2026-06-27-01', failures, ['complexityLedgerCoordinate']);
  requireEqual0(status.noHiddenOracleAuditCoordinate, 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01', failures, ['noHiddenOracleAuditCoordinate']);
  requireEqual0(status.noSharedCodePolicyCoordinate, 'PNP-INDEPENDENT-VERIFIERS-NO-SHARED-CODE-2026-06-27-01', failures, ['noSharedCodePolicyCoordinate']);

  if (failures.length !== 0) return { tag: 'reject', id: 'status-file-consistency', coord: 'StatusFile.ValidationFailed', path: failures[0].path, witness: { failures } };

  return { tag: 'accept', id: 'status-file-consistency', kind: 'json-status', statusSha256: sha256Hex0(bytes), publicTheoremEmissionAllowed: status.publicTheoremEmissionAllowed, finalTheoremReady: status.finalTheoremReady, activeFinalNodeIds: status.activeFinalNodeIds, remainingBlockers: status.remainingBlockers };
}

function requireEqual0(actual, expected, failures, pathArray) { if (actual !== expected) failures.push({ path: pathArray, expected, actual }); }
function requireArrayEqual0(actual, expected, failures, pathArray) { if (!Array.isArray(actual) || actual.length !== expected.length || actual.some((value, index) => value !== expected[index])) failures.push({ path: pathArray, expected, actual }); }

async function runPythonUnitTests0(root, python) {
  const candidates = python ? [python] : ['python3', 'python'];
  const spawnErrors = [];
  for (const executable of candidates) {
    const step = await runStep0({ id: 'independent-python-unit-tests', command: executable, args: ['-m', 'unittest', 'discover', 'independent-verifiers/python', '-p', '*_test.py'], root, kind: 'process' });
    if (step.tag === 'accept') return { ...step, executable };
    if (step.coord !== 'Process.SpawnFailed' || step.witness?.code !== 'ENOENT') return step;
    spawnErrors.push(step.witness);
  }
  return { tag: 'reject', id: 'independent-python-unit-tests', coord: 'Python.NotFound', path: ['independent-verifiers/python'], witness: { reason: 'no Python executable found', spawnErrors } };
}

function runStep0({ id, command, args, root, kind }) {
  return new Promise((resolve) => {
    const child = spawn(command, args, { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    let settled = false;
    child.stdout.on('data', (chunk) => { stdout += chunk.toString('utf8'); });
    child.stderr.on('data', (chunk) => { stderr += chunk.toString('utf8'); });
    child.on('error', (error) => {
      if (settled) return;
      settled = true;
      resolve({ tag: 'reject', id, kind, coord: 'Process.SpawnFailed', path: [id], command: renderCommand0(command, args), witness: normalizeError0(error) });
    });
    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      const base = { id, kind, command: renderCommand0(command, args), exitCode: code, stdoutSha256: sha256Hex0(Buffer.from(stdout, 'utf8')), stderrSha256: sha256Hex0(Buffer.from(stderr, 'utf8')), stdoutPreview: preview0(stdout), stderrPreview: preview0(stderr) };
      if (code !== 0) { resolve({ tag: 'reject', ...base, coord: 'Process.NonZeroExit', path: [id], witness: { reason: 'process exited non-zero', code } }); return; }
      if (kind === 'json') {
        try { resolve({ tag: 'accept', ...base, json: JSON.parse(stdout) }); }
        catch (error) { resolve({ tag: 'reject', ...base, coord: 'Process.BadJson', path: [id], witness: { reason: 'process stdout was not parseable JSON', error: normalizeError0(error) } }); }
        return;
      }
      resolve({ tag: 'accept', ...base });
    });
  });
}

function failFromStep0(step, steps) { return makeReject0(step.coord ?? 'Step.Reject', [step.id ?? 'unknown-step'], 'pnp verify step failed', { failedStep: step }, steps); }
function makeReject0(coord, pathArray, reason, witness = {}, steps = []) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS], steps }; }
async function writeAndReturn0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const absoluteOutputPath = path.join(root, outputPath); await mkdir(path.dirname(absoluteOutputPath), { recursive: true }); await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function renderCommand0(command, args) { return [command, ...args].join(' '); }
function preview0(text) { if (!text) return ''; return text.length > 4000 ? `${text.slice(0, 4000)}\n...[truncated ${text.length - 4000} bytes]` : text; }
function sha256Hex0(buffer) { return createHash('sha256').update(buffer).digest('hex'); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false, includeUnitTests: true, includeReleaseAudit: true, python: null };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--skip-unit-tests') options.includeUnitTests = false;
    else if (arg === '--skip-release-audit') options.includeReleaseAudit = false;
    else if (arg === '--root') { index += 1; if (index >= argv.length) throw new Error('--root requires a value'); options.root = argv[index]; }
    else if (arg === '--output') { index += 1; if (index >= argv.length) throw new Error('--output requires a value'); options.outputPath = argv[index]; }
    else if (arg === '--python') { index += 1; if (index >= argv.length) throw new Error('--python requires a value'); options.python = argv[index]; }
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

function printHelp0() {
  console.log(`Usage: node scripts/pnp-verify-all.mjs [options]\n\nOptions:\n  --json               Emit verdict JSON.\n  --no-write           Do not write artifacts/pnp-verify-all/latest-verdict.json.\n  --skip-unit-tests    Skip node --test.\n  --skip-release-audit Skip release:audit step.\n  --root <path>        Repository root. Defaults to cwd.\n  --output <path>      Verdict output path relative to root.\n  --python <path>      Python executable. Defaults to PYTHON, python3, then python.\n`);
}

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = makeReject0('Cli.BadArgument', [], 'bad pnp verify CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await RunPNPVerifyAll0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
