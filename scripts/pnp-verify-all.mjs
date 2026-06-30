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

const EXPECTED_STATUS_FIELDS = {
  project: 'PNP',
  internalProofStackAccepted: true,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  pnpVerifyCommand: 'npm run pnp:verify',
  minimalKernelCoordinate: 'PNP-MINIMAL-KERNEL-2026-06-27-01',
  theoremBindingLedgerCoordinate: 'REPORT-THEOREM-BINDINGS-2026-06-27-01',
  reportTheoremInventoryCoordinate: 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01',
  reportTheoremCoverageMatrixCoordinate: 'PNP-REPORT-THEOREM-COVERAGE-MATRIX-2026-06-27-01',
  reportTheoremCoverageClosurePlanCoordinate: 'PNP-REPORT-THEOREM-COVERAGE-CLOSURE-PLAN-2026-06-27-01',
  baseDirectBindingSeedCoordinate: 'PNP-DIRECT-BIND-BASE-SEMANTICS-SEED-2026-06-27-01',
  chgDirectBindingSeedCoordinate: 'PNP-DIRECT-BIND-CHG-CHARGE-LEDGER-SEED-2026-06-27-01',
  modeDirectBindingSeedCoordinate: 'PNP-DIRECT-BIND-MODE-FIREWALL-SEED-2026-06-27-01',
  eDirectBindingSeedCoordinate: 'PNP-DIRECT-BIND-E-VERIFYDW-SOUNDNESS-SEED-2026-06-27-01',
  noProseOnlyTheoremPolicyCoordinate: 'PNP-NO-PROSE-ONLY-THEOREM-POLICY-2026-06-27-01',
  proofObligationLedgerCoordinate: 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01',
  gapLedgerCoordinate: 'PNP-GAP-LEDGER-2026-06-27-01',
  finiteToUnboundedFamilyAuditCoordinate: 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01',
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
  freshCloneVerifyCoordinate: 'PNP-FRESH-CLONE-VERIFY-2026-06-27-01',
  containerEnvironmentCoordinate: 'PNP-CONTAINER-ENVIRONMENT-2026-06-27-01',
  multiPlatformCICoordinate: 'PNP-MULTI-PLATFORM-CI-2026-06-27-01',
  determinismAuditCoordinate: 'PNP-DETERMINISM-AUDIT-2026-06-27-01',
  regenerationLedgerCoordinate: 'PNP-REGENERATION-LEDGER-2026-06-27-01',
  releaseLadderCoordinate: 'PNP-RELEASE-LADDER-2026-06-27-01',
  noSharedCodePolicyCoordinate: 'PNP-INDEPENDENT-VERIFIERS-NO-SHARED-CODE-2026-06-27-01',
};

const NODE_SYNTAX_TARGETS = [
  'pcc-core.mjs', 'pcc-trust-base0.mjs', 'pcc-trust-base-shrink-plan0.mjs', 'pcc-rule-family-coverage0.mjs',
  'pcc-nand-direct-wire-semantics0.mjs', 'pcc-nand-small-models0.mjs', 'pcc-locked-nand-sat-small-models0.mjs',
  'pcc-complexity-ledger0.mjs', 'pcc-release-ladder0.mjs', 'pcc-proof-obligation-ledger0.mjs', 'pcc-gap-ledger0.mjs',
  'pcc-finite-to-unbounded-family-audit0.mjs', 'pcc-no-prose-only-theorem-policy0.mjs', 'pcc-report-theorem-inventory0.mjs',
  'pcc-report-theorem-coverage-matrix0.mjs', 'pcc-report-theorem-coverage-closure-plan0.mjs', 'pcc-direct-bind-base-semantics0.mjs',
  'pcc-direct-bind-charge-ledger0.mjs', 'pcc-direct-bind-mode-firewall0.mjs', 'pcc-direct-bind-verifydw-soundness0.mjs',
  'semantics/nand-direct-wire-reference.mjs', 'semantics/nand-small-models.mjs', 'semantics/locked-nand-sat-small-models.mjs',
  'scripts/cross-verify.mjs', 'scripts/audit-report-theorem-bindings.mjs', 'scripts/audit-independent-verifiers-no-shared-code.mjs',
  'scripts/audit-checker-totality.mjs', 'scripts/audit-negative-checker-mutations.mjs', 'scripts/generate-checker-dependency-graph.mjs',
  'scripts/audit-checker-cycles.mjs', 'scripts/audit-no-hidden-oracle.mjs', 'scripts/audit-determinism.mjs',
  'scripts/audit-regeneration-ledger.mjs', 'scripts/pnp-verify-all.mjs',
];

const REQUIRED_STEPS = [
  ['theorem-binding-ledger-audit', ['scripts/audit-report-theorem-bindings.mjs', '--json'], 'json'],
  ['report-theorem-inventory-audit', ['pcc-report-theorem-inventory0.mjs', '--json'], 'json'],
  ['report-theorem-inventory-tests', ['--test', 'audits/report-theorem-inventory0.test.mjs'], 'process'],
  ['report-theorem-coverage-matrix-audit', ['pcc-report-theorem-coverage-matrix0.mjs', '--json'], 'json'],
  ['report-theorem-coverage-matrix-tests', ['--test', 'audits/report-theorem-coverage-matrix0.test.mjs'], 'process'],
  ['report-theorem-coverage-closure-plan-audit', ['pcc-report-theorem-coverage-closure-plan0.mjs', '--json'], 'json'],
  ['report-theorem-coverage-closure-plan-tests', ['--test', 'audits/report-theorem-coverage-closure-plan0.test.mjs'], 'process'],
  ['base-direct-binding-seed-audit', ['pcc-direct-bind-base-semantics0.mjs', '--json'], 'json'],
  ['base-direct-binding-seed-tests', ['--test', 'audits/direct-bind-base-semantics0.test.mjs'], 'process'],
  ['chg-direct-binding-seed-audit', ['pcc-direct-bind-charge-ledger0.mjs', '--json'], 'json'],
  ['chg-direct-binding-seed-tests', ['--test', 'audits/direct-bind-charge-ledger0.test.mjs'], 'process'],
  ['mode-direct-binding-seed-audit', ['pcc-direct-bind-mode-firewall0.mjs', '--json'], 'json'],
  ['mode-direct-binding-seed-tests', ['--test', 'audits/direct-bind-mode-firewall0.test.mjs'], 'process'],
  ['e-direct-binding-seed-audit', ['pcc-direct-bind-verifydw-soundness0.mjs', '--json'], 'json'],
  ['e-direct-binding-seed-tests', ['--test', 'audits/direct-bind-verifydw-soundness0.test.mjs'], 'process'],
  ['no-prose-only-theorem-policy-audit', ['pcc-no-prose-only-theorem-policy0.mjs', '--json'], 'json'],
  ['no-prose-only-theorem-policy-tests', ['--test', 'audits/no-prose-only-theorem-policy0.test.mjs'], 'process'],
  ['proof-obligation-ledger-audit', ['pcc-proof-obligation-ledger0.mjs', '--json'], 'json'],
  ['proof-obligation-ledger-tests', ['--test', 'audits/proof-obligation-ledger0.test.mjs'], 'process'],
  ['gap-ledger-audit', ['pcc-gap-ledger0.mjs', '--json'], 'json'],
  ['gap-ledger-tests', ['--test', 'audits/gap-ledger0.test.mjs'], 'process'],
  ['finite-to-unbounded-family-audit', ['pcc-finite-to-unbounded-family-audit0.mjs', '--json'], 'json'],
  ['finite-to-unbounded-family-audit-tests', ['--test', 'audits/finite-to-unbounded-family-audit0.test.mjs'], 'process'],
  ['trust-base-audit', ['pcc-trust-base0.mjs', '--json'], 'json'],
  ['trust-base-tests', ['--test', 'audits/trust-base0.test.mjs'], 'process'],
  ['trust-base-shrink-plan-audit', ['pcc-trust-base-shrink-plan0.mjs', '--json'], 'json'],
  ['trust-base-shrink-plan-tests', ['--test', 'audits/trust-base-shrink-plan0.test.mjs'], 'process'],
  ['checker-totality-audit', ['scripts/audit-checker-totality.mjs', '--json'], 'json'],
  ['checker-totality-tests', ['--test', 'audits/checker-totality0.test.mjs'], 'process'],
  ['negative-checker-mutation-audit', ['scripts/audit-negative-checker-mutations.mjs', '--json'], 'json'],
  ['negative-checker-mutation-tests', ['--test', 'audits/negative-checker-mutations0.test.mjs'], 'process'],
  ['rule-family-coverage-audit', ['pcc-rule-family-coverage0.mjs', '--json'], 'json'],
  ['rule-family-coverage-tests', ['--test', 'audits/rule-family-coverage0.test.mjs'], 'process'],
  ['checker-dependency-graph-generation', ['scripts/generate-checker-dependency-graph.mjs', '--json'], 'json'],
  ['checker-dependency-graph-tests', ['--test', 'audits/checker-dependency-graph0.test.mjs'], 'process'],
  ['checker-cycle-audit', ['scripts/audit-checker-cycles.mjs', '--json'], 'json'],
  ['checker-cycle-tests', ['--test', 'audits/checker-cycles0.test.mjs'], 'process'],
  ['nand-direct-wire-semantics-audit', ['pcc-nand-direct-wire-semantics0.mjs', '--json'], 'json'],
  ['nand-direct-wire-semantics-tests', ['--test', 'audits/nand-direct-wire-semantics0.test.mjs'], 'process'],
  ['nand-small-model-audit', ['pcc-nand-small-models0.mjs', '--json'], 'json'],
  ['nand-small-model-tests', ['--test', 'audits/nand-small-models0.test.mjs'], 'process'],
  ['locked-nand-sat-small-model-audit', ['pcc-locked-nand-sat-small-models0.mjs', '--json'], 'json'],
  ['locked-nand-sat-small-model-tests', ['--test', 'audits/locked-nand-sat-small-models0.test.mjs'], 'process'],
  ['complexity-ledger-audit', ['pcc-complexity-ledger0.mjs', '--json'], 'json'],
  ['complexity-ledger-tests', ['--test', 'audits/complexity-ledger0.test.mjs'], 'process'],
  ['no-hidden-oracle-audit', ['scripts/audit-no-hidden-oracle.mjs', '--json'], 'json'],
  ['no-hidden-oracle-tests', ['--test', 'audits/no-hidden-oracle0.test.mjs'], 'process'],
  ['fresh-clone-verifier-tests', ['--test', 'audits/fresh-clone-verify0.test.mjs'], 'process'],
  ['container-environment-tests', ['--test', 'audits/container-environment0.test.mjs'], 'process'],
  ['multi-platform-ci-tests', ['--test', 'audits/multi-platform-ci0.test.mjs'], 'process'],
  ['determinism-audit-tests', ['--test', 'audits/determinism0.test.mjs'], 'process'],
  ['regeneration-ledger-audit', ['scripts/audit-regeneration-ledger.mjs', '--json'], 'json'],
  ['regeneration-ledger-tests', ['--test', 'audits/regeneration-ledger0.test.mjs'], 'process'],
  ['release-ladder-audit', ['pcc-release-ladder0.mjs', '--json'], 'json'],
  ['release-ladder-tests', ['--test', 'audits/release-ladder0.test.mjs'], 'process'],
  ['minimal-kernel-cross-verify', ['scripts/cross-verify.mjs', '--json'], 'json'],
  ['independent-no-shared-code-audit', ['scripts/audit-independent-verifiers-no-shared-code.mjs', '--json'], 'json'],
  ['independent-no-shared-code-tests', ['--test', 'audits/independent-verifiers-no-shared-code.test.mjs'], 'process'],
];

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

  for (const target of NODE_SYNTAX_TARGETS) {
    const step = await runStep0({ id: `node-syntax:${target}`, command: process.execPath, args: ['--check', target], root, kind: 'process' });
    steps.push(step);
    if (step.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(step, steps));
  }

  if (includeUnitTests) {
    const unitStep = await runStep0({ id: 'node-unit-tests', command: process.execPath, args: ['--test'], root, kind: 'process' });
    steps.push(unitStep);
    if (unitStep.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(unitStep, steps));
  }

  const stepsToRun = [...REQUIRED_STEPS.map(([id, args, kind]) => ({ id, command: process.execPath, args, kind })), ...(includeReleaseAudit ? [{ id: 'release-audit', command: process.execPath, args: ['./bin/release-audit0.mjs'], kind: 'process' }] : [])];
  for (const spec of stepsToRun) {
    const step = await runStep0({ ...spec, root });
    steps.push(step);
    if (step.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(step, steps));
    if (spec.kind === 'json' && step.json?.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, makeReject0('JsonStep.UnexpectedTag', [spec.id], 'JSON verifier returned an unexpected tag', { expectedTag: 'accept', actualTag: step.json?.tag ?? null, step }, steps));
  }

  const pythonStep = await runPythonUnitTests0(root, options.python ?? process.env.PYTHON ?? null);
  steps.push(pythonStep);
  if (pythonStep.tag !== 'accept') return writeAndReturn0(root, outputPath, writeOutput, failFromStep0(pythonStep, steps));

  return writeAndReturn0(root, outputPath, writeOutput, {
    tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION,
    claimStatus: 'internal-proof-certificate-stack-accepted-under-public-review-boundary',
    statusPath: PNP_STATUS_PATH, statusSha256: statusStep.statusSha256,
    ...Object.fromEntries(Object.entries(EXPECTED_STATUS_FIELDS).filter(([key]) => key.endsWith('Coordinate'))),
    publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS], oneCommand: 'npm run pnp:verify',
    stepCount: steps.length, acceptedStepCount: steps.filter((step) => step.tag === 'accept').length, steps, outputPath: writeOutput ? outputPath : null,
  });
}

async function verifyStatusFile0(root) {
  const absolutePath = path.join(root, PNP_STATUS_PATH);
  let bytes;
  let status;
  try { bytes = await readFile(absolutePath); status = JSON.parse(bytes.toString('utf8')); }
  catch (error) { return { tag: 'reject', id: 'status-file-consistency', coord: 'StatusFile.ReadOrParseFailed', path: [PNP_STATUS_PATH], witness: normalizeError0(error) }; }
  const failures = [];
  for (const [field, expected] of Object.entries(EXPECTED_STATUS_FIELDS)) requireEqual0(status[field], expected, failures, [field]);
  requireArrayEqual0(status.activeFinalNodeIds, [], failures, ['activeFinalNodeIds']);
  requireArrayEqual0(status.remainingBlockers, EXPECTED_BLOCKERS, failures, ['remainingBlockers']);
  if (failures.length !== 0) return { tag: 'reject', id: 'status-file-consistency', coord: 'StatusFile.ValidationFailed', path: failures[0].path, witness: { failures } };
  return { tag: 'accept', id: 'status-file-consistency', kind: 'json-status', statusSha256: sha256Hex0(bytes), publicTheoremEmissionAllowed: status.publicTheoremEmissionAllowed, finalTheoremReady: status.finalTheoremReady, activeFinalNodeIds: status.activeFinalNodeIds, remainingBlockers: status.remainingBlockers };
}

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
    child.on('error', (error) => { if (settled) return; settled = true; resolve({ tag: 'reject', id, kind, coord: 'Process.SpawnFailed', path: [id], command: renderCommand0(command, args), witness: normalizeError0(error) }); });
    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      const base = { id, kind, command: renderCommand0(command, args), exitCode: code, stdoutSha256: sha256Hex0(Buffer.from(stdout, 'utf8')), stderrSha256: sha256Hex0(Buffer.from(stderr, 'utf8')), stdoutPreview: preview0(stdout), stderrPreview: preview0(stderr) };
      if (code !== 0) { resolve({ tag: 'reject', ...base, coord: 'Process.NonZeroExit', path: [id], witness: { reason: 'process exited non-zero', code } }); return; }
      if (kind === 'json') { try { resolve({ tag: 'accept', ...base, json: JSON.parse(stdout) }); } catch (error) { resolve({ tag: 'reject', ...base, coord: 'Process.BadJson', path: [id], witness: { reason: 'process stdout was not parseable JSON', error: normalizeError0(error) } }); } return; }
      resolve({ tag: 'accept', ...base });
    });
  });
}

function requireEqual0(actual, expected, failures, pathArray) { if (actual !== expected) failures.push({ path: pathArray, expected, actual }); }
function requireArrayEqual0(actual, expected, failures, pathArray) { if (!Array.isArray(actual) || actual.length !== expected.length || actual.some((value, index) => value !== expected[index])) failures.push({ path: pathArray, expected, actual }); }
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
function printHelp0() { console.log(`Usage: node scripts/pnp-verify-all.mjs [options]\n\nOptions:\n  --json               Emit verdict JSON.\n  --no-write           Do not write artifacts/pnp-verify-all/latest-verdict.json.\n  --skip-unit-tests    Skip node --test.\n  --skip-release-audit Skip release:audit step.\n  --root <path>        Repository root. Defaults to cwd.\n  --output <path>      Verdict output path relative to root.\n  --python <path>      Python executable. Defaults to PYTHON, python3, then python.\n`); }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = makeReject0('Cli.BadArgument', [], 'bad pnp verify CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await RunPNPVerifyAll0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }

if (import.meta.url === `file://${process.argv[1]}`) main0();
