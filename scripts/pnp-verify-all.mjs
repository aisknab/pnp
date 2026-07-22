#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  CheckFormalReconstructionStatus0,
  FORMAL_RECONSTRUCTION_BLOCKERS0,
} from '../pcc-formal-reconstruction-status0.mjs';
import { CheckFormalPublicSurface0 } from '../pcc-formal-public-surface0.mjs';
import { CheckLegacyV0Archive0 } from '../pcc-legacy-v0-archive0.mjs';

const CHECKER = 'pnp-verify-all0';
const VERSION = 0;
const OUTPUT = 'artifacts/pnp-verify-all/latest-verdict.json';

export const CURRENT_VERIFICATION_TESTS0 = Object.freeze([
  'audits/formal-reconstruction-status0.test.mjs',
  'audits/formal-public-surface0.test.mjs',
  'audits/lean-theorem-inventory0.test.mjs',
  'audits/formal-publication0.test.mjs',
  'audits/lean-root-target0.test.mjs',
  'audits/lean-concrete-machine0.test.mjs',
  'audits/lean-concrete-tape-handoff0.test.mjs',
  'audits/lean-concrete-tape-blank-equivalence0.test.mjs',
  'audits/lean-concrete-pipeline-tape-geometry0.test.mjs',
  'audits/lean-concrete-pipeline-input-framer0.test.mjs',
  'audits/lean-concrete-pipeline-output-handoff0.test.mjs',
  'audits/lean-concrete-pipeline-state-namespace0.test.mjs',
  'audits/lean-concrete-pipeline-sequential-state-namespace0.test.mjs',
  'audits/lean-concrete-pipeline-sequential-compiler0.test.mjs',
  'audits/lean-concrete-pipeline-stage-bridges0.test.mjs',
  'audits/lean-concrete-terminal-output-packer0.test.mjs',
  'audits/lean-concrete-pipeline-terminal-bridge0.test.mjs',
  'audits/lean-concrete-pipeline-paired-compiler0.test.mjs',
  'audits/lean-concrete-pipeline-compiler0.test.mjs',
  'audits/lean-concrete-pipeline-machine-simulation0.test.mjs',
  'audits/lean-concrete-complexity0.test.mjs',
  'audits/lean-concrete-pipeline-refinement0.test.mjs',
  'audits/lean-concrete-cnf0.test.mjs',
  'audits/lean-concrete-cook-levin-layout0.test.mjs',
  'audits/lean-concrete-cook-levin-tableau0.test.mjs',
  'audits/lean-concrete-cook-levin-verifier-tableau0.test.mjs',
  'audits/lean-concrete-cook-levin-local-cnf0.test.mjs',
  'audits/lean-concrete-cook-levin-tableau-cnf0.test.mjs',
  'audits/lean-concrete-cook-levin-tableau-cnf-semantics0.test.mjs',
  'audits/lean-concrete-cook-levin-raw-tape-bridge0.test.mjs',
  'audits/lean-concrete-cook-levin-formula-size0.test.mjs',
  'audits/lean-concrete-cook-levin-formula-schedule0.test.mjs',
  'audits/lean-concrete-cook-levin-formula-cursor0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-input-length0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-input-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-token-appender0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-first-token-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-complete-header0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-body-start-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-first-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-first-clause-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-dynamic-token-cursor-step0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-first-clause-padding-run0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-clause-separator-step0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-clause-first-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-clause-second-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-clause-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-clause-padding-run0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-third-clause-separator-step0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-third-clause-first-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-third-clause-second-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-third-clause-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-third-clause-padding-run0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-fourth-clause-separator-step0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-fourth-clause-first-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-fourth-clause-second-literal-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-fourth-clause-prefix0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-fourth-clause-padding-run0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-fifth-clause-padding-run0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-first-constraint-padding-run0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-constraint-separator-step0.test.mjs',
  'audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-sign-step0.test.mjs',
  'audits/lean-nand-semantics0.test.mjs',
  'audits/lean-nand-enumerator0.test.mjs',
  'audits/lean-nand-reference-minimum0.test.mjs',
  'audits/lean-locked-nand-baseline0.test.mjs',
  'audits/lean-locked-nand-threshold-boundary0.test.mjs',
  'audits/lean-residual-routes0.test.mjs',
  'audits/legacy-v0-archive0.test.mjs',
  'test/current-package-surface0.test.mjs',
  'test/current-verifier0.test.mjs',
  'test/replay-legacy-v0.test.mjs',
]);

export function MakeCurrentVerificationPlan0(options = {}) {
  return Object.freeze([
    Object.freeze({ id: 'formal-reconstruction-status', kind: 'checker' }),
    Object.freeze({ id: 'formal-public-surface', kind: 'checker' }),
    Object.freeze({ id: 'legacy-v0-archive-integrity', kind: 'checker' }),
    ...(options.includeUnitTests === false
      ? []
      : [Object.freeze({ id: 'current-authority-unit-tests', kind: 'process', files: [...CURRENT_VERIFICATION_TESTS0] })]),
  ]);
}

export async function RunPNPVerifyAll0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUTPUT;
  const writeOutput = options.writeOutput ?? true;
  const plan = MakeCurrentVerificationPlan0(options);
  const steps = [];

  const checkers = [
    ['formal-reconstruction-status', () => CheckFormalReconstructionStatus0({ root, writeOutput: false })],
    ['formal-public-surface', () => CheckFormalPublicSurface0({ root, writeOutput: false })],
    ['legacy-v0-archive-integrity', () => CheckLegacyV0Archive0({ root, writeOutput: false })],
  ];

  for (const [id, check] of checkers) {
    const verdict = await check();
    const step = { ...verdict, id };
    steps.push(step);
    if (verdict.tag !== 'accept') {
      return finish0(root, outputPath, writeOutput, reject0(
        'CurrentVerification.CheckerRejected',
        [id],
        'a current-authority checker rejected',
        { failedStep: step, steps },
      ));
    }
  }

  if (options.includeUnitTests !== false) {
    const step = await runNodeTests0(root, CURRENT_VERIFICATION_TESTS0);
    steps.push(step);
    if (step.tag !== 'accept') {
      return finish0(root, outputPath, writeOutput, reject0(
        'CurrentVerification.TestsRejected',
        ['current-authority-unit-tests'],
        'the current-authority unit suite failed',
        { failedStep: step, steps },
      ));
    }
  }

  const statusStep = steps.find((step) => step.id === 'formal-reconstruction-status');
  const surfaceStep = steps.find((step) => step.id === 'formal-public-surface');
  const archiveStep = steps.find((step) => step.id === 'legacy-v0-archive-integrity');
  return finish0(root, outputPath, writeOutput, {
    tag: 'accept',
    kind: 'accept',
    checker: CHECKER,
    version: VERSION,
    claimStatus: 'formal-reconstruction-in-progress',
    currentStatusAuthority: true,
    targetTheorem: 'P = NP',
    mathematicalTheoremEstablished: statusStep?.mathematicalTheoremEstablished ?? false,
    checkerAcceptanceIsMathematicalProof: false,
    publicTheoremEmissionAllowed: statusStep?.publicTheoremEmissionAllowed ?? false,
    leanConcreteCNFVerifierCorrectnessFormalized:
      statusStep?.leanConcreteCNFVerifierCorrectnessFormalized ?? false,
    leanConcreteCNFVerifierNoTimeoutFormalized:
      statusStep?.leanConcreteCNFVerifierNoTimeoutFormalized ?? false,
    leanConcreteCNFSATMembershipFormalized:
      statusStep?.leanConcreteCNFSATMembershipFormalized ?? false,
    leanConcreteCNFSATMembershipTheorem:
      statusStep?.leanConcreteCNFSATMembershipTheorem ?? null,
    leanConcreteCNFProofScope: statusStep?.leanConcreteCNFProofScope ?? null,
    leanConcreteCNFSATInPFormalized: false,
    leanConcreteCNFNPCompletenessFormalized: false,
    publicTheoremStatement: statusStep?.publicTheoremStatement ?? null,
    publicTheoremConclusion: statusStep?.publicTheoremConclusion ?? null,
    finalTheoremReady: statusStep?.finalTheoremReady ?? false,
    activeFinalNodeIds: [],
    remainingFormalObligations: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
    remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
    historicalReplayExecuted: false,
    legacyCheckerReplayAccepted: false,
    legacyCheckerReplayIsMathematicalProof: false,
    archiveIdentityVerified: archiveStep?.tagObjectIdentityVerified === true
      && archiveStep?.archivedFileDigestsVerified === true,
    statusSha256: statusStep?.statusSha256 ?? null,
    publicSurfaceBaselineCoordinate: surfaceStep?.coordinate ?? null,
    oneCommand: 'npm run pnp:verify -- --no-write',
    plan,
    stepCount: steps.length,
    acceptedStepCount: steps.filter((step) => step.tag === 'accept').length,
    steps,
  });
}

function runNodeTests0(root, files) {
  return new Promise((resolve) => {
    const args = ['--test', ...files];
    const child = spawn(process.execPath, args, { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    let settled = false;
    child.stdout.on('data', (chunk) => { stdout += chunk.toString('utf8'); });
    child.stderr.on('data', (chunk) => { stderr += chunk.toString('utf8'); });
    child.on('error', (error) => {
      if (settled) return;
      settled = true;
      resolve({
        tag: 'reject',
        id: 'current-authority-unit-tests',
        coord: 'Process.SpawnFailed',
        path: ['current-authority-unit-tests'],
        witness: normalizeError0(error),
      });
    });
    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      const base = {
        id: 'current-authority-unit-tests',
        kind: 'process',
        command: [process.execPath, ...args].join(' '),
        exitCode: code,
        stdoutSha256: sha2560(stdout),
        stderrSha256: sha2560(stderr),
        stdoutPreview: preview0(stdout),
        stderrPreview: preview0(stderr),
      };
      resolve(code === 0
        ? { tag: 'accept', ...base }
        : { tag: 'reject', ...base, coord: 'Process.NonZeroExit', path: ['current-authority-unit-tests'] });
    });
  });
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
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    leanConcreteCNFVerifierCorrectnessFormalized: false,
    leanConcreteCNFVerifierNoTimeoutFormalized: false,
    leanConcreteCNFSATMembershipFormalized: false,
    finalTheoremReady: false,
    historicalReplayExecuted: false,
    remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
  };
}

async function finish0(root, outputPath, enabled, verdict) {
  const rendered = { ...verdict, outputPath: enabled ? outputPath : null };
  if (enabled) {
    const absolute = path.join(root, outputPath);
    await mkdir(path.dirname(absolute), { recursive: true });
    await writeFile(absolute, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
}

function sha2560(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

function preview0(text) {
  return text.length > 4000 ? `${text.slice(0, 4000)}\n...[truncated]` : text;
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}

function parseArgs0(argv) {
  const options = { json: false, writeOutput: true, includeUnitTests: true };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--skip-unit-tests') options.includeUnitTests = false;
    else if (arg === '--root') {
      const value = argv[++i];
      if (value === undefined) throw new Error('--root requires a value');
      options.root = value;
    } else if (arg === '--output') {
      const value = argv[++i];
      if (value === undefined) throw new Error('--output requires a value');
      options.outputPath = value;
    } else if (arg === '--help' || arg === '-h') options.help = true;
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
    if (options.help) {
      console.log('Usage: node scripts/pnp-verify-all.mjs [--json] [--no-write] [--skip-unit-tests] [--root <path>] [--output <path>]');
      return;
    }
  } catch (error) {
    console.error(JSON.stringify(reject0('CurrentVerification.CliArgument', [], 'invalid command-line argument', normalizeError0(error)), null, 2));
    process.exitCode = 2;
    return;
  }
  const verdict = await RunPNPVerifyAll0(options);
  console.log(JSON.stringify(verdict, null, 2));
  process.exitCode = verdict.tag === 'accept' ? 0 : 1;
}

if (import.meta.url === `file://${process.argv[1]}`) await main0();
