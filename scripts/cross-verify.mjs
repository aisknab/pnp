#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  CheckMinimalKernel0,
  MINIMAL_KERNEL_REMAINING_BLOCKERS0,
  PNP_MINIMAL_KERNEL_COORDINATE0,
  makeMinimalKernelInput0,
} from '../pcc-minimal-kernel0.mjs';

const VERSION = 0;
const CHECKER = 'cross-verify-minimal-kernel0';
const DEFAULT_OUTPUT_PATH = 'artifacts/cross-verify/latest-verdict.json';
const KERNEL_PATH = 'kernel/PNP_MINIMAL_KERNEL.json';
const REPORT_BINDINGS_PATH = 'report-bindings/REPORT_THEOREM_BINDINGS.json';
const PYTHON_VERIFIER_PATH = 'independent-verifiers/python/verify_minimal_kernel.py';
const THEOREM_BINDING_AUDIT_PATH = 'scripts/audit-report-theorem-bindings.mjs';

export async function CrossVerifyMinimalKernel0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  const python = options.python ?? process.env.PYTHON ?? null;

  try {
    const kernelBytes = await readFile(path.join(root, KERNEL_PATH));
    const reportBindingBytes = await readFile(path.join(root, REPORT_BINDINGS_PATH));
    const kernel = JSON.parse(kernelBytes.toString('utf8'));

    const kernelSha256 = sha256Hex0(kernelBytes);
    const reportBindingsSha256 = sha256Hex0(reportBindingBytes);

    const jsVerdict = await CheckMinimalKernel0(makeMinimalKernelInput0({ Kernel: kernel }));
    if (jsVerdict.tag !== 'accept') {
      return reject0('JSMinimalKernel.Reject', [], 'CheckMinimalKernel0 rejected', {
        jsVerdict: slimReject0(jsVerdict),
      });
    }

    const theoremAudit = await runJsonCommand0({
      root,
      command: process.execPath,
      args: [THEOREM_BINDING_AUDIT_PATH, '--json'],
      label: 'audit-report-theorem-bindings0',
    });
    if (theoremAudit.tag !== 'accept') return theoremAudit;
    if (theoremAudit.verdict.tag !== 'accept') {
      return reject0('TheoremBindingAudit.Reject', [], 'the theorem-binding audit rejected', {
        theoremAudit: slimReject0(theoremAudit.verdict),
      });
    }

    const pythonVerdict = await runPythonVerifier0({ root, python });
    if (pythonVerdict.tag !== 'accept') return pythonVerdict;
    if (pythonVerdict.verdict.tag !== 'accept') {
      return reject0('PythonVerifier.Reject', [], 'independent Python verifier rejected', {
        pythonVerdict: slimReject0(pythonVerdict.verdict),
      });
    }

    const agreements = computeAgreements0({
      jsVerdict,
      theoremAudit: theoremAudit.verdict,
      pythonVerdict: pythonVerdict.verdict,
      kernelSha256,
      reportBindingsSha256,
    });

    const failed = Object.entries(agreements).filter(([, ok]) => ok !== true).map(([key]) => key);
    if (failed.length !== 0) {
      return reject0('CrossVerifierAgreement.Mismatch', failed, 'cross-verifier agreement failed', {
        failed,
        agreements,
      });
    }

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      claimStatus: 'minimal-kernel-cross-verifier-agreement-accepted',
      coordinate: PNP_MINIMAL_KERNEL_COORDINATE0,
      kernelPath: KERNEL_PATH,
      kernelSha256,
      reportBindingsPath: REPORT_BINDINGS_PATH,
      reportBindingsSha256,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...MINIMAL_KERNEL_REMAINING_BLOCKERS0],
      agreement: agreements,
      verifiers: [
        {
          id: 'js:CheckMinimalKernel0',
          tag: jsVerdict.tag,
          coordinate: jsVerdict.NF.coordinate,
          kernelCanonicalDigest: jsVerdict.NF.kernelDigest.hex,
          proofSpineCount: jsVerdict.NF.proofSpineCount,
          checkerSurfaceCount: jsVerdict.NF.checkerSurfaceCount,
        },
        {
          id: 'js:audit-report-theorem-bindings0',
          tag: theoremAudit.verdict.tag,
          coordinate: theoremAudit.verdict.coordinate,
          ledgerSha256: theoremAudit.verdict.ledgerSha256,
          theoremBindingCount: theoremAudit.verdict.theoremBindingCount,
        },
        {
          id: 'python:independent-python-minimal-kernel0',
          tag: pythonVerdict.verdict.tag,
          coordinate: pythonVerdict.verdict.coordinate,
          executable: pythonVerdict.executable,
          kernelSha256: pythonVerdict.verdict.kernelSha256,
          reportBindingsSha256: pythonVerdict.verdict.reportBindingsSha256,
          proofSpineCount: pythonVerdict.verdict.proofSpineCount,
          checkerSurfaceCount: pythonVerdict.verdict.checkerSurfaceCount,
        },
      ],
      optionalVerifiers: {
        rust: {
          configured: false,
          requiredForAccept: false,
          status: 'not-configured',
        },
      },
      outputPath: writeOutput ? outputPath : null,
    };

    if (writeOutput) {
      const absoluteOutputPath = path.join(root, outputPath);
      await mkdir(path.dirname(absoluteOutputPath), { recursive: true });
      await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
    }

    return verdict;
  } catch (error) {
    return reject0('CrossVerifier.UnhandledException', [], 'cross verifier threw unexpectedly', normalizeError0(error));
  }
}

function computeAgreements0({ jsVerdict, theoremAudit, pythonVerdict, kernelSha256, reportBindingsSha256 }) {
  return {
    jsVerifierAccepted: jsVerdict.tag === 'accept',
    theoremBindingAuditAccepted: theoremAudit.tag === 'accept',
    pythonVerifierAccepted: pythonVerdict.tag === 'accept',
    coordinateMatches: jsVerdict.NF.coordinate === PNP_MINIMAL_KERNEL_COORDINATE0 && pythonVerdict.coordinate === PNP_MINIMAL_KERNEL_COORDINATE0,
    kernelSha256Matches: pythonVerdict.kernelSha256 === kernelSha256,
    reportBindingsSha256Matches: pythonVerdict.reportBindingsSha256 === reportBindingsSha256 && theoremAudit.ledgerSha256 === reportBindingsSha256,
    checkerSurfaceCountMatches: jsVerdict.NF.checkerSurfaceCount === pythonVerdict.checkerSurfaceCount,
    proofSpineCountMatches: jsVerdict.NF.proofSpineCount === pythonVerdict.proofSpineCount,
    publicTheoremEmissionDisabled: jsVerdict.NF.publicTheoremEmissionAllowed === false && pythonVerdict.publicTheoremEmissionAllowed === false,
    finalTheoremReadyDisabled: jsVerdict.NF.finalTheoremReady === false && pythonVerdict.finalTheoremReady === false,
    activeFinalNodesEmpty: sameStringArray0(jsVerdict.NF.activeFinalNodeIds, []) && sameStringArray0(pythonVerdict.activeFinalNodeIds, []),
    remainingBlockersMatch: sameStringArray0(jsVerdict.NF.remainingBlockers, MINIMAL_KERNEL_REMAINING_BLOCKERS0) && sameStringArray0(pythonVerdict.remainingBlockers, MINIMAL_KERNEL_REMAINING_BLOCKERS0),
  };
}

async function runPythonVerifier0({ root, python }) {
  const candidates = python ? [python] : ['python3', 'python'];
  const errors = [];

  for (const executable of candidates) {
    const result = await runJsonCommand0({
      root,
      command: executable,
      args: [PYTHON_VERIFIER_PATH, '--json'],
      label: 'independent-python-minimal-kernel0',
      missingCommandAsReject: false,
    });
    if (result.tag === 'accept') return { ...result, executable };
    if (result.coord !== 'Process.SpawnFailed' || result.witness?.code !== 'ENOENT') return result;
    errors.push(result.witness);
  }

  return reject0('PythonVerifier.NotFound', [PYTHON_VERIFIER_PATH], 'no Python executable could run the independent verifier', { errors });
}

function runJsonCommand0({ root, command, args, label, missingCommandAsReject = true }) {
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
      const verdict = reject0('Process.SpawnFailed', [label], 'could not spawn verifier process', normalizeError0(error));
      resolve(missingCommandAsReject ? verdict : verdict);
    });

    child.on('close', (code) => {
      if (settled) return;
      settled = true;
      if (code !== 0) {
        resolve(reject0('Process.NonZeroExit', [label], 'verifier process exited non-zero', { code, stdout: stdout.slice(0, 4000), stderr: stderr.slice(0, 4000) }));
        return;
      }
      try {
        resolve({ tag: 'accept', verdict: JSON.parse(stdout), stdout, stderr });
      } catch (error) {
        resolve(reject0('Process.BadJson', [label], 'verifier process did not emit parseable JSON', { stdout: stdout.slice(0, 4000), stderr: stderr.slice(0, 4000), error: normalizeError0(error) }));
      }
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
  };
}

function slimReject0(verdict) {
  return {
    tag: verdict?.tag ?? null,
    coord: verdict?.coord ?? verdict?.Coord ?? null,
    path: verdict?.path ?? verdict?.Path ?? null,
    witness: verdict?.witness ?? verdict?.Witness ?? null,
  };
}

function sha256Hex0(buffer) {
  return createHash('sha256').update(buffer).digest('hex');
}

function sameStringArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function normalizeError0(error) {
  return {
    name: error?.name ?? 'Error',
    message: error?.message ?? String(error),
    code: error?.code ?? null,
  };
}

function parseArgs0(argv) {
  const options = { root: process.cwd(), outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false, python: null };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') {
      index += 1;
      if (index >= argv.length) throw new Error('--root requires a value');
      options.root = argv[index];
    } else if (arg === '--output') {
      index += 1;
      if (index >= argv.length) throw new Error('--output requires a value');
      options.outputPath = argv[index];
    } else if (arg === '--python') {
      index += 1;
      if (index >= argv.length) throw new Error('--python requires a value');
      options.python = argv[index];
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
  console.log(`Usage: node scripts/cross-verify.mjs [options]\n\nOptions:\n  --json              Emit verdict JSON.\n  --no-write          Do not write artifacts/cross-verify/latest-verdict.json.\n  --root <path>       Repository root. Defaults to cwd.\n  --output <path>     Verdict output path relative to root.\n  --python <path>     Python executable. Defaults to PYTHON, python3, then python.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad cross-verifier CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await CrossVerifyMinimalKernel0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0();
}
