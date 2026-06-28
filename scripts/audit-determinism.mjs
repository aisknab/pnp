#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'AuditDeterminism0';
const VERSION = 0;
const MANIFEST_PATH = 'reproducibility/DETERMINISM_AUDIT.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/determinism-audit/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-DETERMINISM-AUDIT-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export async function AuditDeterminism0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readManifest0({ root, manifestPath, override: options.manifestOverride });
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);

    const manifestCheck = validateManifest0(manifestRead.manifest);
    if (manifestCheck.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestCheck);

    const command = options.command ?? manifestRead.manifest.defaultCommand;
    const generatedArtifactPaths = options.generatedArtifactPaths?.length
      ? options.generatedArtifactPaths
      : manifestRead.manifest.defaultGeneratedArtifactPaths;

    const stableBefore = await digestExistingFiles0(root, manifestRead.manifest.stableArtifactPaths, 'stable-before');
    if (stableBefore.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, stableBefore);

    const firstRun = await runCommand0({ root, command, runId: 'run1' });
    if (firstRun.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, firstRun);
    const stableAfterFirst = await digestExistingFiles0(root, manifestRead.manifest.stableArtifactPaths, 'stable-after-run1');
    if (stableAfterFirst.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, stableAfterFirst);
    const generatedAfterFirst = await digestExistingFiles0(root, generatedArtifactPaths, 'generated-after-run1');
    if (generatedAfterFirst.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, generatedAfterFirst);

    const secondRun = await runCommand0({ root, command, runId: 'run2' });
    if (secondRun.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, secondRun);
    const stableAfterSecond = await digestExistingFiles0(root, manifestRead.manifest.stableArtifactPaths, 'stable-after-run2');
    if (stableAfterSecond.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, stableAfterSecond);
    const generatedAfterSecond = await digestExistingFiles0(root, generatedArtifactPaths, 'generated-after-run2');
    if (generatedAfterSecond.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, generatedAfterSecond);

    const comparison = compareRuns0({
      firstRun,
      secondRun,
      stableBefore,
      stableAfterFirst,
      stableAfterSecond,
      generatedAfterFirst,
      generatedAfterSecond,
    });
    if (comparison.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, comparison);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'determinism-audit-accepted-under-public-review-boundary',
      manifestPath,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      command,
      determinismAuditReady: true,
      fullDeterminismProved: false,
      publicTheoremEmissionAllowedByAudit: false,
      runComparison: comparison.runComparison,
      stableArtifactCount: stableBefore.digests.length,
      generatedArtifactCount: generatedAfterFirst.digests.length,
      stableArtifactDigest: sha256Text0(stableStringify0(stableBefore.digests)),
      generatedArtifactDigest: sha256Text0(stableStringify0(generatedAfterFirst.digests)),
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('DeterminismAudit.UnhandledException', [], 'determinism audit threw unexpectedly', normalizeError0(error)));
  }
}

async function readManifest0({ root, manifestPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', manifest: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, manifestPath));
    return { tag: 'accept', manifest: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('DeterminismAudit.ManifestReadOrParseFailed', [manifestPath], 'could not read or parse determinism manifest', normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('DeterminismAudit.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPDeterminismAudit0') return reject0('DeterminismAudit.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('DeterminismAudit.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('DeterminismAudit.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: manifest.coordinate });
  if (manifest.status !== 'determinism-audit-ready') return reject0('DeterminismAudit.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.determinismAuditReady !== true) return reject0('DeterminismAudit.ReadyFlag', ['determinismAuditReady'], 'determinismAuditReady must be true');
  if (manifest.fullDeterminismProved !== false) return reject0('DeterminismAudit.FullProofFlag', ['fullDeterminismProved'], 'seed determinism audit cannot claim full determinism proof');
  if (manifest.publicTheoremEmissionAllowedByAudit !== false) return reject0('DeterminismAudit.PublicEmissionByAuditFlag', ['publicTheoremEmissionAllowedByAudit'], 'determinism audit cannot allow public theorem emission');
  if (!nonempty0(manifest.defaultCommand)) return reject0('DeterminismAudit.DefaultCommand', ['defaultCommand'], 'defaultCommand must be non-empty');
  if (!nonempty0(manifest.ciSmokeCommand)) return reject0('DeterminismAudit.CISmokeCommand', ['ciSmokeCommand'], 'ciSmokeCommand must be non-empty');

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  for (const field of ['stableArtifactPaths', 'defaultGeneratedArtifactPaths', 'ciGeneratedArtifactPaths', 'comparisonFields', 'nonClaims']) {
    const check = validateStringArray0(manifest[field], [field], true);
    if (check.tag === 'reject') return check;
  }

  const expectedComparisonFields = ['exitCode', 'stdoutSha256', 'stderrSha256', 'parsedJsonCanonicalSha256', 'stableArtifactDigestsBeforeAfter', 'generatedArtifactDigestsRun1Run2'];
  if (!sameArray0(manifest.comparisonFields, expectedComparisonFields)) return reject0('DeterminismAudit.ComparisonFields', ['comparisonFields'], 'comparison field list must stay exact and ordered', { expected: expectedComparisonFields, actual: manifest.comparisonFields });

  if (!plain0(manifest.ciMode)) return reject0('DeterminismAudit.CIModeShape', ['ciMode'], 'ciMode must be an object');
  if (manifest.ciMode.workflow !== '.github/workflows/determinism-audit.yml') return reject0('DeterminismAudit.CIModeWorkflow', ['ciMode', 'workflow'], 'ciMode workflow mismatch');
  if (!nonempty0(manifest.ciMode.command) || !nonempty0(manifest.ciMode.rationale)) return reject0('DeterminismAudit.CIModeFields', ['ciMode'], 'ciMode command and rationale must be non-empty');

  if (!plain0(manifest.audit)) return reject0('DeterminismAudit.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'scripts/audit-determinism.mjs',
    test: 'audits/determinism0.test.mjs',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('DeterminismAudit.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: manifest.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('DeterminismAudit.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('DeterminismAudit.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('DeterminismAudit.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('DeterminismAudit.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('DeterminismAudit.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function runCommand0({ root, command, runId }) {
  const result = await spawnShell0({ root, command });
  if (result.exitCode !== 0) return reject0('DeterminismAudit.CommandFailed', [runId], 'determinism command exited non-zero', { command, runId, result });
  const parsed = parseJsonMaybe0(result.stdout);
  return {
    tag: 'accept',
    runId,
    command,
    exitCode: result.exitCode,
    stdoutSha256: sha256Text0(result.stdout),
    stderrSha256: sha256Text0(result.stderr),
    parsedJsonCanonicalSha256: parsed.ok ? sha256Text0(stableStringify0(parsed.value)) : null,
    stdoutPreview: preview0(result.stdout),
    stderrPreview: preview0(result.stderr),
  };
}

function spawnShell0({ root, command }) {
  return new Promise((resolve) => {
    const child = spawn(command, { cwd: root, shell: true, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    child.stdout.on('data', (chunk) => { stdout += chunk.toString('utf8'); });
    child.stderr.on('data', (chunk) => { stderr += chunk.toString('utf8'); });
    child.on('error', (error) => resolve({ exitCode: 127, stdout, stderr: `${stderr}${String(error?.message ?? error)}\n` }));
    child.on('close', (code) => resolve({ exitCode: code ?? 0, stdout, stderr }));
  });
}

async function digestExistingFiles0(root, relativePaths, phase) {
  const digests = [];
  for (const relativePath of relativePaths) {
    const safePath = safeJoin0(root, relativePath);
    if (safePath === null) return reject0('DeterminismAudit.UnsafePath', [phase, relativePath], 'artifact path must stay inside repository root');
    try {
      const info = await stat(safePath);
      if (!info.isFile()) return reject0('DeterminismAudit.ArtifactNotFile', [phase, relativePath], 'artifact path must be a file');
      const bytes = await readFile(safePath);
      digests.push({ path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length });
    } catch (error) {
      return reject0('DeterminismAudit.ArtifactMissing', [phase, relativePath], 'artifact file is missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', phase, digests };
}

function compareRuns0({ firstRun, secondRun, stableBefore, stableAfterFirst, stableAfterSecond, generatedAfterFirst, generatedAfterSecond }) {
  const failures = [];
  compareField0(failures, ['runs', 'exitCode'], firstRun.exitCode, secondRun.exitCode);
  compareField0(failures, ['runs', 'stdoutSha256'], firstRun.stdoutSha256, secondRun.stdoutSha256);
  compareField0(failures, ['runs', 'stderrSha256'], firstRun.stderrSha256, secondRun.stderrSha256);
  compareField0(failures, ['runs', 'parsedJsonCanonicalSha256'], firstRun.parsedJsonCanonicalSha256, secondRun.parsedJsonCanonicalSha256);
  compareField0(failures, ['stableArtifacts', 'before-vs-after-run1'], stableStringify0(stableBefore.digests), stableStringify0(stableAfterFirst.digests));
  compareField0(failures, ['stableArtifacts', 'before-vs-after-run2'], stableStringify0(stableBefore.digests), stableStringify0(stableAfterSecond.digests));
  compareField0(failures, ['generatedArtifacts', 'run1-vs-run2'], stableStringify0(generatedAfterFirst.digests), stableStringify0(generatedAfterSecond.digests));
  if (failures.length !== 0) return reject0('DeterminismAudit.Mismatch', failures[0].path, 'determinism comparison mismatch', { failures });
  return {
    tag: 'accept',
    runComparison: {
      command: firstRun.command,
      stdoutSha256: firstRun.stdoutSha256,
      stderrSha256: firstRun.stderrSha256,
      parsedJsonCanonicalSha256: firstRun.parsedJsonCanonicalSha256,
    },
  };
}

function compareField0(failures, pathArray, left, right) {
  if (left !== right) failures.push({ path: pathArray, left, right });
}

function parseJsonMaybe0(text) {
  try { return { ok: true, value: JSON.parse(text) }; }
  catch { return { ok: false, value: null }; }
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

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('DeterminismAudit.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('DeterminismAudit.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) if (!nonempty0(value[index])) return reject0('DeterminismAudit.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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

function stableStringify0(value) {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map((entry) => stableStringify0(entry)).join(',')}]`;
  return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
}

function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function preview0(text) { return text.length > 2000 ? `${text.slice(0, 2000)}\n...[truncated ${text.length - 2000} bytes]` : text; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), manifestPath: MANIFEST_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false, command: null, generatedArtifactPaths: [] };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--manifest') options.manifestPath = requireValue0(argv, ++index, '--manifest');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--command') options.command = requireValue0(argv, ++index, '--command');
    else if (arg === '--generated-artifact') options.generatedArtifactPaths.push(requireValue0(argv, ++index, '--generated-artifact'));
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
  console.log(`Usage: node scripts/audit-determinism.mjs [options]\n\nOptions:\n  --json                         Emit verdict JSON.\n  --no-write                     Do not write artifacts/determinism-audit/latest-verdict.json.\n  --root <path>                  Repository root. Defaults to cwd.\n  --manifest <path>              Manifest path relative to root.\n  --output <path>                Verdict output path relative to root.\n  --command <command>            Verification command to run twice.\n  --generated-artifact <path>    Generated artifact path to compare. Repeatable.\n`);
}

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad determinism audit CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await AuditDeterminism0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
