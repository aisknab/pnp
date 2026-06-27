#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckTrustBase0';
const VERSION = 0;
const TRUST_BASE_PATH = 'trust-base/TRUST_BASE.json';
const SHA256SUMS_PATH = 'trust-base/SHA256SUMS';
const DEFAULT_OUTPUT_PATH = 'artifacts/trust-base/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-TRUST-BASE-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export const TRUST_BASE_REQUIRED_ASSUMPTION_IDS0 = Object.freeze([
  'Runtime.NodeJS.Semantics',
  'Crypto.SHA256.CollisionResistance',
  'Git.ObjectIntegrity',
  'Semantics.NANDDirectWireWords',
  'Reduction.SATToLockedNANDEncoding',
  'Kernel.PCCCheckerInferenceRules',
  'Complexity.SATInPImpliesPEqualsNP',
]);

const EXPECTED_AUDIT0 = Object.freeze({
  checker: CHECKER,
  script: 'pcc-trust-base0.mjs',
  command: 'node pcc-trust-base0.mjs --json',
  expectedAcceptTag: 'accept',
  sha256Sums: SHA256SUMS_PATH,
});

export async function CheckTrustBase0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const trustBasePath = options.trustBasePath ?? TRUST_BASE_PATH;
  const sha256SumsPath = options.sha256SumsPath ?? SHA256SUMS_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const trustBaseRead = await readTrustBase0({ root, trustBasePath, override: options.trustBaseOverride });
    if (trustBaseRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, trustBaseRead);

    const validation = validateTrustBase0(trustBaseRead.trustBase);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, validation);

    const checksum = await validateChecksumLedger0({
      root,
      trustBasePath,
      trustBaseBytes: trustBaseRead.bytes,
      sha256SumsPath,
      override: options.sha256SumsOverride,
    });
    if (checksum.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, checksum);

    const fileCheck = await validateRepresentedFiles0({ root, trustBase: trustBaseRead.trustBase });
    if (fileCheck.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, fileCheck);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'trust-base-explicit-represented-ready',
      trustBasePath,
      trustBaseSha256: sha256Hex0(trustBaseRead.bytes),
      sha256SumsPath,
      sha256SumsSha256: checksum.sha256SumsSha256,
      trustBaseRepresentedReady: true,
      trustBaseExplicit: true,
      trustBaseEmpty: false,
      assumptionCount: trustBaseRead.trustBase.assumptions.length,
      assumptionIds: TRUST_BASE_REQUIRED_ASSUMPTION_IDS0,
      representedFileCount: fileCheck.representedFileCount,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('TrustBase.UnhandledException', [], 'trust-base checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readTrustBase0({ root, trustBasePath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', trustBase: override, bytes };
  }

  try {
    const bytes = await readFile(path.join(root, trustBasePath));
    return { tag: 'accept', trustBase: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('TrustBase.ReadOrParseFailed', [trustBasePath], 'could not read or parse trust-base JSON', normalizeError0(error));
  }
}

function validateTrustBase0(trustBase) {
  if (!isPlainObject0(trustBase)) return reject0('TrustBase.Shape', [], 'trust base must be an object');
  if (trustBase.kind !== 'PNPTrustBase0') return reject0('TrustBase.Kind', ['kind'], 'trust-base kind mismatch', { expected: 'PNPTrustBase0', actual: trustBase.kind });
  if (trustBase.version !== VERSION) return reject0('TrustBase.Version', ['version'], 'trust-base version mismatch', { expected: VERSION, actual: trustBase.version });
  if (trustBase.coordinate !== EXPECTED_COORDINATE) return reject0('TrustBase.Coordinate', ['coordinate'], 'trust-base coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: trustBase.coordinate });
  if (trustBase.status !== 'trust-base-explicit-ready') return reject0('TrustBase.Status', ['status'], 'trust-base status mismatch');

  const boundary = validateBoundary0(trustBase.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (trustBase.trustBaseRepresentedReady !== true) return reject0('TrustBase.Flag', ['trustBaseRepresentedReady'], 'trustBaseRepresentedReady must be true');
  if (trustBase.trustBaseExplicit !== true) return reject0('TrustBase.Flag', ['trustBaseExplicit'], 'trustBaseExplicit must be true');
  if (trustBase.trustBaseEmpty !== false) return reject0('TrustBase.Flag', ['trustBaseEmpty'], 'trustBaseEmpty must be false');

  if (!Array.isArray(trustBase.assumptions) || trustBase.assumptions.length === 0) return reject0('TrustBase.Assumptions', ['assumptions'], 'trust base must list at least one assumption');
  const ids = trustBase.assumptions.map((entry) => entry?.id);
  if (!sameStringArray0(ids, TRUST_BASE_REQUIRED_ASSUMPTION_IDS0)) {
    return reject0('TrustBase.AssumptionIds', ['assumptions'], 'trust-base assumption ids must stay exact and ordered', {
      expected: TRUST_BASE_REQUIRED_ASSUMPTION_IDS0,
      actual: ids,
    });
  }

  for (let index = 0; index < trustBase.assumptions.length; index += 1) {
    const assumption = trustBase.assumptions[index];
    const pathArray = ['assumptions', index];
    if (!isPlainObject0(assumption)) return reject0('TrustBase.AssumptionShape', pathArray, 'assumption must be an object');
    for (const field of ['id', 'title', 'status', 'description', 'reductionPlan']) {
      if (!isNonEmptyString0(assumption[field])) return reject0('TrustBase.AssumptionField', [...pathArray, field], 'assumption field must be a non-empty string');
    }
    if (assumption.externalAssumption !== true) return reject0('TrustBase.ExternalAssumptionFlag', [...pathArray, 'externalAssumption'], 'each trust-base entry must be marked externalAssumption=true');
    const represented = validateStringArray0(assumption.representedBy, [...pathArray, 'representedBy'], true);
    if (represented.tag === 'reject') return represented;
    const mitigations = validateStringArray0(assumption.currentMitigations, [...pathArray, 'currentMitigations'], true);
    if (mitigations.tag === 'reject') return mitigations;
  }

  if (!isPlainObject0(trustBase.audit)) return reject0('TrustBase.Audit', ['audit'], 'audit field must be an object');
  for (const [key, expected] of Object.entries(EXPECTED_AUDIT0)) {
    if (trustBase.audit[key] !== expected) return reject0('TrustBase.AuditField', ['audit', key], 'trust-base audit field mismatch', { expected, actual: trustBase.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!isPlainObject0(boundary)) return reject0('TrustBase.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('TrustBase.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('TrustBase.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameStringArray0(boundary.activeFinalNodeIds, [])) return reject0('TrustBase.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameStringArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('TrustBase.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function validateChecksumLedger0({ root, trustBasePath, trustBaseBytes, sha256SumsPath, override }) {
  let text;
  let bytes;
  if (override !== undefined) {
    text = override;
    bytes = Buffer.from(text, 'utf8');
  } else {
    try {
      bytes = await readFile(path.join(root, sha256SumsPath));
      text = bytes.toString('utf8');
    } catch (error) {
      return reject0('TrustBase.ChecksumReadFailed', [sha256SumsPath], 'could not read trust-base SHA256SUMS', normalizeError0(error));
    }
  }

  const expectedHash = sha256Hex0(trustBaseBytes);
  const entries = parseSha256Sums0(text);
  if (entries.tag === 'reject') return entries;
  const trustBaseFileName = path.basename(trustBasePath);
  const actual = entries.map.get(trustBaseFileName);
  if (actual !== expectedHash) {
    return reject0('TrustBase.ChecksumMismatch', [sha256SumsPath, trustBaseFileName], 'trust-base SHA256SUMS does not match TRUST_BASE.json', {
      expectedHash,
      actualHash: actual ?? null,
    });
  }
  return { tag: 'accept', sha256SumsSha256: sha256Hex0(bytes) };
}

function parseSha256Sums0(text) {
  const map = new Map();
  const lines = text.split(/\r?\n/u).filter((line) => line.trim().length !== 0);
  if (lines.length === 0) return reject0('TrustBase.EmptyChecksumLedger', [SHA256SUMS_PATH], 'trust-base SHA256SUMS must not be empty');
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const match = line.match(/^([a-f0-9]{64})\s+(.+)$/u);
    if (!match) return reject0('TrustBase.BadChecksumLine', [SHA256SUMS_PATH, index + 1], 'bad SHA256SUMS line', { line });
    const [, hash, fileName] = match;
    if (fileName.includes('/') || fileName.includes('\\') || fileName.startsWith('.')) return reject0('TrustBase.BadChecksumPath', [SHA256SUMS_PATH, index + 1], 'checksum path must be a local file name', { fileName });
    map.set(fileName, hash);
  }
  return { tag: 'accept', map };
}

async function validateRepresentedFiles0({ root, trustBase }) {
  const paths = [...new Set(trustBase.assumptions.flatMap((entry) => entry.representedBy))].sort();
  for (const relativePath of paths) {
    const absolutePath = safeJoin0(root, relativePath);
    if (absolutePath === null) return reject0('TrustBase.RepresentedPathUnsafe', [relativePath], 'representedBy path must stay inside repository root');
    try {
      const info = await stat(absolutePath);
      if (!info.isFile()) return reject0('TrustBase.RepresentedPathNotFile', [relativePath], 'representedBy path must be a file');
    } catch (error) {
      return reject0('TrustBase.RepresentedPathMissing', [relativePath], 'representedBy file is missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', representedFileCount: paths.length };
}

function validateStringArray0(value, pathArray, nonEmpty = false) {
  if (!Array.isArray(value)) return reject0('TrustBase.StringArray', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('TrustBase.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!isNonEmptyString0(value[index])) return reject0('TrustBase.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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
  const options = { root: process.cwd(), trustBasePath: TRUST_BASE_PATH, sha256SumsPath: SHA256SUMS_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') {
      index += 1;
      if (index >= argv.length) throw new Error('--root requires a value');
      options.root = argv[index];
    } else if (arg === '--trust-base') {
      index += 1;
      if (index >= argv.length) throw new Error('--trust-base requires a value');
      options.trustBasePath = argv[index];
    } else if (arg === '--sha256sums') {
      index += 1;
      if (index >= argv.length) throw new Error('--sha256sums requires a value');
      options.sha256SumsPath = argv[index];
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
  console.log(`Usage: node pcc-trust-base0.mjs [options]\n\nOptions:\n  --json                  Emit verdict JSON.\n  --no-write              Do not write artifacts/trust-base/latest-verdict.json.\n  --root <path>           Repository root. Defaults to cwd.\n  --trust-base <path>     Trust-base JSON path relative to root.\n  --sha256sums <path>     SHA256SUMS path relative to root.\n  --output <path>         Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad trust-base CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await CheckTrustBase0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0();
}
