#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { lstat, mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const CHECKER = 'AuditCheckerTotality0';
const VERSION = 0;
const MANIFEST_PATH = 'checker-totality/CHECKER_TOTALITY_AUDIT.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/checker-totality/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-CHECKER-TOTALITY-AUDIT-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_TRUST_BASE_COORDINATE = 'PNP-TRUST-BASE-2026-06-27-01';
const EXPECTED_SHRINK_PLAN_COORDINATE = 'PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01';

const SKIP_DIRS = new Set([
  '.git',
  '.github',
  'node_modules',
  'artifacts',
  'proof-artifacts',
  'successor-report-seals',
]);

export async function AuditCheckerTotality0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readManifest0({ root, manifestPath, override: options.manifestOverride });
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);

    const manifestValidation = validateManifest0(manifestRead.manifest);
    if (manifestValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestValidation);

    const inventory = await scanCheckerExportInventory0(root);
    if (inventory.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventory);

    const fuzz = await runRequiredCheckerFuzz0({
      root,
      manifest: manifestRead.manifest,
      inventory: inventory.exports,
    });
    if (fuzz.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, fuzz);

    const auditedIds = manifestRead.manifest.requiredAuditedCheckers.map((entry) => entry.id).sort();
    const discoveredIds = inventory.exports.map((entry) => entry.exportName).sort();
    const unauditedIds = discoveredIds.filter((id) => !auditedIds.includes(id));

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'checker-totality-seed-audit-accepted',
      manifestPath,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      checkerTotalitySeedReady: true,
      fullCheckerTotalityProved: false,
      discoveredCheckerCount: inventory.exports.length,
      auditedCheckerCount: manifestRead.manifest.requiredAuditedCheckers.length,
      fuzzCaseCount: fuzz.caseCount,
      unauditedCheckerCount: unauditedIds.length,
      unauditedCheckerIdsPreview: unauditedIds.slice(0, 50),
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('CheckerTotality.UnhandledException', [], 'checker totality audit threw unexpectedly', normalizeError0(error)));
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
    return reject0('CheckerTotality.ManifestReadOrParseFailed', [manifestPath], 'could not read or parse checker-totality manifest', normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!isPlainObject0(manifest)) return reject0('CheckerTotality.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPCheckerTotalityAudit0') return reject0('CheckerTotality.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('CheckerTotality.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('CheckerTotality.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch');
  if (manifest.status !== 'checker-totality-seed-ready') return reject0('CheckerTotality.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.checkerTotalitySeedReady !== true) return reject0('CheckerTotality.SeedFlag', ['checkerTotalitySeedReady'], 'checkerTotalitySeedReady must be true');
  if (manifest.fullCheckerTotalityProved !== false) return reject0('CheckerTotality.FullProofFlag', ['fullCheckerTotalityProved'], 'initial checker-totality audit must not claim full checker totality');
  if (manifest.exportInventoryRequired !== true) return reject0('CheckerTotality.InventoryFlag', ['exportInventoryRequired'], 'export inventory must be required');

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!Array.isArray(manifest.requiredAuditedCheckers) || manifest.requiredAuditedCheckers.length === 0) return reject0('CheckerTotality.RequiredCheckers', ['requiredAuditedCheckers'], 'at least one audited checker is required');
  const ids = new Set();
  for (let index = 0; index < manifest.requiredAuditedCheckers.length; index += 1) {
    const entry = manifest.requiredAuditedCheckers[index];
    const entryPath = ['requiredAuditedCheckers', index];
    if (!isPlainObject0(entry)) return reject0('CheckerTotality.RequiredCheckerShape', entryPath, 'required checker entry must be an object');
    for (const field of ['id', 'file', 'exportName', 'category']) {
      if (!isNonEmptyString0(entry[field])) return reject0('CheckerTotality.RequiredCheckerField', [...entryPath, field], 'required checker field must be a non-empty string');
    }
    if (entry.id !== entry.exportName) return reject0('CheckerTotality.RequiredCheckerIdMismatch', entryPath, 'required checker id must equal exportName');
    if (ids.has(entry.id)) return reject0('CheckerTotality.RequiredCheckerDuplicate', [...entryPath, 'id'], 'required checker ids must be unique', { id: entry.id });
    ids.add(entry.id);
    if (!entry.file.endsWith('.mjs') || entry.file.startsWith('.') || path.isAbsolute(entry.file)) return reject0('CheckerTotality.RequiredCheckerFile', [...entryPath, 'file'], 'required checker file must be a repository-relative .mjs file');
    if (!Array.isArray(entry.cases) || entry.cases.length === 0) return reject0('CheckerTotality.RequiredCheckerCases', [...entryPath, 'cases'], 'required checker must have fuzz cases');
    for (let caseIndex = 0; caseIndex < entry.cases.length; caseIndex += 1) {
      const fuzzCase = entry.cases[caseIndex];
      if (!isPlainObject0(fuzzCase)) return reject0('CheckerTotality.FuzzCaseShape', [...entryPath, 'cases', caseIndex], 'fuzz case must be an object');
      if (!isNonEmptyString0(fuzzCase.id)) return reject0('CheckerTotality.FuzzCaseId', [...entryPath, 'cases', caseIndex, 'id'], 'fuzz case id must be non-empty');
      if (!['accept', 'reject'].includes(fuzzCase.expectedTag)) return reject0('CheckerTotality.FuzzCaseExpectedTag', [...entryPath, 'cases', caseIndex, 'expectedTag'], 'fuzz case expectedTag must be accept or reject');
    }
  }

  if (!isPlainObject0(manifest.audit)) return reject0('CheckerTotality.AuditShape', ['audit'], 'audit field must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'scripts/audit-checker-totality.mjs',
    command: 'npm run checker:totality',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('CheckerTotality.AuditField', ['audit', key], 'manifest audit field mismatch', { expected, actual: manifest.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!isPlainObject0(boundary)) return reject0('CheckerTotality.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('CheckerTotality.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('CheckerTotality.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameStringArray0(boundary.activeFinalNodeIds, [])) return reject0('CheckerTotality.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final node ids must remain empty');
  if (!sameStringArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('CheckerTotality.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function scanCheckerExportInventory0(root) {
  const files = [];
  const walkResult = await walkMjsFiles0(root, '.', files);
  if (walkResult?.tag === 'reject') return walkResult;

  const exports = [];
  const pattern = /export\s+(?:async\s+)?function\s+(Check[A-Za-z0-9_]*0)\s*\(/gu;
  for (const relativePath of files.sort()) {
    let text;
    try {
      text = await readFile(path.join(root, relativePath), 'utf8');
    } catch (error) {
      return reject0('CheckerTotality.SourceReadFailed', [relativePath], 'could not read source file while scanning checker exports', normalizeError0(error));
    }
    let match;
    while ((match = pattern.exec(text)) !== null) {
      exports.push({ file: normalizePath0(relativePath), exportName: match[1], offset: match.index });
    }
  }

  if (exports.length === 0) return reject0('CheckerTotality.NoCheckerExports', [], 'no exported Check*0 functions found');

  const duplicates = findDuplicateExports0(exports);
  if (duplicates.length !== 0) return reject0('CheckerTotality.DuplicateExports', [], 'duplicate Check*0 export names found', { duplicates });

  return { tag: 'accept', exports };
}

async function walkMjsFiles0(root, relativeDir, files) {
  const absoluteDir = path.join(root, relativeDir);
  let entries;
  try {
    entries = await readdir(absoluteDir, { withFileTypes: true });
  } catch (error) {
    return reject0('CheckerTotality.DirectoryReadFailed', [relativeDir], 'could not read repository directory while scanning checker exports', normalizeError0(error));
  }

  for (const entry of entries.sort((left, right) => left.name.localeCompare(right.name))) {
    const childRelative = relativeDir === '.' ? entry.name : `${relativeDir}/${entry.name}`;
    if (entry.isDirectory()) {
      if (SKIP_DIRS.has(entry.name)) continue;
      const result = await walkMjsFiles0(root, childRelative, files);
      if (result?.tag === 'reject') return result;
    } else if (entry.isFile() && entry.name.endsWith('.mjs')) {
      files.push(childRelative);
    } else if (entry.isSymbolicLink()) {
      return reject0('CheckerTotality.SymlinkForbidden', [childRelative], 'checker-totality export scan rejects symlinks');
    }
  }
  return { tag: 'accept' };
}

async function runRequiredCheckerFuzz0({ root, manifest, inventory }) {
  const inventoryMap = new Map(inventory.map((entry) => [`${entry.file}#${entry.exportName}`, entry]));
  const caseResults = [];

  for (const checkerSpec of manifest.requiredAuditedCheckers) {
    const key = `${checkerSpec.file}#${checkerSpec.exportName}`;
    if (!inventoryMap.has(key)) {
      return reject0('CheckerTotality.RequiredCheckerNotDiscovered', [checkerSpec.file, checkerSpec.exportName], 'required audited checker was not discovered in export inventory');
    }

    const moduleResult = await importModule0(root, checkerSpec.file);
    if (moduleResult.tag === 'reject') return moduleResult;
    const fn = moduleResult.module[checkerSpec.exportName];
    if (typeof fn !== 'function') return reject0('CheckerTotality.RequiredCheckerNotFunction', [checkerSpec.file, checkerSpec.exportName], 'required audited checker export is not a function');

    for (const fuzzCase of checkerSpec.cases) {
      const argsResult = await buildFuzzArgs0({ root, module: moduleResult.module, checkerSpec, fuzzCase });
      if (argsResult.tag === 'reject') return argsResult;
      const callResult = await callTotalChecker0({ fn, checkerSpec, fuzzCase, args: argsResult.args });
      if (callResult.tag === 'reject') return callResult;
      caseResults.push(callResult.result);
    }
  }

  return { tag: 'accept', caseCount: caseResults.length, caseResults };
}

async function importModule0(root, relativePath) {
  try {
    const absolutePath = path.join(root, relativePath);
    return { tag: 'accept', module: await import(pathToFileURL(absolutePath).href) };
  } catch (error) {
    return reject0('CheckerTotality.ModuleImportFailed', [relativePath], 'could not import audited checker module', normalizeError0(error));
  }
}

async function buildFuzzArgs0({ root, module, checkerSpec, fuzzCase }) {
  try {
    switch (fuzzCase.id) {
      case 'minimal.valid-default':
        return { tag: 'accept', args: [] };
      case 'minimal.null-input':
        return { tag: 'accept', args: [null] };
      case 'minimal.caller-readiness':
        return { tag: 'accept', args: [{ ...module.makeMinimalKernelInput0(), publicTheoremEmissionAllowed: true }] };

      case 'successor.valid-input':
        return { tag: 'accept', args: [module.makeSuccessorPublicReviewReportSealInput0()] };
      case 'successor.null-input':
        return { tag: 'accept', args: [null] };
      case 'successor.caller-readiness':
        return { tag: 'accept', args: [{ ...module.makeSuccessorPublicReviewReportSealInput0(), publicTheoremEmissionAllowed: true }] };

      case 'trustbase.valid-default':
        return { tag: 'accept', args: [{ writeOutput: false }] };
      case 'trustbase.bad-json-shape': {
        const trustBaseOverride = { kind: 'WrongTrustBase0' };
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: `${hashOverride0(trustBaseOverride)}  TRUST_BASE.json\n`, writeOutput: false }] };
      }
      case 'trustbase.boundary-activation': {
        const trustBaseOverride = await readJsonFile0(root, 'trust-base/TRUST_BASE.json');
        trustBaseOverride.claimBoundary.publicTheoremEmissionAllowed = true;
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: `${hashOverride0(trustBaseOverride)}  TRUST_BASE.json\n`, writeOutput: false }] };
      }

      case 'shrink.valid-default':
        return { tag: 'accept', args: [{ writeOutput: false }] };
      case 'shrink.bad-plan-shape':
        return { tag: 'accept', args: [{ planOverride: { kind: 'WrongShrinkPlan0' }, trustBaseOverride: { kind: 'WrongTrustBase0' }, writeOutput: false }] };
      case 'shrink.premature-complete': {
        const planOverride = await readJsonFile0(root, 'trust-base/SHRINK_PLAN.json');
        const trustBaseOverride = await readJsonFile0(root, 'trust-base/TRUST_BASE.json');
        planOverride.tasks[0].status = 'complete';
        return { tag: 'accept', args: [{ planOverride, trustBaseOverride, writeOutput: false }] };
      }

      case 'publicsurface.valid-default':
        return { tag: 'accept', args: [] };
      case 'publicsurface.bad-package-json':
        return { tag: 'accept', args: [{ rootDir: root, publicEntryOverride: null, packageJsonOverride: {} }] };

      default:
        return reject0('CheckerTotality.UnknownFuzzCase', [checkerSpec.id, fuzzCase.id], 'unknown checker-totality fuzz case id');
    }
  } catch (error) {
    return reject0('CheckerTotality.FuzzArgBuildFailed', [checkerSpec.id, fuzzCase.id], 'could not build checker-totality fuzz arguments', normalizeError0(error));
  }
}

async function callTotalChecker0({ fn, checkerSpec, fuzzCase, args }) {
  let record;
  try {
    record = await fn(...args);
  } catch (error) {
    return reject0('CheckerTotality.CheckerThrew', [checkerSpec.id, fuzzCase.id], 'audited checker threw instead of returning accept/reject', normalizeError0(error));
  }

  if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
    return reject0('CheckerTotality.NonTotalReturn', [checkerSpec.id, fuzzCase.id], 'audited checker did not return an accept/reject record', { actual: previewValue0(record) });
  }
  if (record.tag !== fuzzCase.expectedTag) {
    return reject0('CheckerTotality.UnexpectedCaseTag', [checkerSpec.id, fuzzCase.id], 'audited checker fuzz case returned an unexpected tag', { expectedTag: fuzzCase.expectedTag, actualTag: record.tag, coord: record.coord ?? record.Coord ?? null });
  }

  return {
    tag: 'accept',
    result: {
      checkerId: checkerSpec.id,
      caseId: fuzzCase.id,
      tag: record.tag,
      coord: record.coord ?? record.Coord ?? null,
      digest: record.digest ?? record.Digest ?? null,
    },
  };
}

async function readJsonFile0(root, relativePath) {
  const text = await readFile(path.join(root, relativePath), 'utf8');
  return JSON.parse(text);
}

function findDuplicateExports0(exports) {
  const byName = new Map();
  for (const entry of exports) {
    const list = byName.get(entry.exportName) ?? [];
    list.push(entry.file);
    byName.set(entry.exportName, list);
  }
  return [...byName.entries()].filter(([, files]) => files.length > 1).map(([exportName, files]) => ({ exportName, files }));
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

function hashOverride0(value) {
  return sha256Hex0(Buffer.from(JSON.stringify(value, null, 2) + '\n', 'utf8'));
}

function sha256Hex0(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function normalizePath0(relativePath) {
  return relativePath.replace(/\\/gu, '/').replace(/^\.\//u, '');
}

function previewValue0(value) {
  try {
    return JSON.parse(JSON.stringify(value));
  } catch {
    return String(value);
  }
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}

function sameStringArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
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
  const options = { root: process.cwd(), manifestPath: MANIFEST_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') {
      index += 1;
      if (index >= argv.length) throw new Error('--root requires a value');
      options.root = argv[index];
    } else if (arg === '--manifest') {
      index += 1;
      if (index >= argv.length) throw new Error('--manifest requires a value');
      options.manifestPath = argv[index];
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
  console.log(`Usage: node scripts/audit-checker-totality.mjs [options]\n\nOptions:\n  --json              Emit verdict JSON.\n  --no-write          Do not write artifacts/checker-totality/latest-verdict.json.\n  --root <path>       Repository root. Defaults to cwd.\n  --manifest <path>   Checker-totality manifest path relative to root.\n  --output <path>     Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad checker-totality CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await AuditCheckerTotality0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0();
}
