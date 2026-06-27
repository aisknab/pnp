#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const CHECKER = 'AuditCheckerTotality0';
const VERSION = 0;
const MANIFEST_PATH = 'checker-totality/CHECKER_TOTALITY_AUDIT.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/checker-totality/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-CHECKER-TOTALITY-AUDIT-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const SKIP_DIRS = new Set(['.git', '.github', 'node_modules', 'artifacts', 'proof-artifacts', 'successor-report-seals']);

export async function AuditCheckerTotality0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readJson0(root, manifestPath, options.manifestOverride);
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);

    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestCheck);

    const inventory = await scanCheckerExports0(root);
    if (inventory.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, inventory);

    const fuzz = await fuzzAuditedCheckers0(root, manifestRead.value, inventory.exports);
    if (fuzz.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, fuzz);

    const auditedIds = new Set(manifestRead.value.requiredAuditedCheckers.map((entry) => entry.id));
    const discoveredIds = inventory.exports.map((entry) => entry.exportName).sort();
    const uniqueDiscoveredIds = [...new Set(discoveredIds)].sort();
    const unauditedCheckerIds = uniqueDiscoveredIds.filter((id) => !auditedIds.has(id));

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
      uniqueDiscoveredCheckerCount: uniqueDiscoveredIds.length,
      duplicateExportNameCount: inventory.duplicateExportNames.length,
      auditedCheckerCount: manifestRead.value.requiredAuditedCheckers.length,
      fuzzCaseCount: fuzz.caseCount,
      unauditedCheckerCount: unauditedCheckerIds.length,
      unauditedCheckerIdsPreview: unauditedCheckerIds.slice(0, 50),
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('CheckerTotality.UnhandledException', [], 'checker-totality audit threw unexpectedly', normalizeError0(error)));
  }
}

async function readJson0(root, relativePath, override) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, relativePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('CheckerTotality.JsonReadOrParseFailed', [relativePath], 'could not read or parse checker-totality JSON', normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('CheckerTotality.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPCheckerTotalityAudit0') return reject0('CheckerTotality.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('CheckerTotality.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('CheckerTotality.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch');
  if (manifest.status !== 'checker-totality-seed-ready') return reject0('CheckerTotality.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.checkerTotalitySeedReady !== true) return reject0('CheckerTotality.SeedFlag', ['checkerTotalitySeedReady'], 'checkerTotalitySeedReady must be true');
  if (manifest.fullCheckerTotalityProved !== false) return reject0('CheckerTotality.FullProofFlag', ['fullCheckerTotalityProved'], 'initial audit cannot claim full checker totality');
  if (manifest.exportInventoryRequired !== true) return reject0('CheckerTotality.InventoryFlag', ['exportInventoryRequired'], 'export inventory must be required');
  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;
  if (!Array.isArray(manifest.requiredAuditedCheckers) || manifest.requiredAuditedCheckers.length === 0) return reject0('CheckerTotality.RequiredCheckers', ['requiredAuditedCheckers'], 'required audited checker list must be non-empty');

  const ids = new Set();
  for (let index = 0; index < manifest.requiredAuditedCheckers.length; index += 1) {
    const entry = manifest.requiredAuditedCheckers[index];
    const entryPath = ['requiredAuditedCheckers', index];
    if (!plain0(entry)) return reject0('CheckerTotality.RequiredCheckerShape', entryPath, 'required checker entry must be an object');
    for (const field of ['id', 'file', 'exportName', 'category']) {
      if (!nonempty0(entry[field])) return reject0('CheckerTotality.RequiredCheckerField', [...entryPath, field], 'required checker field must be a non-empty string');
    }
    if (entry.id !== entry.exportName) return reject0('CheckerTotality.RequiredCheckerIdMismatch', entryPath, 'checker id must equal exportName');
    if (ids.has(entry.id)) return reject0('CheckerTotality.RequiredCheckerDuplicate', [...entryPath, 'id'], 'required checker ids must be unique');
    ids.add(entry.id);
    if (!entry.file.endsWith('.mjs') || path.isAbsolute(entry.file) || entry.file.startsWith('.')) return reject0('CheckerTotality.RequiredCheckerFile', [...entryPath, 'file'], 'required checker file must be repository-relative .mjs');
    if (!Array.isArray(entry.cases) || entry.cases.length === 0) return reject0('CheckerTotality.RequiredCheckerCases', [...entryPath, 'cases'], 'required checker must have fuzz cases');
    for (let caseIndex = 0; caseIndex < entry.cases.length; caseIndex += 1) {
      const fuzzCase = entry.cases[caseIndex];
      if (!plain0(fuzzCase) || !nonempty0(fuzzCase.id) || !['accept', 'reject'].includes(fuzzCase.expectedTag)) {
        return reject0('CheckerTotality.FuzzCaseShape', [...entryPath, 'cases', caseIndex], 'fuzz case must have id and expectedTag accept|reject');
      }
    }
  }

  const expectedAudit = {
    checker: CHECKER,
    script: 'scripts/audit-checker-totality.mjs',
    command: 'npm run checker:totality',
    expectedAcceptTag: 'accept',
  };
  if (!plain0(manifest.audit)) return reject0('CheckerTotality.AuditShape', ['audit'], 'manifest audit field must be an object');
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('CheckerTotality.AuditField', ['audit', key], 'manifest audit field mismatch', { expected, actual: manifest.audit[key] });
  }
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('CheckerTotality.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('CheckerTotality.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('CheckerTotality.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('CheckerTotality.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final node ids must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('CheckerTotality.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

async function scanCheckerExports0(root) {
  const files = [];
  const walk = await walk0(root, '.', files);
  if (walk?.tag === 'reject') return walk;
  const pattern = /export\s+(?:async\s+)?function\s+(Check[A-Za-z0-9_]*0)\s*\(/gu;
  const exports = [];
  for (const relativePath of files.sort()) {
    let text;
    try {
      text = await readFile(path.join(root, relativePath), 'utf8');
    } catch (error) {
      return reject0('CheckerTotality.SourceReadFailed', [relativePath], 'could not read source file while scanning exports', normalizeError0(error));
    }
    pattern.lastIndex = 0;
    let match;
    while ((match = pattern.exec(text)) !== null) exports.push({ file: normalizePath0(relativePath), exportName: match[1], offset: match.index });
  }
  if (exports.length === 0) return reject0('CheckerTotality.NoCheckerExports', [], 'no exported Check*0 functions found');
  return { tag: 'accept', exports, duplicateExportNames: duplicateExportNames0(exports) };
}

async function walk0(root, relativeDir, files) {
  let entries;
  try {
    entries = await readdir(path.join(root, relativeDir), { withFileTypes: true });
  } catch (error) {
    return reject0('CheckerTotality.DirectoryReadFailed', [relativeDir], 'could not read repository directory', normalizeError0(error));
  }
  for (const entry of entries.sort((left, right) => left.name.localeCompare(right.name))) {
    const child = relativeDir === '.' ? entry.name : `${relativeDir}/${entry.name}`;
    if (entry.isDirectory()) {
      if (!SKIP_DIRS.has(entry.name)) {
        const nested = await walk0(root, child, files);
        if (nested?.tag === 'reject') return nested;
      }
    } else if (entry.isFile() && entry.name.endsWith('.mjs')) {
      files.push(child);
    } else if (entry.isSymbolicLink()) {
      return reject0('CheckerTotality.SymlinkForbidden', [child], 'checker-totality scan rejects symlinks');
    }
  }
  return { tag: 'accept' };
}

async function fuzzAuditedCheckers0(root, manifest, inventory) {
  const inventoryKeys = new Set(inventory.map((entry) => `${entry.file}#${entry.exportName}`));
  let caseCount = 0;
  for (const checkerSpec of manifest.requiredAuditedCheckers) {
    const key = `${checkerSpec.file}#${checkerSpec.exportName}`;
    if (!inventoryKeys.has(key)) return reject0('CheckerTotality.RequiredCheckerNotDiscovered', [checkerSpec.file, checkerSpec.exportName], 'required checker export was not found in inventory');
    const moduleLoad = await importAuditedModule0(root, checkerSpec.file);
    if (moduleLoad.tag === 'reject') return moduleLoad;
    const fn = moduleLoad.module[checkerSpec.exportName];
    if (typeof fn !== 'function') return reject0('CheckerTotality.RequiredCheckerNotFunction', [checkerSpec.file, checkerSpec.exportName], 'required checker export is not a function');
    for (const fuzzCase of checkerSpec.cases) {
      const args = await buildArgs0(root, moduleLoad.module, checkerSpec, fuzzCase);
      if (args.tag === 'reject') return args;
      const result = await callChecker0(fn, checkerSpec, fuzzCase, args.args);
      if (result.tag === 'reject') return result;
      caseCount += 1;
    }
  }
  return { tag: 'accept', caseCount };
}

async function importAuditedModule0(root, relativePath) {
  try {
    return { tag: 'accept', module: await import(pathToFileURL(path.join(root, relativePath)).href) };
  } catch (error) {
    return reject0('CheckerTotality.ModuleImportFailed', [relativePath], 'could not import audited checker module', normalizeError0(error));
  }
}

async function buildArgs0(root, mod, checkerSpec, fuzzCase) {
  try {
    switch (fuzzCase.id) {
      case 'minimal.valid-default': return { tag: 'accept', args: [] };
      case 'minimal.null-input': return { tag: 'accept', args: [null] };
      case 'minimal.caller-readiness': return { tag: 'accept', args: [{ ...mod.makeMinimalKernelInput0(), publicTheoremEmissionAllowed: true }] };
      case 'successor.valid-input': return { tag: 'accept', args: [mod.makeSuccessorPublicReviewReportSealInput0()] };
      case 'successor.null-input': return { tag: 'accept', args: [null] };
      case 'successor.caller-readiness': return { tag: 'accept', args: [{ ...mod.makeSuccessorPublicReviewReportSealInput0(), publicTheoremEmissionAllowed: true }] };
      case 'trustbase.valid-default': return { tag: 'accept', args: [{ writeOutput: false }] };
      case 'trustbase.bad-json-shape': {
        const trustBaseOverride = { kind: 'WrongTrustBase0' };
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: `${hashOverride0(trustBaseOverride)}  TRUST_BASE.json\n`, writeOutput: false }] };
      }
      case 'trustbase.boundary-activation': {
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        trustBaseOverride.claimBoundary.publicTheoremEmissionAllowed = true;
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: `${hashOverride0(trustBaseOverride)}  TRUST_BASE.json\n`, writeOutput: false }] };
      }
      case 'shrink.valid-default': return { tag: 'accept', args: [{ writeOutput: false }] };
      case 'shrink.bad-plan-shape': return { tag: 'accept', args: [{ planOverride: { kind: 'WrongShrinkPlan0' }, trustBaseOverride: { kind: 'WrongTrustBase0' }, writeOutput: false }] };
      case 'shrink.premature-complete': {
        const planOverride = await readRepoJson0(root, 'trust-base/SHRINK_PLAN.json');
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        planOverride.tasks[0].status = 'complete';
        return { tag: 'accept', args: [{ planOverride, trustBaseOverride, writeOutput: false }] };
      }
      case 'publicsurface.valid-default': return { tag: 'accept', args: [] };
      case 'publicsurface.bad-package-json': return { tag: 'accept', args: [{ rootDir: root, publicEntryOverride: null, packageJsonOverride: {} }] };
      default: return reject0('CheckerTotality.UnknownFuzzCase', [checkerSpec.id, fuzzCase.id], 'unknown fuzz case id');
    }
  } catch (error) {
    return reject0('CheckerTotality.FuzzArgBuildFailed', [checkerSpec.id, fuzzCase.id], 'could not build fuzz arguments', normalizeError0(error));
  }
}

async function callChecker0(fn, checkerSpec, fuzzCase, args) {
  let record;
  try {
    record = await fn(...args);
  } catch (error) {
    return reject0('CheckerTotality.CheckerThrew', [checkerSpec.id, fuzzCase.id], 'audited checker threw instead of returning accept/reject', normalizeError0(error));
  }
  if (!plain0(record) || !['accept', 'reject'].includes(record.tag)) return reject0('CheckerTotality.NonTotalReturn', [checkerSpec.id, fuzzCase.id], 'audited checker did not return an accept/reject record', { actual: String(record) });
  if (record.tag !== fuzzCase.expectedTag) return reject0('CheckerTotality.UnexpectedCaseTag', [checkerSpec.id, fuzzCase.id], 'audited checker fuzz case returned an unexpected tag', { expectedTag: fuzzCase.expectedTag, actualTag: record.tag, coord: record.coord ?? record.Coord ?? null });
  return { tag: 'accept' };
}

async function readRepoJson0(root, relativePath) {
  return JSON.parse(await readFile(path.join(root, relativePath), 'utf8'));
}

function duplicateExportNames0(exports) {
  const map = new Map();
  for (const entry of exports) map.set(entry.exportName, [...(map.get(entry.exportName) ?? []), entry.file]);
  return [...map.entries()].filter(([, files]) => files.length > 1).map(([exportName, files]) => ({ exportName, files }));
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

function hashOverride0(value) { return sha256Hex0(Buffer.from(JSON.stringify(value, null, 2) + '\n', 'utf8')); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function normalizePath0(relativePath) { return relativePath.replace(/\\/gu, '/').replace(/^\.\//u, ''); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), manifestPath: MANIFEST_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--manifest') options.manifestPath = requireValue0(argv, ++index, '--manifest');
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

if (import.meta.url === `file://${process.argv[1]}`) main0();
