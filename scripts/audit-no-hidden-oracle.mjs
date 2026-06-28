#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'AuditNoHiddenOracle0';
const VERSION = 0;
const MANIFEST_PATH = 'oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/no-hidden-oracle/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_CHECKS = [
  'manifest boundary remains non-activating',
  'forbidden executable patterns are exact and versioned',
  'repository scan is deterministic over configured file extensions',
  'executable forbidden hits must be explicitly whitelisted by path or line context',
  'documentation/formal references are counted but do not authorize executable calls',
  'generated and durable artifact directories are excluded from source-surface scanning',
  'audit rejects injected executable SAT solver or NP-oracle calls',
  'public theorem emission remains disabled',
];

export async function AuditNoHiddenOracle0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readManifest0({ root, manifestPath, override: options.manifestOverride });
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);

    const manifestCheck = validateManifest0(manifestRead.manifest);
    if (manifestCheck.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestCheck);

    const scan = await scanRepository0({
      root,
      manifest: manifestRead.manifest,
      extraVirtualFiles: options.extraVirtualFiles ?? [],
    });
    if (scan.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, scan);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'no-hidden-oracle-seed-audit-accepted',
      manifestPath,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      noHiddenOracleAuditReady: true,
      fullNoHiddenOracleProved: false,
      publicTheoremEmissionAllowedByAudit: false,
      scannedFileCount: scan.scannedFileCount,
      executableFileCount: scan.executableFileCount,
      documentationReferenceCount: scan.documentationReferenceCount,
      allowedExecutableReferenceCount: scan.allowedExecutableReferenceCount,
      forbiddenExecutableHitCount: 0,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('NoHiddenOracle.UnhandledException', [], 'no-hidden-oracle audit threw unexpectedly', normalizeError0(error)));
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
    return reject0('NoHiddenOracle.ManifestReadOrParseFailed', [manifestPath], 'could not read or parse no-hidden-oracle manifest', normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('NoHiddenOracle.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPNoHiddenOracleAudit0') return reject0('NoHiddenOracle.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('NoHiddenOracle.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('NoHiddenOracle.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: manifest.coordinate });
  if (manifest.status !== 'no-hidden-oracle-seed-ready') return reject0('NoHiddenOracle.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.noHiddenOracleAuditReady !== true) return reject0('NoHiddenOracle.ReadyFlag', ['noHiddenOracleAuditReady'], 'noHiddenOracleAuditReady must be true');
  if (manifest.fullNoHiddenOracleProved !== false) return reject0('NoHiddenOracle.FullProofFlag', ['fullNoHiddenOracleProved'], 'seed audit cannot claim full no-hidden-oracle proof');
  if (manifest.publicTheoremEmissionAllowedByAudit !== false) return reject0('NoHiddenOracle.PublicEmissionByAuditFlag', ['publicTheoremEmissionAllowedByAudit'], 'audit cannot allow public theorem emission');

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(manifest.scan)) return reject0('NoHiddenOracle.ScanShape', ['scan'], 'scan must be an object');
  for (const field of ['extensions', 'skippedPathPrefixes', 'executableExtensions', 'documentationPathPrefixes']) {
    const check = validateStringArray0(manifest.scan[field], ['scan', field], true);
    if (check.tag === 'reject') return check;
  }

  if (!Array.isArray(manifest.forbiddenExecutablePatterns) || manifest.forbiddenExecutablePatterns.length === 0) return reject0('NoHiddenOracle.PatternsShape', ['forbiddenExecutablePatterns'], 'forbiddenExecutablePatterns must be non-empty');
  const patternIds = new Set();
  for (let index = 0; index < manifest.forbiddenExecutablePatterns.length; index += 1) {
    const entry = manifest.forbiddenExecutablePatterns[index];
    const entryPath = ['forbiddenExecutablePatterns', index];
    if (!plain0(entry)) return reject0('NoHiddenOracle.PatternShape', entryPath, 'forbidden pattern entry must be an object');
    if (!nonempty0(entry.id) || !nonempty0(entry.regex)) return reject0('NoHiddenOracle.PatternField', entryPath, 'forbidden pattern id and regex must be non-empty strings');
    if (patternIds.has(entry.id)) return reject0('NoHiddenOracle.PatternDuplicate', [...entryPath, 'id'], 'forbidden pattern ids must be unique', { id: entry.id });
    patternIds.add(entry.id);
    try { new RegExp(entry.regex, 'iu'); } catch (error) { return reject0('NoHiddenOracle.PatternRegexInvalid', [...entryPath, 'regex'], 'forbidden pattern regex must compile', normalizeError0(error)); }
  }

  for (const field of ['allowedExecutablePathPrefixes', 'allowedExecutableFiles', 'allowedExecutableLineRegexes', 'checks']) {
    const check = validateStringArray0(manifest[field], [field], true);
    if (check.tag === 'reject') return check;
  }
  if (!sameArray0(manifest.checks, EXPECTED_CHECKS)) return reject0('NoHiddenOracle.CheckList', ['checks'], 'check list must stay exact and ordered', { expected: EXPECTED_CHECKS, actual: manifest.checks });
  for (let index = 0; index < manifest.allowedExecutableLineRegexes.length; index += 1) {
    try { new RegExp(manifest.allowedExecutableLineRegexes[index], 'iu'); } catch (error) { return reject0('NoHiddenOracle.AllowedLineRegexInvalid', ['allowedExecutableLineRegexes', index], 'allowed executable line regex must compile', normalizeError0(error)); }
  }

  if (!plain0(manifest.audit)) return reject0('NoHiddenOracle.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'scripts/audit-no-hidden-oracle.mjs',
    command: 'npm run audit:no-hidden-oracle',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('NoHiddenOracle.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: manifest.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('NoHiddenOracle.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('NoHiddenOracle.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('NoHiddenOracle.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('NoHiddenOracle.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('NoHiddenOracle.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function scanRepository0({ root, manifest, extraVirtualFiles }) {
  const files = [];
  const walk = await walk0(root, '.', manifest, files);
  if (walk.tag === 'reject') return walk;
  for (const virtual of extraVirtualFiles) {
    if (!plain0(virtual) || !nonempty0(virtual.path) || typeof virtual.text !== 'string') return reject0('NoHiddenOracle.VirtualFileShape', ['extraVirtualFiles'], 'virtual files must have path and text');
    files.push({ path: normalizePath0(virtual.path), virtualText: virtual.text });
  }

  const patterns = manifest.forbiddenExecutablePatterns.map((entry) => ({ ...entry, re: new RegExp(entry.regex, 'iu') }));
  const allowedLineRegexes = manifest.allowedExecutableLineRegexes.map((regex) => new RegExp(regex, 'iu'));
  let scannedFileCount = 0;
  let executableFileCount = 0;
  let documentationReferenceCount = 0;
  let allowedExecutableReferenceCount = 0;
  const forbiddenHits = [];

  for (const file of files.sort((left, right) => left.path.localeCompare(right.path))) {
    const text = file.virtualText ?? await readFile(path.join(root, file.path), 'utf8');
    scannedFileCount += 1;
    const executable = manifest.scan.executableExtensions.includes(path.extname(file.path));
    if (executable) executableFileCount += 1;
    const allowedFile = manifest.allowedExecutableFiles.includes(file.path) || manifest.allowedExecutablePathPrefixes.some((prefix) => file.path.startsWith(prefix));
    const documentationFile = manifest.scan.documentationPathPrefixes.some((prefix) => file.path.startsWith(prefix)) || !executable;

    const lines = text.split(/\r?\n/u);
    for (let index = 0; index < lines.length; index += 1) {
      const line = lines[index];
      for (const pattern of patterns) {
        if (!pattern.re.test(line)) continue;
        const allowedLine = allowedLineRegexes.some((re) => re.test(line));
        if (!executable || documentationFile) {
          documentationReferenceCount += 1;
        } else if (allowedFile || allowedLine) {
          allowedExecutableReferenceCount += 1;
        } else {
          forbiddenHits.push({ file: file.path, line: index + 1, patternId: pattern.id, text: line.trim().slice(0, 240) });
        }
      }
    }
  }

  if (forbiddenHits.length !== 0) {
    return reject0('NoHiddenOracle.ForbiddenExecutableHit', ['scan'], 'unwhitelisted executable oracle/minimization/SAT-solver pattern found', { forbiddenHits: forbiddenHits.slice(0, 20), forbiddenHitCount: forbiddenHits.length });
  }

  return { tag: 'accept', scannedFileCount, executableFileCount, documentationReferenceCount, allowedExecutableReferenceCount };
}

async function walk0(root, relativeDir, manifest, files) {
  let entries;
  try {
    entries = await readdir(path.join(root, relativeDir), { withFileTypes: true });
  } catch (error) {
    return reject0('NoHiddenOracle.DirectoryReadFailed', [relativeDir], 'could not read repository directory', normalizeError0(error));
  }
  for (const entry of entries.sort((left, right) => left.name.localeCompare(right.name))) {
    const child = normalizePath0(relativeDir === '.' ? entry.name : `${relativeDir}/${entry.name}`);
    if (manifest.scan.skippedPathPrefixes.some((prefix) => child === prefix.slice(0, -1) || child.startsWith(prefix))) continue;
    if (entry.isDirectory()) {
      const nested = await walk0(root, child, manifest, files);
      if (nested.tag === 'reject') return nested;
    } else if (entry.isFile()) {
      if (manifest.scan.extensions.includes(path.extname(child))) files.push({ path: child });
    } else if (entry.isSymbolicLink()) {
      return reject0('NoHiddenOracle.SymlinkForbidden', [child], 'no-hidden-oracle scan rejects symlinks');
    }
  }
  return { tag: 'accept' };
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('NoHiddenOracle.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('NoHiddenOracle.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!nonempty0(value[index])) return reject0('NoHiddenOracle.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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

function normalizePath0(value) { return value.replace(/\\/gu, '/').replace(/^\.\//u, ''); }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

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

function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node scripts/audit-no-hidden-oracle.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/no-hidden-oracle/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --manifest <path>  Manifest path relative to root.\n  --output <path>    Verdict output path relative to root.\n`); }

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad no-hidden-oracle CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await AuditNoHiddenOracle0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
