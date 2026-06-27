#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { lstat, mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'audit-independent-verifiers-no-shared-code0';
const VERSION = 0;
const POLICY_PATH = 'independent-verifiers/NO_SHARED_CODE_POLICY.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/independent-verifiers/no-shared-code/latest-verdict.json';
const EXPECTED_KIND = 'PNPIndependentVerifierNoSharedCodePolicy0';
const EXPECTED_COORDINATE = 'PNP-INDEPENDENT-VERIFIERS-NO-SHARED-CODE-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export async function AuditIndependentVerifiersNoSharedCode0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const policyPath = options.policyPath ?? POLICY_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? false;
  const sourceTextOverrides = normalizeOverrideMap0(options.sourceTextOverrides ?? {});

  let policyBytes = null;
  let policy = options.policyOverride ?? null;

  if (policy === null) {
    try {
      policyBytes = await readFile(path.join(root, policyPath));
      policy = JSON.parse(policyBytes.toString('utf8'));
    } catch (error) {
      return reject0('Policy.ReadOrParseFailed', [policyPath], 'could not read or parse no-shared-code policy JSON', normalizeError0(error));
    }
  } else {
    policyBytes = Buffer.from(JSON.stringify(policy, null, 2));
  }

  const validation = validatePolicy0(policy);
  if (!validation.ok) return reject0('Policy.ValidationFailed', validation.path, validation.reason, validation.witness);

  const files = [];
  for (const verifier of policy.policy.verifiers) {
    const discovered = await discoverFiles0({ root, relativeRoot: verifier.root, allowedExtensions: policy.policy.allowedFileExtensions });
    if (discovered.tag === 'reject') return discovered;
    files.push(...discovered.files.map((file) => ({ ...file, verifierId: verifier.id })));
  }

  const uniqueFiles = dedupeByPath0(files);
  const scan = await scanFiles0({ root, files: uniqueFiles, policy, sourceTextOverrides });
  if (scan.tag === 'reject') return scan;

  const verdict = {
    tag: 'accept',
    kind: 'accept',
    checker: CHECKER,
    version: VERSION,
    coordinate: policy.coordinate,
    claimStatus: 'independent-verifier-no-shared-code-policy-accepted',
    policyPath,
    policySha256: sha256Hex0(policyBytes),
    verifierCount: policy.policy.verifiers.length,
    scannedFileCount: uniqueFiles.length,
    scannedPythonSourceCount: scan.pythonSourceCount,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    remainingBlockers: [...EXPECTED_BLOCKERS],
    noSharedCodePolicy: {
      jsonArtifactsOnly: true,
      importsJavaScriptCheckerCode: false,
      spawnsJavaScriptRuntime: false,
      forbiddenExecutablePatternsRejected: true,
    },
    outputPath: writeOutput ? outputPath : null,
  };

  if (writeOutput) {
    const absoluteOutputPath = path.join(root, outputPath);
    await mkdir(path.dirname(absoluteOutputPath), { recursive: true });
    await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
  }

  return verdict;
}

function validatePolicy0(policy) {
  if (!isPlainObject0(policy)) return invalid0([], 'policy must be an object');
  if (policy.kind !== EXPECTED_KIND) return invalid0(['kind'], 'policy kind mismatch', { expected: EXPECTED_KIND, actual: policy.kind });
  if (policy.version !== VERSION) return invalid0(['version'], 'policy version mismatch', { expected: VERSION, actual: policy.version });
  if (policy.coordinate !== EXPECTED_COORDINATE) return invalid0(['coordinate'], 'policy coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: policy.coordinate });

  const boundary = validateBoundary0(policy.claimBoundary);
  if (!boundary.ok) return boundary;

  if (!isPlainObject0(policy.policy)) return invalid0(['policy'], 'policy field must be an object');
  if (policy.policy.independentVerifierRoot !== 'independent-verifiers') return invalid0(['policy', 'independentVerifierRoot'], 'independent verifier root mismatch');
  if (!sameStringArray0(policy.policy.requiredDataInputs, ['kernel/PNP_MINIMAL_KERNEL.json', 'report-bindings/REPORT_THEOREM_BINDINGS.json'])) {
    return invalid0(['policy', 'requiredDataInputs'], 'required data inputs must stay exact');
  }
  if (!sameStringArray0(policy.policy.allowedFileExtensions, ['.json', '.md', '.py'])) return invalid0(['policy', 'allowedFileExtensions'], 'allowed file extensions must stay exact');
  const allowedImports = validateStringArray0(policy.policy.allowedPythonImports, ['policy', 'allowedPythonImports'], true);
  if (!allowedImports.ok) return allowedImports;
  const forbiddenImports = validateStringArray0(policy.policy.forbiddenPythonImports, ['policy', 'forbiddenPythonImports'], true);
  if (!forbiddenImports.ok) return forbiddenImports;
  const forbiddenPatterns = validateStringArray0(policy.policy.forbiddenExecutablePatterns, ['policy', 'forbiddenExecutablePatterns'], true);
  if (!forbiddenPatterns.ok) return forbiddenPatterns;
  const forbiddenTokens = validateStringArray0(policy.policy.forbiddenRuntimeTokens, ['policy', 'forbiddenRuntimeTokens'], true);
  if (!forbiddenTokens.ok) return forbiddenTokens;

  if (!Array.isArray(policy.policy.verifiers) || policy.policy.verifiers.length === 0) return invalid0(['policy', 'verifiers'], 'at least one independent verifier must be declared');
  const seen = new Set();
  for (let index = 0; index < policy.policy.verifiers.length; index += 1) {
    const verifier = policy.policy.verifiers[index];
    const pathArray = ['policy', 'verifiers', index];
    if (!isPlainObject0(verifier)) return invalid0(pathArray, 'verifier entry must be an object');
    for (const key of ['id', 'root', 'language', 'entrypoint']) {
      if (!isNonEmptyString0(verifier[key])) return invalid0([...pathArray, key], 'verifier field must be a non-empty string');
    }
    if (seen.has(verifier.id)) return invalid0([...pathArray, 'id'], 'verifier ids must be unique', { id: verifier.id });
    seen.add(verifier.id);
    if (!verifier.root.startsWith('independent-verifiers/')) return invalid0([...pathArray, 'root'], 'verifier root must stay under independent-verifiers');
    if (!verifier.entrypoint.startsWith(`${verifier.root}/`)) return invalid0([...pathArray, 'entrypoint'], 'verifier entrypoint must be under verifier root');
    if (verifier.importsJavaScriptCheckerCode !== false) return invalid0([...pathArray, 'importsJavaScriptCheckerCode'], 'verifier cannot import JavaScript checker code');
    if (verifier.spawnsJavaScriptRuntime !== false) return invalid0([...pathArray, 'spawnsJavaScriptRuntime'], 'verifier cannot spawn JavaScript runtime');
    if (verifier.usesSharedJsonArtifactsOnly !== true) return invalid0([...pathArray, 'usesSharedJsonArtifactsOnly'], 'verifier must consume shared artifacts only as data');
    if (!sameStringArray0(verifier.allowedDataInputs, policy.policy.requiredDataInputs)) return invalid0([...pathArray, 'allowedDataInputs'], 'verifier allowed data inputs must match policy required data inputs');
    const tests = validateStringArray0(verifier.tests, [...pathArray, 'tests'], true);
    if (!tests.ok) return tests;
    for (const testPath of verifier.tests) {
      if (!testPath.startsWith(`${verifier.root}/`)) return invalid0([...pathArray, 'tests'], 'verifier tests must stay under verifier root', { testPath });
    }
  }

  if (!isPlainObject0(policy.audit)) return invalid0(['audit'], 'audit field must be an object');
  if (policy.audit.script !== 'scripts/audit-independent-verifiers-no-shared-code.mjs') return invalid0(['audit', 'script'], 'audit script path mismatch');
  if (policy.audit.command !== 'npm run independent:no-shared-code') return invalid0(['audit', 'command'], 'audit command mismatch');

  return { ok: true };
}

function validateBoundary0(boundary) {
  if (!isPlainObject0(boundary)) return invalid0(['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return invalid0(['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return invalid0(['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameStringArray0(boundary.activeFinalNodeIds, [])) return invalid0(['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameStringArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return invalid0(['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { ok: true };
}

async function discoverFiles0({ root, relativeRoot, allowedExtensions }) {
  const absoluteRoot = safeJoin0(root, relativeRoot);
  if (absoluteRoot === null) return reject0('Path.UnsafeVerifierRoot', [relativeRoot], 'verifier root path is unsafe');

  const files = [];
  async function walk(currentAbsolute, currentRelative) {
    let info;
    try {
      info = await lstat(currentAbsolute);
    } catch (error) {
      return reject0('Path.ReadFailed', [currentRelative], 'could not inspect independent verifier path', normalizeError0(error));
    }
    if (info.isSymbolicLink()) return reject0('Path.SymlinkForbidden', [currentRelative], 'independent verifier tree must not contain symlinks');
    if (info.isDirectory()) {
      const entries = await readdir(currentAbsolute, { withFileTypes: true });
      for (const entry of entries.sort((left, right) => left.name.localeCompare(right.name))) {
        const childRelative = `${currentRelative}/${entry.name}`;
        const childAbsolute = path.join(currentAbsolute, entry.name);
        const result = await walk(childAbsolute, childRelative);
        if (result?.tag === 'reject') return result;
      }
      return null;
    }
    if (!info.isFile()) return reject0('Path.UnsupportedNode', [currentRelative], 'independent verifier tree may contain only files and directories');
    const ext = path.extname(currentRelative);
    if (!allowedExtensions.includes(ext)) return reject0('Path.UnsupportedExtension', [currentRelative], 'independent verifier file extension is not policy-allowed', { ext, allowedExtensions });
    files.push({ path: currentRelative, extension: ext });
    return null;
  }

  const result = await walk(absoluteRoot, relativeRoot);
  if (result?.tag === 'reject') return result;
  return { tag: 'accept', files };
}

async function scanFiles0({ root, files, policy, sourceTextOverrides }) {
  let pythonSourceCount = 0;
  const allowedImports = new Set(policy.policy.allowedPythonImports);
  const forbiddenImports = new Set(policy.policy.forbiddenPythonImports);
  const forbiddenPatterns = policy.policy.forbiddenExecutablePatterns;
  const forbiddenTokens = policy.policy.forbiddenRuntimeTokens;

  for (const file of files) {
    let text;
    if (sourceTextOverrides.has(file.path)) {
      text = sourceTextOverrides.get(file.path);
    } else {
      try {
        text = await readFile(path.join(root, file.path), 'utf8');
      } catch (error) {
        return reject0('File.ReadFailed', [file.path], 'could not read independent verifier file', normalizeError0(error));
      }
    }

    if (file.extension === '.py') {
      pythonSourceCount += 1;
      const importScan = scanPythonImports0(text, file.path, allowedImports, forbiddenImports);
      if (importScan.tag === 'reject') return importScan;
      const patternScan = scanForbiddenExecutablePatterns0(text, file.path, forbiddenPatterns, forbiddenTokens);
      if (patternScan.tag === 'reject') return patternScan;
    }
  }

  if (pythonSourceCount === 0) return reject0('Scan.NoPythonSources', ['independent-verifiers'], 'no Python verifier source files were scanned');
  return { tag: 'accept', pythonSourceCount };
}

function scanPythonImports0(text, relativePath, allowedImports, forbiddenImports) {
  const lines = text.split(/\r?\n/u);
  for (let index = 0; index < lines.length; index += 1) {
    const line = stripInlineComment0(lines[index]).trim();
    const importMatch = line.match(/^import\s+([A-Za-z_][\w.]*)/u);
    const fromMatch = line.match(/^from\s+([A-Za-z_][\w.]*)\s+import\s+/u);
    const moduleName = importMatch?.[1] ?? fromMatch?.[1] ?? null;
    if (moduleName === null) continue;
    const topLevel = moduleName.split('.')[0];
    if (forbiddenImports.has(topLevel)) {
      return reject0('PythonImport.Forbidden', [relativePath, index + 1], 'independent verifier imports a forbidden module', { moduleName, topLevel });
    }
    if (!allowedImports.has(topLevel)) {
      return reject0('PythonImport.NotAllowed', [relativePath, index + 1], 'independent verifier imports a module outside the policy allow-list', { moduleName, topLevel, allowed: [...allowedImports].sort() });
    }
  }
  return { tag: 'accept' };
}

function scanForbiddenExecutablePatterns0(text, relativePath, forbiddenPatterns, forbiddenTokens) {
  for (const pattern of forbiddenPatterns) {
    const offset = text.indexOf(pattern);
    if (offset !== -1) {
      return reject0('Source.ForbiddenExecutablePattern', [relativePath], 'independent verifier source contains a forbidden executable pattern', { pattern, offset });
    }
  }

  const runtimePattern = new RegExp(String.raw`(?:^|[^A-Za-z0-9_])(${forbiddenTokens.map(escapeRegExp0).join('|')})(?:[^A-Za-z0-9_]|$)`, 'iu');
  const runtimeHit = runtimePattern.exec(text);
  if (runtimeHit !== null) {
    return reject0('Source.ForbiddenRuntimeToken', [relativePath], 'independent verifier source contains a forbidden JavaScript runtime token', { token: runtimeHit[1] });
  }
  return { tag: 'accept' };
}

function stripInlineComment0(line) {
  const hashIndex = line.indexOf('#');
  if (hashIndex === -1) return line;
  return line.slice(0, hashIndex);
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

function invalid0(pathArray, reason, witness = {}) {
  return { ok: false, path: pathArray, reason, witness };
}

function validateStringArray0(value, pathArray, nonEmpty = false) {
  if (!Array.isArray(value)) return invalid0(pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return invalid0(pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!isNonEmptyString0(value[index])) return invalid0([...pathArray, index], 'array entry must be a non-empty string');
  }
  return { ok: true };
}

function normalizeOverrideMap0(overrides) {
  if (overrides instanceof Map) return overrides;
  return new Map(Object.entries(overrides));
}

function dedupeByPath0(files) {
  const seen = new Map();
  for (const file of files) seen.set(file.path, file);
  return [...seen.values()].sort((left, right) => left.path.localeCompare(right.path));
}

function safeJoin0(root, relativePath) {
  if (!isNonEmptyString0(relativePath) || path.isAbsolute(relativePath)) return null;
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
}

function sameStringArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function sha256Hex0(buffer) {
  return createHash('sha256').update(buffer).digest('hex');
}

function escapeRegExp0(text) {
  return text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
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
  const options = { root: process.cwd(), policyPath: POLICY_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') {
      index += 1;
      if (index >= argv.length) throw new Error('--root requires a value');
      options.root = argv[index];
    } else if (arg === '--policy') {
      index += 1;
      if (index >= argv.length) throw new Error('--policy requires a value');
      options.policyPath = argv[index];
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
  console.log(`Usage: node scripts/audit-independent-verifiers-no-shared-code.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/independent-verifiers/no-shared-code/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --policy <path>    Policy path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad no-shared-code audit CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await AuditIndependentVerifiersNoSharedCode0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0();
}
