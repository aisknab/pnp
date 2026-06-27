#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { readFile, stat } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'audit-report-theorem-bindings0';
const VERSION = 0;
const EXPECTED_KIND = 'PNPReportTheoremBindings0';
const EXPECTED_BLOCKERS = [
  'Release.UnrestrictedFinalSoundness',
  'ExternalReview.Acceptance',
];

const TEXT_EXTENSIONS = new Set([
  '.js',
  '.json',
  '.md',
  '.mjs',
  '.tex',
  '.txt',
  '.yml',
  '.yaml',
]);

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    ledgerPath: 'report-bindings/REPORT_THEOREM_BINDINGS.json',
    json: false,
    skipFileExistence: false,
    skipCheckerSearch: false,
    skipAnchorSearch: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') {
      options.json = true;
    } else if (arg === '--skip-file-existence') {
      options.skipFileExistence = true;
    } else if (arg === '--skip-checker-search') {
      options.skipCheckerSearch = true;
    } else if (arg === '--skip-anchor-search') {
      options.skipAnchorSearch = true;
    } else if (arg === '--root') {
      index += 1;
      if (index >= argv.length) throw new Error('--root requires a value');
      options.root = argv[index];
    } else if (arg === '--ledger') {
      index += 1;
      if (index >= argv.length) throw new Error('--ledger requires a value');
      options.ledgerPath = argv[index];
    } else if (arg === '--help' || arg === '-h') {
      printHelp();
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }

  return options;
}

function printHelp() {
  console.log(`Usage: node scripts/audit-report-theorem-bindings.mjs [options]\n\nOptions:\n  --root <path>       Repository root. Defaults to cwd.\n  --ledger <path>     Ledger path relative to root. Defaults to report-bindings/REPORT_THEOREM_BINDINGS.json.\n  --json              Emit the verdict JSON only.\n  --skip-file-existence  Validate ledger schema without checking referenced paths.\n  --skip-checker-search  Do not verify checker ids occur in declared checker files.\n  --skip-anchor-search   Do not verify report anchors in the TeX source.\n`);
}

async function main() {
  let options;
  try {
    options = parseArgs(process.argv.slice(2));
  } catch (error) {
    const verdict = rejectVerdict('Cli.BadArgument', [], { message: error.message });
    emit(verdict, false);
    process.exit(2);
  }

  const absoluteLedgerPath = path.resolve(options.root, options.ledgerPath);
  let ledgerBytes;
  let ledger;

  try {
    ledgerBytes = await readFile(absoluteLedgerPath);
  } catch (error) {
    const verdict = rejectVerdict('Ledger.ReadFailed', [options.ledgerPath], normalizeError(error));
    emit(verdict, options.json);
    process.exit(1);
  }

  try {
    ledger = JSON.parse(ledgerBytes.toString('utf8'));
  } catch (error) {
    const verdict = rejectVerdict('Ledger.ParseFailed', [options.ledgerPath], normalizeError(error));
    emit(verdict, options.json);
    process.exit(1);
  }

  const failures = [];
  validateLedgerShape(ledger, failures);

  if (failures.length === 0 && !options.skipFileExistence) {
    await validateReferencedPaths(ledger, options.root, failures);
  }

  if (failures.length === 0 && !options.skipAnchorSearch) {
    await validateReportAnchors(ledger, options.root, failures);
  }

  if (failures.length === 0 && !options.skipCheckerSearch) {
    await validateCheckerIds(ledger, options.root, failures);
  }

  if (failures.length !== 0) {
    const verdict = rejectVerdict('Ledger.ValidationFailed', [], {
      failureCount: failures.length,
      firstFailure: failures[0],
      failures,
    });
    emit(verdict, options.json);
    process.exit(1);
  }

  const resolved = resolveAllBindings(ledger);
  const verdict = {
    tag: 'accept',
    kind: 'accept',
    checker: CHECKER,
    version: VERSION,
    coordinate: ledger.coordinate,
    ledgerPath: options.ledgerPath,
    ledgerSha256: sha256Hex(ledgerBytes),
    groupCount: Object.keys(ledger.bindingGroups).length,
    theoremBindingCount: ledger.theoremBindings.length,
    checkerFileCount: sortedUnique(resolved.flatMap((entry) => entry.checkerFiles)).length,
    proofArtifactCount: sortedUnique(resolved.flatMap((entry) => entry.proofArtifacts)).length,
    testFileCount: sortedUnique(resolved.flatMap((entry) => entry.tests)).length,
    claimBoundary: {
      publicTheoremEmissionAllowed: ledger.claimBoundary.publicTheoremEmissionAllowed,
      finalTheoremReady: ledger.claimBoundary.finalTheoremReady,
      activeFinalNodeIds: ledger.claimBoundary.activeFinalNodeIds,
      remainingBlockers: ledger.claimBoundary.remainingBlockers,
    },
  };

  emit(verdict, options.json);
}

function validateLedgerShape(ledger, failures) {
  if (!isPlainObject(ledger)) {
    pushFailure(failures, 'Ledger.Shape', [], 'ledger must be a JSON object');
    return;
  }

  requireEqual(ledger.kind, EXPECTED_KIND, failures, ['kind']);
  requireEqual(ledger.version, VERSION, failures, ['version']);
  requireNonEmptyString(ledger.coordinate, failures, ['coordinate']);
  requireNonEmptyString(ledger.purpose, failures, ['purpose']);
  requireNonEmptyString(ledger.reportTextSource, failures, ['reportTextSource']);

  validateClaimBoundary(ledger.claimBoundary, failures);

  if (!Array.isArray(ledger.sources) || ledger.sources.length === 0) {
    pushFailure(failures, 'Sources.Shape', ['sources'], 'sources must be a non-empty array');
  } else {
    ledger.sources.forEach((source, index) => validateSource(source, failures, ['sources', index]));
  }

  if (!isPlainObject(ledger.bindingGroups)) {
    pushFailure(failures, 'BindingGroups.Shape', ['bindingGroups'], 'bindingGroups must be an object');
  } else {
    for (const [id, group] of Object.entries(ledger.bindingGroups)) {
      validateBindingGroup(id, group, failures, ['bindingGroups', id]);
    }
  }

  if (!Array.isArray(ledger.theoremBindings) || ledger.theoremBindings.length === 0) {
    pushFailure(failures, 'TheoremBindings.Shape', ['theoremBindings'], 'theoremBindings must be a non-empty array');
    return;
  }

  const seenIds = new Set();
  for (let index = 0; index < ledger.theoremBindings.length; index += 1) {
    const binding = ledger.theoremBindings[index];
    const bindingPath = ['theoremBindings', index];
    validateTheoremBinding(binding, ledger.bindingGroups ?? {}, failures, bindingPath);
    if (isPlainObject(binding) && typeof binding.id === 'string') {
      if (seenIds.has(binding.id)) {
        pushFailure(failures, 'TheoremBindings.DuplicateId', [...bindingPath, 'id'], 'theorem binding ids must be unique', { id: binding.id });
      }
      seenIds.add(binding.id);
    }
  }

  if (isPlainObject(ledger.audit)) {
    if (Number.isInteger(ledger.audit.expectedBindingCount) && ledger.audit.expectedBindingCount !== ledger.theoremBindings.length) {
      pushFailure(failures, 'Audit.ExpectedBindingCount', ['audit', 'expectedBindingCount'], 'expectedBindingCount must equal theoremBindings.length', {
        expectedBindingCount: ledger.audit.expectedBindingCount,
        actual: ledger.theoremBindings.length,
      });
    }
    if (typeof ledger.audit.script === 'string' && ledger.audit.script !== 'scripts/audit-report-theorem-bindings.mjs') {
      pushFailure(failures, 'Audit.ScriptPath', ['audit', 'script'], 'audit script path drifted');
    }
  }
}

function validateClaimBoundary(boundary, failures) {
  if (!isPlainObject(boundary)) {
    pushFailure(failures, 'ClaimBoundary.Shape', ['claimBoundary'], 'claimBoundary must be an object');
    return;
  }

  requireEqual(boundary.publicTheoremEmissionAllowed, false, failures, ['claimBoundary', 'publicTheoremEmissionAllowed']);
  requireEqual(boundary.finalTheoremReady, false, failures, ['claimBoundary', 'finalTheoremReady']);

  if (!Array.isArray(boundary.activeFinalNodeIds) || boundary.activeFinalNodeIds.length !== 0) {
    pushFailure(failures, 'ClaimBoundary.ActiveFinalNodeIds', ['claimBoundary', 'activeFinalNodeIds'], 'activeFinalNodeIds must be empty');
  }

  if (!sameStringSet(boundary.remainingBlockers, EXPECTED_BLOCKERS)) {
    pushFailure(failures, 'ClaimBoundary.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must stay exact', {
      expected: EXPECTED_BLOCKERS,
      actual: boundary.remainingBlockers,
    });
  }
}

function validateSource(source, failures, sourcePath) {
  if (!isPlainObject(source)) {
    pushFailure(failures, 'Source.Shape', sourcePath, 'source must be an object');
    return;
  }
  requireNonEmptyString(source.id, failures, [...sourcePath, 'id']);
  requireNonEmptyString(source.kind, failures, [...sourcePath, 'kind']);
  if (!hasAnyStringPath(source, ['path', 'textPath', 'pdfPath', 'checksumPath'])) {
    pushFailure(failures, 'Source.Path', sourcePath, 'source must declare at least one local path field');
  }
}

function validateBindingGroup(id, group, failures, groupPath) {
  if (!isNonEmptyString(id)) {
    pushFailure(failures, 'BindingGroup.Id', groupPath, 'binding group id must be non-empty');
  }
  if (!isPlainObject(group)) {
    pushFailure(failures, 'BindingGroup.Shape', groupPath, 'binding group must be an object');
    return;
  }
  requireNonEmptyString(group.description, failures, [...groupPath, 'description']);
  requireStringArray(group.checkerIds, failures, [...groupPath, 'checkerIds'], { nonEmpty: true });
  requireStringArray(group.checkerFiles, failures, [...groupPath, 'checkerFiles'], { nonEmpty: true });
  requireStringArray(group.proofArtifacts, failures, [...groupPath, 'proofArtifacts'], { nonEmpty: true });
  requireStringArray(group.tests, failures, [...groupPath, 'tests'], { nonEmpty: true });
  requireNonEmptyString(group.bindingStrength, failures, [...groupPath, 'bindingStrength']);
}

function validateTheoremBinding(binding, groups, failures, bindingPath) {
  if (!isPlainObject(binding)) {
    pushFailure(failures, 'TheoremBinding.Shape', bindingPath, 'theorem binding must be an object');
    return;
  }

  for (const key of ['id', 'theoremNumber', 'reportSection', 'reportTheoremName', 'statementSummary', 'bindingStatus', 'claimEffect', 'publicEmissionEffect']) {
    requireNonEmptyString(binding[key], failures, [...bindingPath, key]);
  }

  requireStringArray(binding.reportAnchors, failures, [...bindingPath, 'reportAnchors'], { nonEmpty: true });
  requireStringArray(binding.bindingGroupIds, failures, [...bindingPath, 'bindingGroupIds'], { nonEmpty: true });

  if (binding.claimEffect !== 'audit-ledger-only') {
    pushFailure(failures, 'TheoremBinding.ClaimEffect', [...bindingPath, 'claimEffect'], 'claimEffect must be audit-ledger-only');
  }
  if (binding.publicEmissionEffect !== 'none') {
    pushFailure(failures, 'TheoremBinding.PublicEmissionEffect', [...bindingPath, 'publicEmissionEffect'], 'publicEmissionEffect must be none');
  }
  if (binding.dischargesPublicTheorem !== false) {
    pushFailure(failures, 'TheoremBinding.NoPublicDischarge', [...bindingPath, 'dischargesPublicTheorem'], 'theorem binding ledger cannot discharge public theorem emission');
  }

  for (const groupId of binding.bindingGroupIds ?? []) {
    if (!Object.prototype.hasOwnProperty.call(groups, groupId)) {
      pushFailure(failures, 'TheoremBinding.UnknownGroup', [...bindingPath, 'bindingGroupIds'], 'binding references an unknown group', { groupId });
    }
  }

  if (binding.bindingGroupIds?.length > 0 && isPlainObject(groups)) {
    const resolved = resolveBinding(binding, groups);
    for (const field of ['checkerIds', 'checkerFiles', 'proofArtifacts', 'tests']) {
      if (!Array.isArray(resolved[field]) || resolved[field].length === 0) {
        pushFailure(failures, 'TheoremBinding.EmptyResolvedField', [...bindingPath, field], `resolved ${field} must be non-empty`);
      }
    }
  }
}

async function validateReferencedPaths(ledger, root, failures) {
  const paths = collectReferencedPaths(ledger);
  for (const relativePath of paths) {
    const absolutePath = safeJoin(root, relativePath);
    if (absolutePath === null) {
      pushFailure(failures, 'Path.Unsafe', [relativePath], 'referenced path must remain inside repository root');
      continue;
    }
    try {
      const info = await stat(absolutePath);
      if (!info.isFile()) {
        pushFailure(failures, 'Path.NotFile', [relativePath], 'referenced path is not a file');
      }
    } catch (error) {
      pushFailure(failures, 'Path.Missing', [relativePath], 'referenced file is missing', normalizeError(error));
    }
  }
}

async function validateReportAnchors(ledger, root, failures) {
  const sourcePath = ledger.reportTextSource;
  const absolutePath = safeJoin(root, sourcePath);
  if (absolutePath === null) {
    pushFailure(failures, 'ReportAnchor.UnsafePath', ['reportTextSource'], 'reportTextSource must remain inside repository root');
    return;
  }

  let text;
  try {
    text = await readFile(absolutePath, 'utf8');
  } catch (error) {
    pushFailure(failures, 'ReportAnchor.ReadFailed', ['reportTextSource'], 'could not read report text source', normalizeError(error));
    return;
  }

  for (let index = 0; index < ledger.theoremBindings.length; index += 1) {
    const binding = ledger.theoremBindings[index];
    for (const anchor of binding.reportAnchors ?? []) {
      if (!text.includes(anchor)) {
        pushFailure(failures, 'ReportAnchor.Missing', ['theoremBindings', index, 'reportAnchors'], 'report anchor not found in report text source', {
          id: binding.id,
          anchor,
          reportTextSource: sourcePath,
        });
      }
    }
  }
}

async function validateCheckerIds(ledger, root, failures) {
  const groups = ledger.bindingGroups;
  const textCache = new Map();

  for (const [groupId, group] of Object.entries(groups)) {
    const texts = [];
    for (const relativePath of group.checkerFiles) {
      const ext = path.extname(relativePath);
      if (!TEXT_EXTENSIONS.has(ext)) continue;
      const absolutePath = safeJoin(root, relativePath);
      if (absolutePath === null) continue;
      if (!textCache.has(relativePath)) {
        try {
          textCache.set(relativePath, await readFile(absolutePath, 'utf8'));
        } catch (error) {
          textCache.set(relativePath, null);
        }
      }
      const text = textCache.get(relativePath);
      if (typeof text === 'string') texts.push({ relativePath, text });
    }

    for (const checkerId of group.checkerIds) {
      const hit = texts.some(({ text }) => text.includes(checkerId));
      if (!hit) {
        pushFailure(failures, 'CheckerId.NotFoundInFiles', ['bindingGroups', groupId, 'checkerIds'], 'checker id does not occur in any declared checker file', {
          groupId,
          checkerId,
          checkerFiles: group.checkerFiles,
        });
      }
    }
  }
}

function resolveAllBindings(ledger) {
  return ledger.theoremBindings.map((binding) => resolveBinding(binding, ledger.bindingGroups));
}

function resolveBinding(binding, groups) {
  const resolved = {
    id: binding.id,
    checkerIds: [],
    checkerFiles: [],
    proofArtifacts: [],
    tests: [],
  };

  for (const groupId of binding.bindingGroupIds ?? []) {
    const group = groups[groupId];
    if (!group) continue;
    for (const field of ['checkerIds', 'checkerFiles', 'proofArtifacts', 'tests']) {
      resolved[field].push(...(group[field] ?? []));
    }
  }

  for (const field of ['checkerIds', 'checkerFiles', 'proofArtifacts', 'tests']) {
    if (Array.isArray(binding[field])) resolved[field].push(...binding[field]);
    resolved[field] = sortedUnique(resolved[field]);
  }

  return resolved;
}

function collectReferencedPaths(ledger) {
  const out = [];
  out.push(ledger.reportTextSource);
  out.push('report-bindings/REPORT_THEOREM_BINDINGS.json');
  out.push(ledger.audit?.script);

  for (const source of ledger.sources ?? []) {
    for (const key of ['path', 'textPath', 'pdfPath', 'checksumPath', 'sha256Path', 'artifactPath']) {
      if (typeof source?.[key] === 'string') out.push(source[key]);
    }
  }

  for (const group of Object.values(ledger.bindingGroups ?? {})) {
    for (const field of ['checkerFiles', 'proofArtifacts', 'tests']) {
      for (const value of group?.[field] ?? []) out.push(value);
    }
  }

  for (const binding of ledger.theoremBindings ?? []) {
    for (const field of ['checkerFiles', 'proofArtifacts', 'tests']) {
      for (const value of binding?.[field] ?? []) out.push(value);
    }
  }

  return sortedUnique(out.filter((entry) => typeof entry === 'string' && entry.length > 0 && !entry.startsWith('http://') && !entry.startsWith('https://')));
}

function requireEqual(actual, expected, failures, pathArray) {
  if (actual !== expected) {
    pushFailure(failures, 'Field.ValueMismatch', pathArray, 'field has unexpected value', { expected, actual });
  }
}

function requireNonEmptyString(value, failures, pathArray) {
  if (!isNonEmptyString(value)) {
    pushFailure(failures, 'Field.NonEmptyString', pathArray, 'field must be a non-empty string', { actual: value });
  }
}

function requireStringArray(value, failures, pathArray, { nonEmpty = false } = {}) {
  if (!Array.isArray(value)) {
    pushFailure(failures, 'Field.StringArray', pathArray, 'field must be an array of strings', { actual: value });
    return;
  }
  if (nonEmpty && value.length === 0) {
    pushFailure(failures, 'Field.NonEmptyArray', pathArray, 'field must not be empty');
  }
  for (let index = 0; index < value.length; index += 1) {
    if (!isNonEmptyString(value[index])) {
      pushFailure(failures, 'Field.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string', { actual: value[index] });
    }
  }
}

function pushFailure(failures, coord, pathArray, reason, witness = {}) {
  failures.push({ coord, path: pathArray, reason, witness });
}

function rejectVerdict(coord, pathArray, witness) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER,
    version: VERSION,
    coord,
    path: pathArray,
    witness,
  };
}

function emit(verdict, jsonOnly) {
  if (jsonOnly) {
    console.log(JSON.stringify(verdict, null, 2));
    return;
  }

  if (verdict.tag === 'accept') {
    console.log(`[accept] ${CHECKER}`);
    console.log(JSON.stringify(verdict, null, 2));
  } else {
    console.error(`[reject] ${CHECKER}: ${verdict.coord}`);
    console.error(JSON.stringify(verdict, null, 2));
  }
}

function sha256Hex(buffer) {
  return createHash('sha256').update(buffer).digest('hex');
}

function sortedUnique(values) {
  return Array.from(new Set(values)).sort();
}

function sameStringSet(actual, expected) {
  if (!Array.isArray(actual)) return false;
  const left = sortedUnique(actual);
  const right = sortedUnique(expected);
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function hasAnyStringPath(object, keys) {
  return keys.some((key) => typeof object?.[key] === 'string' && object[key].length > 0);
}

function safeJoin(root, relativePath) {
  if (typeof relativePath !== 'string' || relativePath.length === 0 || path.isAbsolute(relativePath)) {
    return null;
  }
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
}

function normalizeError(error) {
  return {
    name: error?.name ?? 'Error',
    message: error?.message ?? String(error),
    code: error?.code ?? null,
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

main().catch((error) => {
  const verdict = rejectVerdict('Audit.UnhandledException', [], normalizeError(error));
  emit(verdict, false);
  process.exit(1);
});
