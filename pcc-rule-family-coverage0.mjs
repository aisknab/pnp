#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckRuleFamilyCoverage0';
const VERSION = 0;
const LEDGER_PATH = 'semantic-kernel/RULE_FAMILY_COVERAGE.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/rule-family-coverage/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-RULE-FAMILY-COVERAGE-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_FAMILY_IDS = ['DPInd', 'GlobalFinalPrefix', 'SATReduction', 'Complexity', 'PublicEmission', 'SuccessorSeal', 'TrustBase'];
const VALID_COVERAGE_STATUSES = new Set(['represented-seed', 'covered-seed', 'planned']);

export async function CheckRuleFamilyCoverage0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const ledgerPath = options.ledgerPath ?? LEDGER_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const read = await readLedger0({ root, ledgerPath, override: options.ledgerOverride });
    if (read.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, read);

    const validation = validateLedger0(read.ledger);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, validation);

    const evidence = await validateEvidenceFiles0({ root, ledger: read.ledger });
    if (evidence.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, evidence);

    const totals = read.ledger.ruleFamilies.reduce((acc, family) => {
      acc.positiveTestCount += family.positiveTestCount;
      acc.negativeTestCount += family.negativeTestCount;
      acc.mutationTestCount += family.mutationTestCount;
      return acc;
    }, { positiveTestCount: 0, negativeTestCount: 0, mutationTestCount: 0 });

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'rule-family-coverage-ledger-accepted',
      ledgerPath,
      ledgerSha256: sha256Hex0(read.bytes),
      coverageLedgerReady: true,
      fullRuleFamilyCoverageProved: false,
      ruleFamilyCount: read.ledger.ruleFamilies.length,
      ruleFamilyIds: EXPECTED_FAMILY_IDS,
      totalPositiveTestCount: totals.positiveTestCount,
      totalNegativeTestCount: totals.negativeTestCount,
      totalMutationTestCount: totals.mutationTestCount,
      evidenceFileCount: evidence.evidenceFileCount,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('RuleFamilyCoverage.UnhandledException', [], 'rule-family coverage checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readLedger0({ root, ledgerPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', ledger: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, ledgerPath));
    return { tag: 'accept', ledger: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('RuleFamilyCoverage.ReadOrParseFailed', [ledgerPath], 'could not read or parse rule-family coverage ledger', normalizeError0(error));
  }
}

function validateLedger0(ledger) {
  if (!isPlainObject0(ledger)) return reject0('RuleFamilyCoverage.Shape', [], 'ledger must be an object');
  if (ledger.kind !== 'PNPRuleFamilyCoverage0') return reject0('RuleFamilyCoverage.Kind', ['kind'], 'ledger kind mismatch');
  if (ledger.version !== VERSION) return reject0('RuleFamilyCoverage.Version', ['version'], 'ledger version mismatch');
  if (ledger.coordinate !== EXPECTED_COORDINATE) return reject0('RuleFamilyCoverage.Coordinate', ['coordinate'], 'ledger coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: ledger.coordinate });
  if (ledger.status !== 'rule-family-coverage-ledger-ready') return reject0('RuleFamilyCoverage.Status', ['status'], 'ledger status mismatch');
  if (ledger.coverageLedgerReady !== true) return reject0('RuleFamilyCoverage.ReadyFlag', ['coverageLedgerReady'], 'coverageLedgerReady must be true');
  if (ledger.fullRuleFamilyCoverageProved !== false) return reject0('RuleFamilyCoverage.FullCoverageFlag', ['fullRuleFamilyCoverageProved'], 'seed ledger cannot claim full rule-family coverage');

  const boundary = validateBoundary0(ledger.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!Array.isArray(ledger.ruleFamilies)) return reject0('RuleFamilyCoverage.FamiliesShape', ['ruleFamilies'], 'ruleFamilies must be an array');
  const ids = ledger.ruleFamilies.map((family) => family?.id);
  if (!sameArray0(ids, EXPECTED_FAMILY_IDS)) return reject0('RuleFamilyCoverage.FamilyIds', ['ruleFamilies'], 'rule family ids must stay exact and ordered', { expected: EXPECTED_FAMILY_IDS, actual: ids });

  let coveredSeedCount = 0;
  for (let index = 0; index < ledger.ruleFamilies.length; index += 1) {
    const family = ledger.ruleFamilies[index];
    const familyPath = ['ruleFamilies', index];
    const check = validateFamily0(family, familyPath);
    if (check.tag === 'reject') return check;
    if (family.coverageStatus === 'covered-seed') coveredSeedCount += 1;
  }
  if (coveredSeedCount === 0) return reject0('RuleFamilyCoverage.NoCoveredSeed', ['ruleFamilies'], 'at least one family must have covered-seed status');

  if (!isPlainObject0(ledger.audit)) return reject0('RuleFamilyCoverage.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-rule-family-coverage0.mjs',
    command: 'npm run rule-family:coverage',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (ledger.audit[key] !== expected) return reject0('RuleFamilyCoverage.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: ledger.audit[key] });
  }

  return { tag: 'accept' };
}

function validateFamily0(family, familyPath) {
  if (!isPlainObject0(family)) return reject0('RuleFamilyCoverage.FamilyShape', familyPath, 'rule-family entry must be an object');
  for (const field of ['id', 'title', 'coverageStatus', 'notes']) {
    if (!isNonEmptyString0(family[field])) return reject0('RuleFamilyCoverage.FamilyField', [...familyPath, field], 'family field must be a non-empty string');
  }
  if (!VALID_COVERAGE_STATUSES.has(family.coverageStatus)) return reject0('RuleFamilyCoverage.StatusValue', [...familyPath, 'coverageStatus'], 'coverageStatus must be represented-seed, covered-seed, or planned', { actual: family.coverageStatus });
  for (const field of ['positiveTestCount', 'negativeTestCount', 'mutationTestCount']) {
    if (!Number.isInteger(family[field]) || family[field] < 0) return reject0('RuleFamilyCoverage.Count', [...familyPath, field], 'coverage counts must be nonnegative integers', { actual: family[field] });
  }
  if (family.positiveTestCount === 0) return reject0('RuleFamilyCoverage.NoPositiveTests', [...familyPath, 'positiveTestCount'], 'each represented family must have at least one positive seed test');
  if (family.negativeTestCount === 0) return reject0('RuleFamilyCoverage.NoNegativeTests', [...familyPath, 'negativeTestCount'], 'each represented family must have at least one negative seed test');
  if (family.coverageStatus === 'covered-seed' && family.mutationTestCount === 0) return reject0('RuleFamilyCoverage.NoMutationTests', [...familyPath, 'mutationTestCount'], 'covered-seed families must have mutation seed tests');
  const evidence = validateStringArray0(family.evidenceFiles, [...familyPath, 'evidenceFiles'], true);
  if (evidence.tag === 'reject') return evidence;
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!isPlainObject0(boundary)) return reject0('RuleFamilyCoverage.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('RuleFamilyCoverage.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('RuleFamilyCoverage.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('RuleFamilyCoverage.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('RuleFamilyCoverage.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function validateEvidenceFiles0({ root, ledger }) {
  const evidencePaths = [...new Set(ledger.ruleFamilies.flatMap((family) => family.evidenceFiles))].sort();
  for (const relativePath of evidencePaths) {
    const absolutePath = safeJoin0(root, relativePath);
    if (absolutePath === null) return reject0('RuleFamilyCoverage.EvidencePathUnsafe', [relativePath], 'evidence file path must stay inside repository root');
    try {
      const info = await stat(absolutePath);
      if (!info.isFile()) return reject0('RuleFamilyCoverage.EvidencePathNotFile', [relativePath], 'evidence path must be a file');
    } catch (error) {
      return reject0('RuleFamilyCoverage.EvidencePathMissing', [relativePath], 'evidence file is missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', evidenceFileCount: evidencePaths.length };
}

function validateStringArray0(value, pathArray, nonEmpty = false) {
  if (!Array.isArray(value)) return reject0('RuleFamilyCoverage.StringArray', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('RuleFamilyCoverage.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!isNonEmptyString0(value[index])) return reject0('RuleFamilyCoverage.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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

function safeJoin0(root, relativePath) {
  if (!isNonEmptyString0(relativePath) || path.isAbsolute(relativePath)) return null;
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
}

function sameArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
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
  const options = { root: process.cwd(), ledgerPath: LEDGER_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--ledger') options.ledgerPath = requireValue0(argv, ++index, '--ledger');
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
  console.log(`Usage: node pcc-rule-family-coverage0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/rule-family-coverage/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --ledger <path>    Rule-family coverage ledger path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad rule-family coverage CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await CheckRuleFamilyCoverage0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
