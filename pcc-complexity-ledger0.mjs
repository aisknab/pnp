#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckComplexityLedger0';
const VERSION = 0;
const LEDGER_PATH = 'complexity/COMPLEXITY_LEDGER.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/complexity-ledger/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-COMPLEXITY-LEDGER-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_PROOF_IDS = [
  'Complexity.BooleanCircuitSAT.NPComplete',
  'Complexity.LockedNAND.SATThresholdReductionSeed',
  'Complexity.ResidualBandMinimization.ConditionalPolynomial',
  'Complexity.ConstructedSATAlgorithm.ConditionalPolynomial',
  'Complexity.SATInP.ImpliesPEqualsNP',
  'Complexity.PublicEmissionBoundary.NonActivation',
];
const EXPECTED_DERIVED_IDS = [
  'Complexity.Derived.SATInPConditional',
  'Complexity.Derived.PEqualsNPConditional',
];
const EXPECTED_COORDINATES = {
  trustBase: 'PNP-TRUST-BASE-2026-06-27-01',
  minimalKernel: 'PNP-MINIMAL-KERNEL-2026-06-27-01',
  nandSemantics: 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01',
  nandSmallModels: 'PNP-NAND-SMALL-MODELS-2026-06-27-01',
  lockedNANDSATSmallModels: 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01',
  ruleFamilyCoverage: 'PNP-RULE-FAMILY-COVERAGE-2026-06-27-01',
};

export async function CheckComplexityLedger0(options = {}) {
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

    const proofStatusCounts = countBy0(read.ledger.proofObjects.map((object) => object.status));

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'complexity-implication-ledger-accepted-under-public-review-boundary',
      ledgerPath,
      ledgerSha256: sha256Hex0(read.bytes),
      complexityLedgerReady: true,
      fullComplexityImplicationDischarged: false,
      publicTheoremEmissionAllowedByLedger: false,
      proofObjectCount: read.ledger.proofObjects.length,
      proofObjectIds: EXPECTED_PROOF_IDS,
      derivedConditionalConclusionCount: read.ledger.derivedConditionalConclusions.length,
      proofStatusCounts,
      evidenceFileCount: evidence.evidenceFileCount,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('ComplexityLedger.UnhandledException', [], 'complexity ledger checker threw unexpectedly', normalizeError0(error)));
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
    return reject0('ComplexityLedger.ReadOrParseFailed', [ledgerPath], 'could not read or parse complexity ledger JSON', normalizeError0(error));
  }
}

function validateLedger0(ledger) {
  if (!plain0(ledger)) return reject0('ComplexityLedger.Shape', [], 'ledger must be an object');
  if (ledger.kind !== 'PNPComplexityLedger0') return reject0('ComplexityLedger.Kind', ['kind'], 'ledger kind mismatch');
  if (ledger.version !== VERSION) return reject0('ComplexityLedger.Version', ['version'], 'ledger version mismatch');
  if (ledger.coordinate !== EXPECTED_COORDINATE) return reject0('ComplexityLedger.Coordinate', ['coordinate'], 'ledger coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: ledger.coordinate });
  if (ledger.status !== 'complexity-ledger-seed-ready') return reject0('ComplexityLedger.Status', ['status'], 'ledger status mismatch');
  if (ledger.complexityLedgerReady !== true) return reject0('ComplexityLedger.ReadyFlag', ['complexityLedgerReady'], 'complexityLedgerReady must be true');
  if (ledger.fullComplexityImplicationDischarged !== false) return reject0('ComplexityLedger.FullDischargeFlag', ['fullComplexityImplicationDischarged'], 'seed complexity ledger cannot claim full implication discharge');
  if (ledger.publicTheoremEmissionAllowedByLedger !== false) return reject0('ComplexityLedger.PublicEmissionByLedgerFlag', ['publicTheoremEmissionAllowedByLedger'], 'complexity ledger must not allow public theorem emission');

  const boundary = validateBoundary0(ledger.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  const coordinates = validateLinkedCoordinates0(ledger.linkedCoordinates);
  if (coordinates.tag === 'reject') return coordinates;

  if (!Array.isArray(ledger.proofObjects)) return reject0('ComplexityLedger.ProofObjectsShape', ['proofObjects'], 'proofObjects must be an array');
  const proofIds = ledger.proofObjects.map((object) => object?.id);
  if (!sameArray0(proofIds, EXPECTED_PROOF_IDS)) return reject0('ComplexityLedger.ProofObjectIds', ['proofObjects'], 'proof object ids must stay exact and ordered', { expected: EXPECTED_PROOF_IDS, actual: proofIds });

  const knownIds = new Set(proofIds);
  for (let index = 0; index < ledger.proofObjects.length; index += 1) {
    const object = ledger.proofObjects[index];
    const objectPath = ['proofObjects', index];
    const check = validateProofObject0(object, objectPath, knownIds, index);
    if (check.tag === 'reject') return check;
  }

  if (!Array.isArray(ledger.derivedConditionalConclusions)) return reject0('ComplexityLedger.DerivedShape', ['derivedConditionalConclusions'], 'derivedConditionalConclusions must be an array');
  const derivedIds = ledger.derivedConditionalConclusions.map((conclusion) => conclusion?.id);
  if (!sameArray0(derivedIds, EXPECTED_DERIVED_IDS)) return reject0('ComplexityLedger.DerivedIds', ['derivedConditionalConclusions'], 'derived conditional ids must stay exact and ordered', { expected: EXPECTED_DERIVED_IDS, actual: derivedIds });
  for (let index = 0; index < ledger.derivedConditionalConclusions.length; index += 1) {
    const conclusion = ledger.derivedConditionalConclusions[index];
    const conclusionPath = ['derivedConditionalConclusions', index];
    if (!plain0(conclusion)) return reject0('ComplexityLedger.DerivedConclusionShape', conclusionPath, 'derived conclusion must be an object');
    if (!nonempty0(conclusion.statement)) return reject0('ComplexityLedger.DerivedStatement', [...conclusionPath, 'statement'], 'derived conclusion statement must be non-empty');
    if (conclusion.currentlyActivated !== false) return reject0('ComplexityLedger.DerivedActivation', [...conclusionPath, 'currentlyActivated'], 'derived conclusions must not be activated in this seed ledger');
    const deps = validateStringArray0(conclusion.dependsOn, [...conclusionPath, 'dependsOn'], true);
    if (deps.tag === 'reject') return deps;
    for (const dep of conclusion.dependsOn) {
      if (!knownIds.has(dep)) return reject0('ComplexityLedger.DerivedUnknownDependency', [...conclusionPath, 'dependsOn'], 'derived conclusion depends on unknown proof object', { dep });
    }
  }

  const audit = validateAudit0(ledger.audit);
  if (audit.tag === 'reject') return audit;

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('ComplexityLedger.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('ComplexityLedger.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('ComplexityLedger.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('ComplexityLedger.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('ComplexityLedger.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

function validateLinkedCoordinates0(coordinates) {
  if (!plain0(coordinates)) return reject0('ComplexityLedger.LinkedCoordinatesShape', ['linkedCoordinates'], 'linkedCoordinates must be an object');
  for (const [key, expected] of Object.entries(EXPECTED_COORDINATES)) {
    if (coordinates[key] !== expected) return reject0('ComplexityLedger.LinkedCoordinate', ['linkedCoordinates', key], 'linked coordinate mismatch', { expected, actual: coordinates[key] });
  }
  return { tag: 'accept' };
}

function validateProofObject0(object, objectPath, knownIds, index) {
  if (!plain0(object)) return reject0('ComplexityLedger.ProofObjectShape', objectPath, 'proof object must be an object');
  for (const field of ['id', 'statement', 'status', 'proofRule', 'machineCheckStatus']) {
    if (!nonempty0(object[field])) return reject0('ComplexityLedger.ProofObjectField', [...objectPath, field], 'proof object field must be a non-empty string');
  }
  const premiseCheck = validateStringArray0(object.premiseIds, [...objectPath, 'premiseIds'], false);
  if (premiseCheck.tag === 'reject') return premiseCheck;
  for (const premiseId of object.premiseIds) {
    if (!knownIds.has(premiseId)) return reject0('ComplexityLedger.UnknownPremise', [...objectPath, 'premiseIds'], 'proof object references unknown premise', { premiseId });
    const premiseIndex = EXPECTED_PROOF_IDS.indexOf(premiseId);
    if (premiseIndex >= index) return reject0('ComplexityLedger.ForwardPremise', [...objectPath, 'premiseIds'], 'proof object premises must point to earlier proof objects', { premiseId, index, premiseIndex });
  }
  const evidenceCheck = validateStringArray0(object.evidenceFiles, [...objectPath, 'evidenceFiles'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;
  if (object.status === 'machine-checked-seed' && !object.machineCheckStatus.startsWith('checked-by-')) return reject0('ComplexityLedger.SeedCheckStatus', [...objectPath, 'machineCheckStatus'], 'machine-checked seed proof objects must name their checker');
  if (object.status === 'conditional-proof-object' && object.machineCheckStatus !== 'represented-not-activated') return reject0('ComplexityLedger.ConditionalStatus', [...objectPath, 'machineCheckStatus'], 'conditional proof objects must remain represented-not-activated');
  return { tag: 'accept' };
}

function validateAudit0(audit) {
  if (!plain0(audit)) return reject0('ComplexityLedger.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-complexity-ledger0.mjs',
    command: 'npm run complexity:ledger',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (audit[key] !== expected) return reject0('ComplexityLedger.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: audit[key] });
  }
  return { tag: 'accept' };
}

async function validateEvidenceFiles0({ root, ledger }) {
  const evidencePaths = [...new Set(ledger.proofObjects.flatMap((object) => object.evidenceFiles))].sort();
  for (const relativePath of evidencePaths) {
    const absolutePath = safeJoin0(root, relativePath);
    if (absolutePath === null) return reject0('ComplexityLedger.EvidencePathUnsafe', [relativePath], 'evidence file path must stay inside repository root');
    try {
      const info = await stat(absolutePath);
      if (!info.isFile()) return reject0('ComplexityLedger.EvidencePathNotFile', [relativePath], 'evidence path must be a file');
    } catch (error) {
      return reject0('ComplexityLedger.EvidencePathMissing', [relativePath], 'evidence file is missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', evidenceFileCount: evidencePaths.length };
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('ComplexityLedger.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('ComplexityLedger.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!nonempty0(value[index])) return reject0('ComplexityLedger.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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
  if (!nonempty0(relativePath) || path.isAbsolute(relativePath)) return null;
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
}

function countBy0(values) {
  const map = new Map();
  for (const value of values) map.set(value, (map.get(value) ?? 0) + 1);
  return Object.fromEntries([...map.entries()].sort(([left], [right]) => left.localeCompare(right)));
}

function sameArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function plain0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function nonempty0(value) {
  return typeof value === 'string' && value.length > 0;
}

function sha256Hex0(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
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
  console.log(`Usage: node pcc-complexity-ledger0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/complexity-ledger/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --ledger <path>    Complexity ledger path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad complexity ledger CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckComplexityLedger0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
