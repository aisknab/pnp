#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { RunLockedNANDSATSmallModels0 } from './semantics/locked-nand-sat-small-models.mjs';

const CHECKER = 'CheckLockedNANDSATSmallModels0';
const VERSION = 0;
const CONFIG_PATH = 'semantics/locked-nand-sat-small-models-config.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/locked-nand-sat-small-models/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01';
const EXPECTED_SEMANTICS_COORDINATE = 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01';
const EXPECTED_SMALL_MODELS_COORDINATE = 'PNP-NAND-SMALL-MODELS-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_CHECKS = [
  'brute-force CNF SAT over all assignments',
  'locked NAND final-output construction validates as a NANDDirectWireWord0',
  'constructed truth table is nonzero iff CNF is satisfiable',
  'small-model exact minimum for final output is found inside configured gate bound',
  'threshold predicate agrees with brute-force SAT',
  'unsatisfiable contradiction pairs have zero final output and baseline minimum',
  'satisfiable unit formulas have positive final-output minimum',
  'public theorem emission remains disabled',
];

export async function CheckLockedNANDSATSmallModels0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const configPath = options.configPath ?? CONFIG_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const configRead = await readConfig0({ root, configPath, override: options.configOverride });
    if (configRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, configRead);

    const configCheck = validateConfig0(configRead.config);
    if (configCheck.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, configCheck);

    const audit = RunLockedNANDSATSmallModels0(configRead.config);
    if (audit.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, promoteReject0(audit));

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      semanticsCoordinate: EXPECTED_SEMANTICS_COORDINATE,
      smallModelsCoordinate: EXPECTED_SMALL_MODELS_COORDINATE,
      claimStatus: 'locked-nand-sat-small-models-seed-accepted',
      configPath,
      configSha256: sha256Hex0(configRead.bytes),
      satSmallModelsReady: true,
      fullLockedNANDThresholdCoverageProved: false,
      exhaustiveWithinConfiguredFormulaUniverse: true,
      formulaCount: audit.formulaCount,
      satFormulaCount: audit.satFormulaCount,
      unsatFormulaCount: audit.unsatFormulaCount,
      maxVariables: audit.maxVariables,
      maxExactSearchGates: audit.maxExactSearchGates,
      thresholdModel: audit.thresholdModel,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('LockedNANDSAT.UnhandledException', [], 'locked NAND SAT small-model checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readConfig0({ root, configPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', config: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, configPath));
    return { tag: 'accept', config: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('LockedNANDSAT.ConfigReadOrParseFailed', [configPath], 'could not read or parse locked NAND SAT small-model config JSON', normalizeError0(error));
  }
}

function validateConfig0(config) {
  if (!plain0(config)) return reject0('LockedNANDSAT.ConfigShape', [], 'config must be an object');
  if (config.kind !== 'PNPLockedNANDSATSmallModelsConfig0') return reject0('LockedNANDSAT.ConfigKind', ['kind'], 'config kind mismatch');
  if (config.version !== VERSION) return reject0('LockedNANDSAT.ConfigVersion', ['version'], 'config version mismatch');
  if (config.coordinate !== EXPECTED_COORDINATE) return reject0('LockedNANDSAT.ConfigCoordinate', ['coordinate'], 'config coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: config.coordinate });
  if (config.status !== 'locked-nand-sat-small-models-seed-ready') return reject0('LockedNANDSAT.ConfigStatus', ['status'], 'config status mismatch');
  if (config.semanticsCoordinate !== EXPECTED_SEMANTICS_COORDINATE) return reject0('LockedNANDSAT.SemanticsCoordinate', ['semanticsCoordinate'], 'linked semantics coordinate mismatch');
  if (config.smallModelsCoordinate !== EXPECTED_SMALL_MODELS_COORDINATE) return reject0('LockedNANDSAT.SmallModelsCoordinate', ['smallModelsCoordinate'], 'linked small-model coordinate mismatch');
  if (config.satSmallModelsReady !== true) return reject0('LockedNANDSAT.ReadyFlag', ['satSmallModelsReady'], 'satSmallModelsReady must be true');
  if (config.fullLockedNANDThresholdCoverageProved !== false) return reject0('LockedNANDSAT.FullThresholdCoverageFlag', ['fullLockedNANDThresholdCoverageProved'], 'seed locked-NAND SAT audit cannot claim full threshold coverage');
  if (config.exhaustiveWithinConfiguredFormulaUniverse !== true) return reject0('LockedNANDSAT.ExhaustiveFormulaUniverseFlag', ['exhaustiveWithinConfiguredFormulaUniverse'], 'configured formula universe must be exhaustive');

  const boundary = validateBoundary0(config.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(config.formulaUniverse)) return reject0('LockedNANDSAT.FormulaUniverseShape', ['formulaUniverse'], 'formulaUniverse must be an object');
  if (config.formulaUniverse.maxVariables !== 2) return reject0('LockedNANDSAT.MaxVariables', ['formulaUniverse', 'maxVariables'], 'seed maxVariables must be 2', { actual: config.formulaUniverse.maxVariables });
  if (!sameArray0(config.formulaUniverse.clauseKinds, ['single literal unit clause', 'single-variable contradiction pair'])) return reject0('LockedNANDSAT.ClauseKinds', ['formulaUniverse', 'clauseKinds'], 'clauseKinds mismatch');
  if (config.formulaUniverse.includePositiveUnits !== true || config.formulaUniverse.includeNegativeUnits !== true || config.formulaUniverse.includeContradictions !== true) return reject0('LockedNANDSAT.FormulaUniverseFlags', ['formulaUniverse'], 'formula universe include flags must be true');

  if (!plain0(config.thresholdModel)) return reject0('LockedNANDSAT.ThresholdShape', ['thresholdModel'], 'thresholdModel must be an object');
  if (config.thresholdModel.kind !== 'LockedFinalOutputNonconstantSeed0') return reject0('LockedNANDSAT.ThresholdKind', ['thresholdModel', 'kind'], 'threshold model kind mismatch');
  if (config.thresholdModel.baselineMinimum !== 0) return reject0('LockedNANDSAT.BaselineMinimum', ['thresholdModel', 'baselineMinimum'], 'seed baseline minimum must be 0');
  if (config.thresholdModel.thresholdPredicate !== 'exactMinimum(finalLockedOutput) > baselineMinimum') return reject0('LockedNANDSAT.ThresholdPredicate', ['thresholdModel', 'thresholdPredicate'], 'threshold predicate mismatch');
  if (config.thresholdModel.finalLock !== 'z') return reject0('LockedNANDSAT.FinalLock', ['thresholdModel', 'finalLock'], 'final lock must be z');
  if (config.thresholdModel.maxExactSearchGates !== 3) return reject0('LockedNANDSAT.MaxExactSearchGates', ['thresholdModel', 'maxExactSearchGates'], 'max exact search gates must be 3');

  if (!sameArray0(config.checks, EXPECTED_CHECKS)) return reject0('LockedNANDSAT.CheckList', ['checks'], 'configured checks must stay exact and ordered', { expected: EXPECTED_CHECKS, actual: config.checks });

  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-locked-nand-sat-small-models0.mjs',
    command: 'npm run semantics:locked-nand:sat-small-models',
    expectedAcceptTag: 'accept',
  };
  if (!plain0(config.audit)) return reject0('LockedNANDSAT.AuditShape', ['audit'], 'audit must be an object');
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (config.audit[key] !== expected) return reject0('LockedNANDSAT.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: config.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('LockedNANDSAT.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('LockedNANDSAT.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('LockedNANDSAT.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('LockedNANDSAT.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('LockedNANDSAT.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

function promoteReject0(record) {
  return reject0(record.coord ?? 'LockedNANDSAT.InnerReject', record.path ?? [], record.witness?.reason ?? 'inner locked NAND SAT small-model audit rejected', { inner: record });
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

function sameArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function plain0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function sha256Hex0(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}

function parseArgs0(argv) {
  const options = { root: process.cwd(), configPath: CONFIG_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--config') options.configPath = requireValue0(argv, ++index, '--config');
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
  console.log(`Usage: node pcc-locked-nand-sat-small-models0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/locked-nand-sat-small-models/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --config <path>    Config path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad locked NAND SAT small-model CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckLockedNANDSATSmallModels0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
