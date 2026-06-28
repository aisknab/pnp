#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  compatibleReplacement0,
  flattenedTruthTable0,
  makeBoundarySource0,
  makeConstSource0,
  makeGateSource0,
  makeNANDWord0,
  sizeOfNANDWord0,
  validateNANDWord0,
} from './semantics/nand-direct-wire-reference.mjs';

const CHECKER = 'CheckNANDDirectWireSemantics0';
const VERSION = 0;
const SPEC_PATH = 'semantics/nand-direct-wire-spec.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/nand-direct-wire-semantics/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_CONCEPTS = [
  'NAND gate syntax',
  'open carrier boundary tuple',
  'constant sources',
  'direct-wire topological gate order',
  'multi-output tuple semantics',
  'truth-table evaluation',
  'word size as NAND gate count',
  'truth-table equivalence',
  'compatible replacement semantics for same boundary and output arity',
];

export async function CheckNANDDirectWireSemantics0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const specPath = options.specPath ?? SPEC_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const specRead = await readSpec0({ root, specPath, override: options.specOverride });
    if (specRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, specRead);

    const validation = validateSpec0(specRead.spec);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, validation);

    const examples = runSemanticExamples0();
    if (examples.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, examples);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'nand-direct-wire-semantics-seed-accepted',
      specPath,
      specSha256: sha256Hex0(specRead.bytes),
      semanticsReady: true,
      fullSemanticsCoverageProved: false,
      coveredConceptCount: EXPECTED_CONCEPTS.length,
      exampleCount: examples.exampleCount,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('NANDSemantics.UnhandledException', [], 'NAND direct-wire semantics checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readSpec0({ root, specPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', spec: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, specPath));
    return { tag: 'accept', spec: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('NANDSemantics.SpecReadOrParseFailed', [specPath], 'could not read or parse NAND semantics spec JSON', normalizeError0(error));
  }
}

function validateSpec0(spec) {
  if (!plain0(spec)) return reject0('NANDSemantics.SpecShape', [], 'spec must be an object');
  if (spec.kind !== 'PNPNANDDirectWireSemantics0') return reject0('NANDSemantics.SpecKind', ['kind'], 'spec kind mismatch');
  if (spec.version !== VERSION) return reject0('NANDSemantics.SpecVersion', ['version'], 'spec version mismatch');
  if (spec.coordinate !== EXPECTED_COORDINATE) return reject0('NANDSemantics.SpecCoordinate', ['coordinate'], 'spec coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: spec.coordinate });
  if (spec.status !== 'nand-direct-wire-semantics-seed-ready') return reject0('NANDSemantics.SpecStatus', ['status'], 'spec status mismatch');
  if (spec.semanticsReady !== true) return reject0('NANDSemantics.ReadyFlag', ['semanticsReady'], 'semanticsReady must be true');
  if (spec.fullSemanticsCoverageProved !== false) return reject0('NANDSemantics.FullCoverageFlag', ['fullSemanticsCoverageProved'], 'seed semantics cannot claim full semantics coverage');

  const boundary = validateBoundary0(spec.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!sameArray0(spec.coveredConcepts, EXPECTED_CONCEPTS)) return reject0('NANDSemantics.CoveredConcepts', ['coveredConcepts'], 'covered concepts must stay exact and ordered', { expected: EXPECTED_CONCEPTS, actual: spec.coveredConcepts });
  if (!sameArray0(spec.sourceKinds, ['boundary', 'const', 'gate'])) return reject0('NANDSemantics.SourceKinds', ['sourceKinds'], 'sourceKinds must stay exact');

  if (!plain0(spec.wordSchema)) return reject0('NANDSemantics.WordSchema', ['wordSchema'], 'wordSchema must be an object');
  if (spec.wordSchema.kind !== 'NANDDirectWireWord0') return reject0('NANDSemantics.WordSchemaKind', ['wordSchema', 'kind'], 'word schema kind mismatch');
  if (!sameArray0(spec.wordSchema.requiredFields, ['boundary', 'gates', 'outputs'])) return reject0('NANDSemantics.WordSchemaRequiredFields', ['wordSchema', 'requiredFields'], 'word schema required fields mismatch');

  if (!plain0(spec.audit)) return reject0('NANDSemantics.AuditShape', ['audit'], 'audit field must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-nand-direct-wire-semantics0.mjs',
    command: 'npm run semantics:nand',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (spec.audit[key] !== expected) return reject0('NANDSemantics.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: spec.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('NANDSemantics.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('NANDSemantics.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('NANDSemantics.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('NANDSemantics.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('NANDSemantics.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

function runSemanticExamples0() {
  const nand2 = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [{ id: 'g0', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('y') }],
    outputs: [makeGateSource0('g0')],
  });
  const not1 = makeNANDWord0({
    boundary: ['x'],
    gates: [{ id: 'notx', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('x') }],
    outputs: [makeGateSource0('notx')],
  });
  const and2 = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [
      { id: 'n0', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('y') },
      { id: 'a0', op: 'NAND', left: makeGateSource0('n0'), right: makeGateSource0('n0') },
    ],
    outputs: [makeGateSource0('a0')],
  });
  const const1 = makeNANDWord0({ boundary: [], gates: [], outputs: [makeConstSource0(1)] });

  const examples = [
    ['nand2', nand2, [1, 1, 1, 0], 1],
    ['not1', not1, [1, 0], 1],
    ['and2', and2, [0, 0, 0, 1], 2],
    ['const1', const1, [1], 0],
  ];

  for (const [id, word, expectedBits, expectedSize] of examples) {
    const validation = validateNANDWord0(word);
    if (validation.tag === 'reject') return reject0('NANDSemantics.ExampleInvalid', ['examples', id], 'seed example word is invalid', { validation });
    const table = flattenedTruthTable0(word);
    if (table.tag === 'reject') return table;
    if (!sameArray0(table.bits, expectedBits)) return reject0('NANDSemantics.ExampleTruthTableMismatch', ['examples', id], 'seed example truth table mismatch', { expectedBits, actualBits: table.bits });
    const size = sizeOfNANDWord0(word);
    if (size.tag === 'reject') return size;
    if (size.size !== expectedSize) return reject0('NANDSemantics.ExampleSizeMismatch', ['examples', id], 'seed example size mismatch', { expectedSize, actualSize: size.size });
  }

  const support = and2;
  const replacement = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [
      { id: 'n0', op: 'NAND', left: makeBoundarySource0('y'), right: makeBoundarySource0('x') },
      { id: 'a0', op: 'NAND', left: makeGateSource0('n0'), right: makeGateSource0('n0') },
    ],
    outputs: [makeGateSource0('a0')],
  });
  const compatible = compatibleReplacement0(support, replacement);
  if (compatible.tag === 'reject') return reject0('NANDSemantics.ReplacementExampleFailed', ['replacement'], 'equivalent NAND replacement example must accept', { compatible });

  const badFutureGate = makeNANDWord0({
    boundary: ['x'],
    gates: [{ id: 'g0', op: 'NAND', left: makeGateSource0('future'), right: makeBoundarySource0('x') }],
    outputs: [makeGateSource0('g0')],
  });
  const badValidation = validateNANDWord0(badFutureGate);
  if (badValidation.tag !== 'reject') return reject0('NANDSemantics.BadFutureGateAccepted', ['examples', 'badFutureGate'], 'future gate reference must reject');

  return { tag: 'accept', exampleCount: examples.length + 2 };
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
  const options = { root: process.cwd(), specPath: SPEC_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--spec') options.specPath = requireValue0(argv, ++index, '--spec');
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
  console.log(`Usage: node pcc-nand-direct-wire-semantics0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/nand-direct-wire-semantics/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --spec <path>      Semantics spec path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad NAND semantics CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }

  const verdict = await CheckNANDDirectWireSemantics0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
