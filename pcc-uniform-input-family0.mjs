#!/usr/bin/env node

import { EnforceHistoricalReplayCli0, LegacyReplayRequiredReject0 } from './pcc-legacy-replay-gate0.mjs';

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckUniformInputFamily0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_INPUT_FAMILY.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const OUT = 'artifacts/uniform-input-family/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_LINKED_GAPS = [
  'GAP-001-UnrestrictedFinalSoundness',
  'GAP-003-BoundedSmallModelsNotUniformProof',
  'GAP-004-FiniteToUnboundedUniformity',
];

export async function CheckUniformInputFamily0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  if (options.historicalReplay !== true) return write0(root, outputPath, writeOutput, LegacyReplayRequiredReject0(CHECKER, BLOCKERS));
  try {
    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'uniform input family manifest' });
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const targetRead = await readJson0({ root, filePath: options.targetPath ?? TARGET_PATH, override: options.targetOverride, label: 'uniform final soundness target manifest' });
    if (targetRead.tag === 'reject') return write0(root, outputPath, writeOutput, targetRead);

    const targetCheck = validateTarget0(targetRead.value);
    if (targetCheck.tag === 'reject') return write0(root, outputPath, writeOutput, targetCheck);

    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const exampleCheck = validateExamples0(manifestRead.value);
    if (exampleCheck.tag === 'reject') return write0(root, outputPath, writeOutput, exampleCheck);

    const evidence = await digestEvidence0({ root, paths: manifestRead.value.evidenceSurfaces });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      ufsTargetCoordinate: TARGET_COORD,
      ufsObligationId: 'UFS-001-InputFamilyUniformity',
      claimStatus: 'ufs-001-input-family-uniformity-accepted',
      inputFamilyUniformityAccepted: true,
      ufs001InputFamilyUniformityDischarged: true,
      allFiniteSizesCovered: true,
      schemaUniformAcrossSizes: true,
      finiteInstanceList: false,
      boundedEnumerationOnly: false,
      positiveExampleCount: manifestRead.value.positiveExamples.length,
      negativeExampleCount: manifestRead.value.negativeExamples.length,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      targetSha256: sha256Hex0(targetRead.bytes),
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      uniformFinalSoundnessProved: false,
      unrestrictedFinalSoundnessDischarged: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      nextProofSurface: 'pcc-uniform-locked-nand-construction0.mjs',
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UniformInputFamily.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function CheckNANDCircuitInputFamilyMember0(circuit) {
  return validateNANDCircuit0(circuit);
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UniformInputFamily.ManifestShape', [], 'manifest must be an object');
  const exact = [
    ['kind', 'PNPUniformInputFamily0'],
    ['version', VERSION],
    ['coordinate', COORD],
    ['status', 'uniform-input-family-accepted'],
    ['ufsTargetCoordinate', TARGET_COORD],
    ['ufsObligationId', 'UFS-001-InputFamilyUniformity'],
  ];
  for (const [key, expected] of exact) {
    if (manifest[key] !== expected) return reject0('UniformInputFamily.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  }

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  const bools = {
    inputFamilyUniformityAccepted: true,
    ufs001InputFamilyUniformityDischarged: true,
    uniformFinalSoundnessProved: false,
    unrestrictedFinalSoundnessDischarged: false,
    publicTheoremEmissionAllowedByInputFamily: false,
  };
  for (const [key, expected] of Object.entries(bools)) {
    if (manifest[key] !== expected) return reject0('UniformInputFamily.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  }

  if (!plain0(manifest.inputFamily)) return reject0('UniformInputFamily.InputFamilyShape', ['inputFamily'], 'inputFamily must be an object');
  const family = manifest.inputFamily;
  const familyBools = {
    allFiniteSizesCovered: true,
    schemaUniformAcrossSizes: true,
    finiteInstanceList: false,
    boundedEnumerationOnly: false,
    requiresFutureSizeBound: false,
  };
  for (const [key, expected] of Object.entries(familyBools)) {
    if (family[key] !== expected) return reject0(key === 'finiteInstanceList' ? 'UniformInputFamily.ManifestFiniteList' : 'UniformInputFamily.FamilyBoolean', ['inputFamily', key], 'input family boolean mismatch', { expected, actual: family[key] });
  }
  if (family.id !== 'AllFiniteSingleOutputNANDCircuits0') return reject0('UniformInputFamily.FamilyId', ['inputFamily', 'id'], 'unexpected input family id', { actual: family.id });
  if (!String(family.quantifier ?? '').includes('every finite')) return reject0('UniformInputFamily.FamilyQuantifier', ['inputFamily', 'quantifier'], 'input family must quantify over every finite input');

  if (!plain0(manifest.schema)) return reject0('UniformInputFamily.SchemaShape', ['schema'], 'schema must be an object');
  const schema = manifest.schema;
  if (schema.kind !== 'NANDCircuit0' || schema.version !== 0) return reject0('UniformInputFamily.SchemaKind', ['schema'], 'schema must describe NANDCircuit0 version 0');
  if (!Array.isArray(schema.sourceKinds) || stableStringify0(schema.sourceKinds) !== stableStringify0(['input', 'const', 'gate'])) return reject0('UniformInputFamily.SourceKinds', ['schema', 'sourceKinds'], 'source kinds mismatch');
  if (!String(schema.membershipTimeBound ?? '').includes('O(')) return reject0('UniformInputFamily.PolynomialMembership', ['schema', 'membershipTimeBound'], 'membership check must declare polynomial bound');
  if (!String(schema.gateRule ?? '').includes('j < i')) return reject0('UniformInputFamily.TopologicalGateRule', ['schema', 'gateRule'], 'gate rule must require topological references');

  const claims = manifest.uniformityClaims;
  if (!plain0(claims)) return reject0('UniformInputFamily.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(claims)) {
    if (value !== true) return reject0('UniformInputFamily.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  }

  if (!sameArray0(manifest.linkedGaps, REQUIRED_LINKED_GAPS)) return reject0('UniformInputFamily.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_LINKED_GAPS, actual: manifest.linkedGaps });
  for (const key of ['evidenceSurfaces', 'nonClaims']) {
    const check = validateStringArray0(manifest[key], [key], true);
    if (check.tag === 'reject') return check;
  }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('UniformInputFamily.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('UniformInputFamily.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-uniform-input-family0.mjs' || manifest.audit.test !== 'audits/uniform-input-family0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('UniformInputFamily.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('UniformInputFamily.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const obligations = Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : [];
  const ufs001 = obligations.find((entry) => entry?.id === 'UFS-001-InputFamilyUniformity');
  if (!plain0(ufs001)) return reject0('UniformInputFamily.TargetMissingUFS001', ['target', 'requiredUniformObligations'], 'UFS-001 target missing');
  if (ufs001.requiredForDischarge !== true) return reject0('UniformInputFamily.TargetUFS001NotRequired', ['target', 'requiredUniformObligations', 'UFS-001'], 'UFS-001 must be required for discharge');
  if (ufs001.futureChecker !== 'pcc-uniform-input-family0.mjs') return reject0('UniformInputFamily.TargetUFS001Checker', ['target', 'requiredUniformObligations', 'UFS-001', 'futureChecker'], 'UFS-001 target checker mismatch', { actual: ufs001.futureChecker });
  return { tag: 'accept' };
}

function validateExamples0(manifest) {
  for (let i = 0; i < manifest.positiveExamples.length; i += 1) {
    const example = manifest.positiveExamples[i];
    const out = validateNANDCircuit0(example.circuit);
    if (out.tag !== 'accept') return reject0('UniformInputFamily.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out });
  }
  for (let i = 0; i < manifest.negativeExamples.length; i += 1) {
    const example = manifest.negativeExamples[i];
    if (example.circuit !== undefined) {
      const out = validateNANDCircuit0(example.circuit);
      if (out.tag !== 'reject') return reject0('UniformInputFamily.NegativeExampleAccepted', ['negativeExamples', i], 'negative example accepted', { exampleId: example.id });
      if (example.expectedRejectCoord && out.coord !== example.expectedRejectCoord) return reject0('UniformInputFamily.NegativeExampleCoord', ['negativeExamples', i, 'expectedRejectCoord'], 'negative example reject coordinate mismatch', { expected: example.expectedRejectCoord, actual: out.coord });
    }
  }
  return { tag: 'accept' };
}

function validateNANDCircuit0(circuit) {
  if (!plain0(circuit)) return reject0('UniformInputFamily.CircuitShape', [], 'circuit must be an object');
  if (circuit.kind !== 'NANDCircuit0') return reject0('UniformInputFamily.CircuitKind', ['kind'], 'circuit kind mismatch', { actual: circuit.kind });
  if (circuit.version !== 0) return reject0('UniformInputFamily.CircuitVersion', ['version'], 'circuit version mismatch', { actual: circuit.version });
  if (!safeNat0(circuit.inputCount)) return reject0('UniformInputFamily.InputCount', ['inputCount'], 'inputCount must be a safe nonnegative integer', { actual: circuit.inputCount });
  if (!Array.isArray(circuit.gates)) return reject0('UniformInputFamily.GatesArray', ['gates'], 'gates must be an array');
  for (let i = 0; i < circuit.gates.length; i += 1) {
    const gate = circuit.gates[i];
    if (!plain0(gate)) return reject0('UniformInputFamily.GateShape', ['gates', i], 'gate must be an object');
    if (gate.op !== 'NAND') return reject0('UniformInputFamily.GateOp', ['gates', i, 'op'], 'gate op must be NAND', { actual: gate.op });
    const left = validateSource0(gate.left, { inputCount: circuit.inputCount, gateBound: i, pathArray: ['gates', i, 'left'] });
    if (left.tag === 'reject') return left;
    const right = validateSource0(gate.right, { inputCount: circuit.inputCount, gateBound: i, pathArray: ['gates', i, 'right'] });
    if (right.tag === 'reject') return right;
  }
  const output = validateSource0(circuit.output, { inputCount: circuit.inputCount, gateBound: circuit.gates.length, pathArray: ['output'] });
  if (output.tag === 'reject') return output;
  const gateCount = circuit.gates.length;
  return { tag: 'accept', kind: 'accept', checker: 'CheckNANDCircuitInputFamilyMember0', inputCount: circuit.inputCount, gateCount, sourceReferenceCount: gateCount * 2 + 1, sizeMetric: circuit.inputCount + gateCount + gateCount * 2 + 1 };
}

function validateSource0(source, { inputCount, gateBound, pathArray }) {
  if (!plain0(source)) return reject0('UniformInputFamily.SourceShape', pathArray, 'source must be an object');
  if (source.kind === 'input') {
    if (!safeNat0(source.index)) return reject0('UniformInputFamily.SourceInputIndex', [...pathArray, 'index'], 'input source index must be safe nat', { actual: source.index });
    if (source.index >= inputCount) return reject0('UniformInputFamily.SourceInputOutOfRange', [...pathArray, 'index'], 'input source index out of range', { inputCount, actual: source.index });
    return { tag: 'accept' };
  }
  if (source.kind === 'const') {
    if (source.value !== 0 && source.value !== 1) return reject0('UniformInputFamily.SourceConstValue', [...pathArray, 'value'], 'const source must be 0 or 1', { actual: source.value });
    return { tag: 'accept' };
  }
  if (source.kind === 'gate') {
    if (!safeNat0(source.index)) return reject0('UniformInputFamily.SourceGateIndex', [...pathArray, 'index'], 'gate source index must be safe nat', { actual: source.index });
    if (source.index >= gateBound) return reject0('UniformInputFamily.SourceFutureGate', [...pathArray, 'index'], 'gate source must reference an earlier gate', { gateBound, actual: source.index });
    return { tag: 'accept' };
  }
  return reject0('UniformInputFamily.SourceKind', [...pathArray, 'kind'], 'unknown source kind', { actual: source.kind });
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('UniformInputFamily.BoundaryShape', ['claimBoundary'], 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('UniformInputFamily.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false');
  if (boundary.finalTheoremReady !== false) return reject0('UniformInputFamily.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('UniformInputFamily.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('UniformInputFamily.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, label }) {
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, filePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('UniformInputFamily.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const rel of paths) {
    try {
      const abs = path.join(root, rel);
      const st = await stat(abs);
      if (!st.isFile()) return reject0('UniformInputFamily.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(abs);
      evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length });
    } catch (error) {
      return reject0('UniformInputFamily.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', evidence };
}

function validateStringArray0(value, pathArray, nonempty) {
  if (!Array.isArray(value)) return reject0('UniformInputFamily.ArrayShape', pathArray, 'expected array');
  if (nonempty && value.length === 0) return reject0('UniformInputFamily.ArrayEmpty', pathArray, 'array must be non-empty');
  for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('UniformInputFamily.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string');
  return { tag: 'accept' };
}

async function write0(root, outputPath, writeOutput, verdict) {
  const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null };
  if (writeOutput) {
    const p = path.join(root, outputPath);
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
}

function reject0(coord, pathArray, reason, witness = {}) {
  return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] };
}
function safeNat0(value) { return Number.isSafeInteger(value) && value >= 0; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { EnforceHistoricalReplayCli0({ entrypoint: 'pcc-uniform-input-family0.mjs' }); let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UniformInputFamily.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } options.historicalReplay = true; const verdict = await CheckUniformInputFamily0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
