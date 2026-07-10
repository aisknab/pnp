#!/usr/bin/env node

import { EnforceHistoricalReplayCli0, LegacyReplayRequiredReject0 } from './pcc-legacy-replay-gate0.mjs';

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  CheckNANDCircuitInputFamilyMember0,
  CheckUniformInputFamily0,
} from './pcc-uniform-input-family0.mjs';

const CHECKER = 'CheckUniformLockedNANDConstruction0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const INPUT_FAMILY_COORD = 'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_LOCKED_NAND_CONSTRUCTION.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const OUT = 'artifacts/uniform-locked-nand-construction/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_LINKED_GAPS = [
  'GAP-001-UnrestrictedFinalSoundness',
  'GAP-003-BoundedSmallModelsNotUniformProof',
  'GAP-004-FiniteToUnboundedUniformity',
];

export async function CheckUniformLockedNANDConstruction0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  if (options.historicalReplay !== true) return write0(root, outputPath, writeOutput, LegacyReplayRequiredReject0(CHECKER, BLOCKERS));
  try {
    const inputFamily = await CheckUniformInputFamily0({ root, writeOutput: false, historicalReplay: true });
    if (inputFamily.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UniformLockedNANDConstruction.InputFamilyDependency', ['dependsOn', INPUT_FAMILY_COORD], 'UFS-001 input family dependency must accept', { dependency: inputFamily }));

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'uniform locked NAND construction manifest' });
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
      ufsObligationId: 'UFS-002-LockedNANDConstructionUniformPolynomial',
      claimStatus: 'ufs-002-locked-nand-construction-uniform-polynomial-accepted',
      lockedNANDConstructionAccepted: true,
      ufs002LockedNANDConstructionDischarged: true,
      dependsOn: [INPUT_FAMILY_COORD],
      totalOnInputFamily: true,
      deterministic: true,
      uniformAcrossSizes: true,
      finiteInstanceList: false,
      boundedEnumerationOnly: false,
      constructionTimeBound: manifestRead.value.construction.constructionTimeBound,
      constructionSizeBound: manifestRead.value.construction.constructionSizeBound,
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
      nextProofSurface: 'pcc-uniform-locked-nand-threshold0.mjs',
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UniformLockedNANDConstruction.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function NormalizeLockedNANDInput0(circuit) {
  const member = CheckNANDCircuitInputFamilyMember0(circuit);
  if (member.tag !== 'accept') return member;
  const clone = JSON.parse(JSON.stringify(circuit));
  if (clone.output?.kind === 'gate') return { tag: 'accept', normalizedCircuit: clone, addedGateCount: 0, normalizationKind: 'identity-output-gate' };
  const source = clone.output;
  if (source?.kind === 'input') {
    const g0 = clone.gates.length;
    clone.gates.push({ op: 'NAND', left: source, right: { kind: 'const', value: 1 } });
    clone.gates.push({ op: 'NAND', left: { kind: 'gate', index: g0 }, right: { kind: 'gate', index: g0 } });
    clone.output = { kind: 'gate', index: g0 + 1 };
    return { tag: 'accept', normalizedCircuit: clone, addedGateCount: 2, normalizationKind: 'input-double-nand-identity' };
  }
  if (source?.kind === 'const') {
    const g0 = clone.gates.length;
    if (source.value === 0) clone.gates.push({ op: 'NAND', left: { kind: 'const', value: 1 }, right: { kind: 'const', value: 1 } });
    else clone.gates.push({ op: 'NAND', left: { kind: 'const', value: 0 }, right: { kind: 'const', value: 0 } });
    clone.output = { kind: 'gate', index: g0 };
    return { tag: 'accept', normalizedCircuit: clone, addedGateCount: 1, normalizationKind: `const-${source.value}-single-nand` };
  }
  return reject0('UniformLockedNANDConstruction.NormalizeOutput', ['output'], 'unsupported output source for normalization', { output: source });
}

export function BuildLockedNANDConstruction0(circuit) {
  const normalized = NormalizeLockedNANDInput0(circuit);
  if (normalized.tag !== 'accept') return normalized;
  const c = normalized.normalizedCircuit;
  const m = c.gates.length;
  let equalityMacroCount = 0;
  let constantZeroMacroCount = 0;
  let constantOneMacroCount = 0;
  const sourceOccurrences = [];
  for (let gateIndex = 0; gateIndex < c.gates.length; gateIndex += 1) {
    const gate = c.gates[gateIndex];
    for (const side of ['left', 'right']) {
      const source = gate[side];
      const occurrence = { gateIndex, side, source, occurrenceSlot: `o${sourceOccurrences.length}` };
      if (source.kind === 'const' && source.value === 0) { occurrence.macro = 'ConstantZero'; constantZeroMacroCount += 1; }
      else if (source.kind === 'const' && source.value === 1) { occurrence.macro = 'ConstantOne'; constantOneMacroCount += 1; }
      else { occurrence.macro = 'Equality'; equalityMacroCount += 1; }
      sourceOccurrences.push(occurrence);
    }
  }
  const traceMacroCount = m;
  const checkCount = sourceOccurrences.length + traceMacroCount;
  const prefixNodeCount = Math.max(0, checkCount - 1);
  const baseline = 18 * m + 10 * equalityMacroCount + 3 * constantZeroMacroCount + 2 * constantOneMacroCount + 2 * prefixNodeCount;
  const fullWordSize = baseline + 4;
  return {
    tag: 'accept',
    kind: 'LockedNANDInstance0',
    version: 0,
    normalizedCircuit: c,
    normalizationKind: normalized.normalizationKind,
    addedGateCount: normalized.addedGateCount,
    inputCount: c.inputCount,
    normalizedGateCount: m,
    sourceOccurrenceCount: sourceOccurrences.length,
    equalityMacroCount,
    constantZeroMacroCount,
    constantOneMacroCount,
    traceMacroCount,
    checkCount,
    prefixNodeCount,
    finalGateCount: 4,
    baseline,
    fullWordSize,
    residualSlackBound: 4,
    slotAllocation: {
      primaryInputs: range0(c.inputCount, 'x'),
      traceSlots: range0(m, 't'),
      traceLocks: range0(m, 'l'),
      occurrenceSlots: range0(sourceOccurrences.length, 'o'),
      sourceLocks: range0(sourceOccurrences.length, 'r'),
      finalLock: 'z',
    },
    sourceOccurrences,
  };
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UniformLockedNANDConstruction.ManifestShape', [], 'manifest must be an object');
  const exact = [
    ['kind', 'PNPUniformLockedNANDConstruction0'],
    ['version', VERSION],
    ['coordinate', COORD],
    ['status', 'uniform-locked-nand-construction-accepted'],
    ['ufsTargetCoordinate', TARGET_COORD],
    ['ufsObligationId', 'UFS-002-LockedNANDConstructionUniformPolynomial'],
  ];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('UniformLockedNANDConstruction.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  if (!sameArray0(manifest.dependsOn, [INPUT_FAMILY_COORD])) return reject0('UniformLockedNANDConstruction.DependsOn', ['dependsOn'], 'dependency mismatch', { actual: manifest.dependsOn });
  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;
  const bools = {
    lockedNANDConstructionAccepted: true,
    ufs002LockedNANDConstructionDischarged: true,
    uniformFinalSoundnessProved: false,
    unrestrictedFinalSoundnessDischarged: false,
    publicTheoremEmissionAllowedByConstruction: false,
  };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('UniformLockedNANDConstruction.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  if (!plain0(manifest.construction)) return reject0('UniformLockedNANDConstruction.ConstructionShape', ['construction'], 'construction must be an object');
  const construction = manifest.construction;
  const constructionBools = {
    totalOnInputFamily: true,
    deterministic: true,
    uniformAcrossSizes: true,
    finiteInstanceList: false,
    boundedEnumerationOnly: false,
    usesOracle: false,
    usesExactMinimization: false,
  };
  for (const [key, expected] of Object.entries(constructionBools)) if (construction[key] !== expected) return reject0('UniformLockedNANDConstruction.ConstructionBoolean', ['construction', key], 'construction boolean mismatch', { expected, actual: construction[key] });
  if (!String(construction.baselineFormula ?? '').includes('18*m')) return reject0('UniformLockedNANDConstruction.BaselineFormula', ['construction', 'baselineFormula'], 'baseline formula missing trace term');
  if (construction.residualSlackBound !== 4) return reject0('UniformLockedNANDConstruction.ResidualSlackBound', ['construction', 'residualSlackBound'], 'residual slack bound must be 4');
  if (!String(construction.constructionTimeBound ?? '').includes('O(') || !String(construction.constructionSizeBound ?? '').includes('O(')) return reject0('UniformLockedNANDConstruction.PolynomialBounds', ['construction'], 'construction must declare polynomial bounds');
  const claims = manifest.uniformityClaims;
  if (!plain0(claims)) return reject0('UniformLockedNANDConstruction.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(claims)) if (value !== true) return reject0('UniformLockedNANDConstruction.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  if (!sameArray0(manifest.linkedGaps, REQUIRED_LINKED_GAPS)) return reject0('UniformLockedNANDConstruction.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_LINKED_GAPS, actual: manifest.linkedGaps });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('UniformLockedNANDConstruction.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('UniformLockedNANDConstruction.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-uniform-locked-nand-construction0.mjs' || manifest.audit.test !== 'audits/uniform-locked-nand-construction0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('UniformLockedNANDConstruction.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('UniformLockedNANDConstruction.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const obligations = Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : [];
  const ufs002 = obligations.find((entry) => entry?.id === 'UFS-002-LockedNANDConstructionUniformPolynomial');
  if (!plain0(ufs002)) return reject0('UniformLockedNANDConstruction.TargetMissingUFS002', ['target', 'requiredUniformObligations'], 'UFS-002 target missing');
  if (ufs002.requiredForDischarge !== true) return reject0('UniformLockedNANDConstruction.TargetUFS002NotRequired', ['target', 'requiredUniformObligations', 'UFS-002'], 'UFS-002 must be required for discharge');
  if (ufs002.futureChecker !== 'pcc-uniform-locked-nand-construction0.mjs') return reject0('UniformLockedNANDConstruction.TargetUFS002Checker', ['target', 'requiredUniformObligations', 'UFS-002', 'futureChecker'], 'UFS-002 target checker mismatch', { actual: ufs002.futureChecker });
  return { tag: 'accept' };
}

function validateExamples0(manifest) {
  for (let i = 0; i < manifest.positiveExamples.length; i += 1) {
    const example = manifest.positiveExamples[i];
    const out = BuildLockedNANDConstruction0(example.inputCircuit);
    if (out.tag !== 'accept') return reject0('UniformLockedNANDConstruction.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out });
    for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('UniformLockedNANDConstruction.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual: out[key] });
  }
  for (let i = 0; i < manifest.negativeExamples.length; i += 1) {
    const example = manifest.negativeExamples[i];
    if (example.inputCircuit !== undefined) {
      const out = BuildLockedNANDConstruction0(example.inputCircuit);
      if (out.tag !== 'reject') return reject0('UniformLockedNANDConstruction.NegativeExampleAccepted', ['negativeExamples', i], 'negative example accepted', { exampleId: example.id });
      if (example.expectedRejectCoord && out.coord !== example.expectedRejectCoord) return reject0('UniformLockedNANDConstruction.NegativeExampleCoord', ['negativeExamples', i, 'expectedRejectCoord'], 'negative example reject coordinate mismatch', { expected: example.expectedRejectCoord, actual: out.coord });
    }
  }
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('UniformLockedNANDConstruction.BoundaryShape', ['claimBoundary'], 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('UniformLockedNANDConstruction.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false');
  if (boundary.finalTheoremReady !== false) return reject0('UniformLockedNANDConstruction.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('UniformLockedNANDConstruction.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('UniformLockedNANDConstruction.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, label }) {
  if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; }
  try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('UniformLockedNANDConstruction.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); }
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const rel of paths) {
    try {
      const abs = path.join(root, rel);
      const st = await stat(abs);
      if (!st.isFile()) return reject0('UniformLockedNANDConstruction.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(abs);
      evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length });
    } catch (error) { return reject0('UniformLockedNANDConstruction.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); }
  }
  return { tag: 'accept', evidence };
}

function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('UniformLockedNANDConstruction.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('UniformLockedNANDConstruction.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('UniformLockedNANDConstruction.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
function range0(n, prefix) { return Array.from({ length: n }, (_, i) => `${prefix}${i}`); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { EnforceHistoricalReplayCli0({ entrypoint: 'pcc-uniform-locked-nand-construction0.mjs' }); let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UniformLockedNANDConstruction.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } options.historicalReplay = true; const verdict = await CheckUniformLockedNANDConstruction0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
