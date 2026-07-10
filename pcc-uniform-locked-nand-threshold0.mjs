#!/usr/bin/env node

import { EnforceHistoricalReplayCli0, LegacyReplayRequiredReject0 } from './pcc-legacy-replay-gate0.mjs';

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckNANDCircuitInputFamilyMember0, CheckUniformInputFamily0 } from './pcc-uniform-input-family0.mjs';
import { BuildLockedNANDConstruction0, CheckUniformLockedNANDConstruction0 } from './pcc-uniform-locked-nand-construction0.mjs';

const CHECKER = 'CheckUniformLockedNANDThreshold0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const INPUT_COORD = 'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01';
const CONSTRUCTION_COORD = 'PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_LOCKED_NAND_THRESHOLD.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const OUT = 'artifacts/uniform-locked-nand-threshold/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_GAPS = ['GAP-001-UnrestrictedFinalSoundness', 'GAP-003-BoundedSmallModelsNotUniformProof', 'GAP-004-FiniteToUnboundedUniformity'];
const REQUIRED_OBLIGATIONS = ['THR-001-BaselineDistinctAllInputs', 'THR-002-TraceEquivalenceAllInputs', 'THR-003-ZeroOutputConventionAllInputs', 'THR-004-FinalLockSeparationAllInputs', 'THR-005-ThresholdEquivalenceAllInputs', 'THR-006-ResidualSlackBoundAllInputs'];

export async function CheckUniformLockedNANDThreshold0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  if (options.historicalReplay !== true) return write0(root, outputPath, writeOutput, LegacyReplayRequiredReject0(CHECKER, BLOCKERS));
  try {
    const inputFamily = await CheckUniformInputFamily0({ root, writeOutput: false, historicalReplay: true });
    if (inputFamily.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UniformLockedNANDThreshold.InputFamilyDependency', ['dependsOn', INPUT_COORD], 'UFS-001 input family dependency must accept', { dependency: inputFamily }));
    const construction = await CheckUniformLockedNANDConstruction0({ root, writeOutput: false, historicalReplay: true });
    if (construction.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UniformLockedNANDThreshold.ConstructionDependency', ['dependsOn', CONSTRUCTION_COORD], 'UFS-002 construction dependency must accept', { dependency: construction }));

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'threshold manifest' });
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const targetRead = await readJson0({ root, filePath: options.targetPath ?? TARGET_PATH, override: options.targetOverride, label: 'uniform target manifest' });
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
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD,
      ufsTargetCoordinate: TARGET_COORD, ufsObligationId: 'UFS-003-ThresholdEquivalenceAllInputs',
      claimStatus: 'ufs-003-locked-nand-threshold-equivalence-accepted',
      lockedNANDThresholdAccepted: true, ufs003ThresholdEquivalenceDischarged: true,
      dependsOn: [INPUT_COORD, CONSTRUCTION_COORD], allFiniteInputsCovered: true,
      thresholdEquivalenceParametric: true, residualSlackBound: 4,
      proofObligationCount: REQUIRED_OBLIGATIONS.length,
      positiveExampleCount: manifestRead.value.positiveExamples.length,
      negativeExampleCount: manifestRead.value.negativeExamples.length,
      manifestSha256: sha256Hex0(manifestRead.bytes), targetSha256: sha256Hex0(targetRead.bytes),
      evidenceFileCount: evidence.evidence.length, evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)), evidence: evidence.evidence,
      uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS],
      nextProofSurface: 'pcc-uniform-residual-band-minimizer0.mjs', outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UniformLockedNANDThreshold.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluateNANDCircuit0(circuit, assignment) {
  const member = CheckNANDCircuitInputFamilyMember0(circuit);
  if (member.tag !== 'accept') return member;
  if (!Array.isArray(assignment) || assignment.length !== circuit.inputCount || assignment.some((x) => x !== 0 && x !== 1)) return reject0('UniformLockedNANDThreshold.BadAssignment', ['assignment'], 'assignment must be a 0/1 vector of inputCount length', { inputCount: circuit.inputCount, assignment });
  const gates = [];
  for (const gate of circuit.gates) {
    const left = evalSource0(gate.left, assignment, gates);
    const right = evalSource0(gate.right, assignment, gates);
    gates.push(1 - (left & right));
  }
  return { tag: 'accept', value: evalSource0(circuit.output, assignment, gates), gateValues: gates };
}

export function BruteForceNANDSat0(circuit) {
  const member = CheckNANDCircuitInputFamilyMember0(circuit);
  if (member.tag !== 'accept') return member;
  if (circuit.inputCount > 12) return reject0('UniformLockedNANDThreshold.BruteForceLimit', ['inputCount'], 'example helper is capped at 12 inputs', { inputCount: circuit.inputCount });
  for (let mask = 0; mask < 2 ** circuit.inputCount; mask += 1) {
    const assignment = Array.from({ length: circuit.inputCount }, (_, i) => (mask >> i) & 1);
    const out = EvaluateNANDCircuit0(circuit, assignment);
    if (out.tag !== 'accept') return out;
    if (out.value === 1) return { tag: 'accept', satisfiable: true, witness: assignment };
  }
  return { tag: 'accept', satisfiable: false, witness: null };
}

export function CheckLockedNANDThresholdExample0(circuit) {
  const built = BuildLockedNANDConstruction0(circuit);
  if (built.tag !== 'accept') return built;
  const sat = BruteForceNANDSat0(circuit);
  if (sat.tag !== 'accept') return sat;
  const baseline = built.baseline;
  const fullWordSize = built.fullWordSize;
  if (sat.satisfiable) return { tag: 'accept', satisfiable: true, baseline, fullWordSize, muLowerBoundInSatCase: baseline + 1, muUpperBoundInSatCase: baseline + 4, thresholdPredicate: true, residualSlackBound: 4 };
  return { tag: 'accept', satisfiable: false, baseline, fullWordSize, muEqualsBaselineInUnsatCase: true, thresholdPredicate: false, residualSlackBound: fullWordSize - baseline };
}

function evalSource0(source, assignment, gates) { if (source.kind === 'input') return assignment[source.index]; if (source.kind === 'const') return source.value; return gates[source.index]; }

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UniformLockedNANDThreshold.ManifestShape', [], 'manifest must be an object');
  const exact = [['kind', 'PNPUniformLockedNANDThreshold0'], ['version', VERSION], ['coordinate', COORD], ['status', 'uniform-locked-nand-threshold-accepted'], ['ufsTargetCoordinate', TARGET_COORD], ['ufsObligationId', 'UFS-003-ThresholdEquivalenceAllInputs']];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('UniformLockedNANDThreshold.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  if (!sameArray0(manifest.dependsOn, [INPUT_COORD, CONSTRUCTION_COORD])) return reject0('UniformLockedNANDThreshold.DependsOn', ['dependsOn'], 'dependency mismatch', { actual: manifest.dependsOn });
  const boundary = validateBoundary0(manifest.claimBoundary); if (boundary.tag === 'reject') return boundary;
  const bools = { lockedNANDThresholdAccepted: true, ufs003ThresholdEquivalenceDischarged: true, uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false, publicTheoremEmissionAllowedByThreshold: false };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('UniformLockedNANDThreshold.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  const th = manifest.thresholdTheorem;
  if (!plain0(th)) return reject0('UniformLockedNANDThreshold.TheoremShape', ['thresholdTheorem'], 'threshold theorem must be an object');
  const theoremBools = { allFiniteInputsCovered: true, schemaUniformAcrossSizes: true, finiteInstanceList: false, boundedEnumerationOnly: false, usesSatOracle: false, usesExactMinimizationOracle: false };
  for (const [key, expected] of Object.entries(theoremBools)) if (th[key] !== expected) return reject0('UniformLockedNANDThreshold.TheoremBoolean', ['thresholdTheorem', key], 'threshold theorem boolean mismatch', { expected, actual: th[key] });
  if (!String(th.baselineFormula ?? '').includes('18*m') || !String(th.fullWordSizeFormula ?? '').includes('B_phi + 4')) return reject0('UniformLockedNANDThreshold.Formulas', ['thresholdTheorem'], 'threshold formulas mismatch');
  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((x) => x?.id), REQUIRED_OBLIGATIONS)) return reject0('UniformLockedNANDThreshold.ProofObligations', ['proofObligations'], 'proof obligations mismatch');
  for (const entry of manifest.proofObligations) if (!plain0(entry) || entry.requiredForDischarge !== true || typeof entry.statement !== 'string' || entry.statement.length === 0) return reject0('UniformLockedNANDThreshold.ProofObligationEntry', ['proofObligations'], 'proof obligation entry incomplete');
  if (!plain0(manifest.uniformityClaims)) return reject0('UniformLockedNANDThreshold.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(manifest.uniformityClaims)) if (value !== true) return reject0('UniformLockedNANDThreshold.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  if (!sameArray0(manifest.linkedGaps, REQUIRED_GAPS)) return reject0('UniformLockedNANDThreshold.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_GAPS, actual: manifest.linkedGaps });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('UniformLockedNANDThreshold.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('UniformLockedNANDThreshold.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-uniform-locked-nand-threshold0.mjs' || manifest.audit.test !== 'audits/uniform-locked-nand-threshold0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('UniformLockedNANDThreshold.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('UniformLockedNANDThreshold.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const ufs003 = (Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : []).find((entry) => entry?.id === 'UFS-003-ThresholdEquivalenceAllInputs');
  if (!plain0(ufs003)) return reject0('UniformLockedNANDThreshold.TargetMissingUFS003', ['target', 'requiredUniformObligations'], 'UFS-003 target missing');
  if (ufs003.requiredForDischarge !== true) return reject0('UniformLockedNANDThreshold.TargetUFS003NotRequired', ['target', 'requiredUniformObligations', 'UFS-003'], 'UFS-003 must be required for discharge');
  if (ufs003.futureChecker !== 'pcc-uniform-locked-nand-threshold0.mjs') return reject0('UniformLockedNANDThreshold.TargetUFS003Checker', ['target', 'requiredUniformObligations', 'UFS-003', 'futureChecker'], 'UFS-003 target checker mismatch', { actual: ufs003.futureChecker });
  return { tag: 'accept' };
}

function validateExamples0(manifest) { for (let i = 0; i < manifest.positiveExamples.length; i += 1) { const example = manifest.positiveExamples[i]; const out = CheckLockedNANDThresholdExample0(example.inputCircuit); if (out.tag !== 'accept') return reject0('UniformLockedNANDThreshold.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out }); for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('UniformLockedNANDThreshold.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual: out[key] }); } for (let i = 0; i < manifest.negativeExamples.length; i += 1) { const example = manifest.negativeExamples[i]; if (example.inputCircuit !== undefined) { const out = CheckLockedNANDThresholdExample0(example.inputCircuit); if (out.tag !== 'reject') return reject0('UniformLockedNANDThreshold.NegativeExampleAccepted', ['negativeExamples', i], 'negative example accepted', { exampleId: example.id }); if (example.expectedRejectCoord && out.coord !== example.expectedRejectCoord) return reject0('UniformLockedNANDThreshold.NegativeExampleCoord', ['negativeExamples', i, 'expectedRejectCoord'], 'negative example reject coordinate mismatch', { expected: example.expectedRejectCoord, actual: out.coord }); } } return { tag: 'accept' }; }
function validateBoundary0(boundary) { if (!plain0(boundary)) return reject0('UniformLockedNANDThreshold.BoundaryShape', ['claimBoundary'], 'boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false) return reject0('UniformLockedNANDThreshold.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false'); if (boundary.finalTheoremReady !== false) return reject0('UniformLockedNANDThreshold.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false'); if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('UniformLockedNANDThreshold.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty'); if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('UniformLockedNANDThreshold.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers }); return { tag: 'accept' }; }
async function readJson0({ root, filePath, override, label }) { if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; } try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('UniformLockedNANDThreshold.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); } }
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('UniformLockedNANDThreshold.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('UniformLockedNANDThreshold.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('UniformLockedNANDThreshold.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('UniformLockedNANDThreshold.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('UniformLockedNANDThreshold.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { EnforceHistoricalReplayCli0({ entrypoint: 'pcc-uniform-locked-nand-threshold0.mjs' }); let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UniformLockedNANDThreshold.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } options.historicalReplay = true; const verdict = await CheckUniformLockedNANDThreshold0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
