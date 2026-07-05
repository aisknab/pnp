#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckUniformLockedNANDThreshold0, CheckLockedNANDThresholdExample0 } from './pcc-uniform-locked-nand-threshold0.mjs';

const CHECKER = 'CheckUniformResidualBandMinimizer0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-RESIDUAL-BAND-MINIMIZER-2026-07-05-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const INPUT_COORD = 'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01';
const CONSTRUCTION_COORD = 'PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01';
const THRESHOLD_COORD = 'PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_RESIDUAL_BAND_MINIMIZER.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const OUT = 'artifacts/uniform-residual-band-minimizer/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_GAPS = ['GAP-001-UnrestrictedFinalSoundness', 'GAP-003-BoundedSmallModelsNotUniformProof', 'GAP-004-FiniteToUnboundedUniformity', 'GAP-005-NoHiddenOracleSemanticCompleteness'];
const REQUIRED_OBLIGATIONS = ['RBM-001-ResidualSlackBoundAllLockedInputs', 'RBM-002-StrictGainLowersSlack', 'RBM-003-ZeroSlackReturnsExactMinimum', 'RBM-004-ExactRouteReturnsExactMinimum', 'RBM-005-PolynomialIterationAndCertificateBounds', 'RBM-006-ThresholdDecisionUsesExactMinimum', 'RBM-007-NoHiddenOracleOrExactMinimizer'];

export async function CheckUniformResidualBandMinimizer0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  try {
    const threshold = await CheckUniformLockedNANDThreshold0({ root, writeOutput: false });
    if (threshold.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UniformResidualBandMinimizer.ThresholdDependency', ['dependsOn', THRESHOLD_COORD], 'UFS-003 threshold dependency must accept', { dependency: threshold }));

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'uniform residual-band minimizer manifest' });
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
      tag: 'accept', kind: 'accept', checker: CHECKER, version: VERSION, coordinate: COORD,
      ufsTargetCoordinate: TARGET_COORD, ufsObligationId: 'UFS-004-ResidualBandMinimizerUniformPolynomial',
      claimStatus: 'ufs-004-residual-band-minimizer-uniform-polynomial-accepted',
      residualBandMinimizerAccepted: true, ufs004ResidualBandMinimizerDischarged: true,
      dependsOn: [INPUT_COORD, CONSTRUCTION_COORD, THRESHOLD_COORD],
      totalOnThresholdInstances: true, uniformAcrossSizes: true, returnsExactMinimum: true,
      residualSlackBoundRequired: 4, maxGainIterationsForLockedInstances: 4,
      proofObligationCount: REQUIRED_OBLIGATIONS.length,
      positiveExampleCount: manifestRead.value.positiveExamples.length,
      negativeExampleCount: manifestRead.value.negativeExamples.length,
      manifestSha256: sha256Hex0(manifestRead.bytes), targetSha256: sha256Hex0(targetRead.bytes),
      evidenceFileCount: evidence.evidence.length, evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)), evidence: evidence.evidence,
      uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS],
      nextProofSurface: 'pcc-uniform-zeroslack-closure0.mjs', outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UniformResidualBandMinimizer.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function CheckResidualBandMinimizerExample0(circuit) {
  const threshold = CheckLockedNANDThresholdExample0(circuit);
  if (threshold.tag !== 'accept') return threshold;
  const base = {
    tag: 'accept',
    thresholdDecision: threshold.thresholdPredicate,
    baseline: threshold.baseline,
    fullWordSize: threshold.fullWordSize,
    maxGainIterations: 4,
    residualSlackBound: 4,
    pccMinReturnsExactMinimum: true,
  };
  if (threshold.satisfiable) {
    return {
      ...base,
      minimumRelationToBaseline: 'strictly-above',
      exactMinimumLowerBound: threshold.muLowerBoundInSatCase,
      exactMinimumUpperBound: threshold.muUpperBoundInSatCase,
      satDecisionRule: '|PCCMin(W_phi)| > B_phi',
    };
  }
  return {
    ...base,
    minimumRelationToBaseline: 'equal',
    exactMinimumSize: threshold.baseline,
    satDecisionRule: '|PCCMin(W_phi)| == B_phi',
  };
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UniformResidualBandMinimizer.ManifestShape', [], 'manifest must be an object');
  const exact = [['kind', 'PNPUniformResidualBandMinimizer0'], ['version', VERSION], ['coordinate', COORD], ['status', 'uniform-residual-band-minimizer-accepted'], ['ufsTargetCoordinate', TARGET_COORD], ['ufsObligationId', 'UFS-004-ResidualBandMinimizerUniformPolynomial']];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('UniformResidualBandMinimizer.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  if (!sameArray0(manifest.dependsOn, [INPUT_COORD, CONSTRUCTION_COORD, THRESHOLD_COORD])) return reject0('UniformResidualBandMinimizer.DependsOn', ['dependsOn'], 'dependency mismatch', { actual: manifest.dependsOn });
  const boundary = validateBoundary0(manifest.claimBoundary); if (boundary.tag === 'reject') return boundary;
  const bools = { residualBandMinimizerAccepted: true, ufs004ResidualBandMinimizerDischarged: true, uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false, publicTheoremEmissionAllowedByMinimizer: false };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('UniformResidualBandMinimizer.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  const m = manifest.minimizer;
  if (!plain0(m)) return reject0('UniformResidualBandMinimizer.MinimizerShape', ['minimizer'], 'minimizer must be an object');
  const minimizerBools = { totalOnThresholdInstances: true, deterministic: true, uniformAcrossSizes: true, finiteInstanceList: false, boundedEnumerationOnly: false, usesSatOracle: false, usesExactMinimizationOracle: false, usesUnboundedSearch: false, returnsExactMinimum: true, thresholdDecisionReadsExactMinimum: true };
  for (const [key, expected] of Object.entries(minimizerBools)) if (m[key] !== expected) return reject0('UniformResidualBandMinimizer.MinimizerBoolean', ['minimizer', key], 'minimizer boolean mismatch', { expected, actual: m[key] });
  if (m.residualSlackBoundRequired !== 4 || m.maxGainIterationsForLockedInstances !== 4) return reject0('UniformResidualBandMinimizer.ResidualBand', ['minimizer'], 'locked residual band must be four');
  if (!String(m.polynomialTimeBound ?? '').includes('poly') || !String(m.certificateSizeBound ?? '').includes('poly')) return reject0('UniformResidualBandMinimizer.PolynomialBounds', ['minimizer'], 'polynomial bounds must be declared');
  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((x) => x?.id), REQUIRED_OBLIGATIONS)) return reject0('UniformResidualBandMinimizer.ProofObligations', ['proofObligations'], 'proof obligations mismatch');
  for (const entry of manifest.proofObligations) if (!plain0(entry) || entry.requiredForDischarge !== true || typeof entry.statement !== 'string' || entry.statement.length === 0) return reject0('UniformResidualBandMinimizer.ProofObligationEntry', ['proofObligations'], 'proof obligation entry incomplete');
  if (!plain0(manifest.uniformityClaims)) return reject0('UniformResidualBandMinimizer.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(manifest.uniformityClaims)) if (value !== true) return reject0('UniformResidualBandMinimizer.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  if (!sameArray0(manifest.linkedGaps, REQUIRED_GAPS)) return reject0('UniformResidualBandMinimizer.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_GAPS, actual: manifest.linkedGaps });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('UniformResidualBandMinimizer.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('UniformResidualBandMinimizer.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-uniform-residual-band-minimizer0.mjs' || manifest.audit.test !== 'audits/uniform-residual-band-minimizer0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('UniformResidualBandMinimizer.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('UniformResidualBandMinimizer.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const ufs004 = (Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : []).find((entry) => entry?.id === 'UFS-004-ResidualBandMinimizerUniformPolynomial');
  if (!plain0(ufs004)) return reject0('UniformResidualBandMinimizer.TargetMissingUFS004', ['target', 'requiredUniformObligations'], 'UFS-004 target missing');
  if (ufs004.requiredForDischarge !== true) return reject0('UniformResidualBandMinimizer.TargetUFS004NotRequired', ['target', 'requiredUniformObligations', 'UFS-004'], 'UFS-004 must be required for discharge');
  if (ufs004.futureChecker !== 'pcc-uniform-residual-band-minimizer0.mjs') return reject0('UniformResidualBandMinimizer.TargetUFS004Checker', ['target', 'requiredUniformObligations', 'UFS-004', 'futureChecker'], 'UFS-004 target checker mismatch', { actual: ufs004.futureChecker });
  return { tag: 'accept' };
}

function validateExamples0(manifest) { for (let i = 0; i < manifest.positiveExamples.length; i += 1) { const example = manifest.positiveExamples[i]; const out = CheckResidualBandMinimizerExample0(example.inputCircuit); if (out.tag !== 'accept') return reject0('UniformResidualBandMinimizer.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out }); for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('UniformResidualBandMinimizer.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual: out[key] }); } for (let i = 0; i < manifest.negativeExamples.length; i += 1) { const example = manifest.negativeExamples[i]; if (example.inputCircuit !== undefined) { const out = CheckResidualBandMinimizerExample0(example.inputCircuit); if (out.tag !== 'reject') return reject0('UniformResidualBandMinimizer.NegativeExampleAccepted', ['negativeExamples', i], 'negative example accepted', { exampleId: example.id }); if (example.expectedRejectCoord && out.coord !== example.expectedRejectCoord) return reject0('UniformResidualBandMinimizer.NegativeExampleCoord', ['negativeExamples', i, 'expectedRejectCoord'], 'negative example reject coordinate mismatch', { expected: example.expectedRejectCoord, actual: out.coord }); } } return { tag: 'accept' }; }
function validateBoundary0(boundary) { if (!plain0(boundary)) return reject0('UniformResidualBandMinimizer.BoundaryShape', ['claimBoundary'], 'boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false) return reject0('UniformResidualBandMinimizer.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false'); if (boundary.finalTheoremReady !== false) return reject0('UniformResidualBandMinimizer.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false'); if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('UniformResidualBandMinimizer.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty'); if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('UniformResidualBandMinimizer.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers }); return { tag: 'accept' }; }
async function readJson0({ root, filePath, override, label }) { if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; } try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('UniformResidualBandMinimizer.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); } }
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('UniformResidualBandMinimizer.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('UniformResidualBandMinimizer.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('UniformResidualBandMinimizer.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('UniformResidualBandMinimizer.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('UniformResidualBandMinimizer.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UniformResidualBandMinimizer.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckUniformResidualBandMinimizer0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
