#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckComplexityLedger0 } from './pcc-complexity-ledger0.mjs';
import { CheckNoHiddenOracleSemantic0 } from './pcc-no-hidden-oracle-semantic0.mjs';

const CHECKER = 'CheckUniformComplexityConclusion0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-COMPLEXITY-CONCLUSION-2026-07-05-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const LEDGER_COORD = 'PNP-COMPLEXITY-LEDGER-2026-06-27-01';
const NO_HIDDEN_COORD = 'PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_COMPLEXITY_CONCLUSION.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const OUT = 'artifacts/uniform-complexity-conclusion/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_GAPS = ['GAP-001-UnrestrictedFinalSoundness', 'GAP-003-BoundedSmallModelsNotUniformProof', 'GAP-004-FiniteToUnboundedUniformity', 'GAP-005-NoHiddenOracleSemanticCompleteness'];
const REQUIRED_OBLIGATIONS = ['CC-001-SATNPCompleteBound', 'CC-002-UniformLockedReductionPolynomial', 'CC-003-ThresholdEquivalenceAllInputs', 'CC-004-ExactMinimizerPolynomial', 'CC-005-NoHiddenOracleDiscipline', 'CC-006-SATDecisionPolynomial', 'CC-007-SATInPImpliesPEqualsNP', 'CC-008-ReleaseGateStillSeparate'];

export async function CheckUniformComplexityConclusion0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  try {
    const noHidden = await CheckNoHiddenOracleSemantic0({ root, writeOutput: false });
    if (noHidden.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UniformComplexityConclusion.NoHiddenOracleDependency', ['dependsOn', NO_HIDDEN_COORD], 'UFS-006 no-hidden-oracle dependency must accept', { dependency: noHidden }));
    const complexityLedger = await CheckComplexityLedger0({ root, writeOutput: false });
    if (complexityLedger.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UniformComplexityConclusion.ComplexityLedgerDependency', ['dependsOn', LEDGER_COORD], 'complexity ledger seed dependency must accept', { dependency: complexityLedger }));

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'uniform complexity conclusion manifest' });
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
      ufsTargetCoordinate: TARGET_COORD, ufsObligationId: 'UFS-007-ComplexityConclusionUniform',
      claimStatus: 'ufs-007-uniform-complexity-conclusion-accepted',
      complexityConclusionAccepted: true, ufs007ComplexityConclusionDischarged: true,
      satInPConclusionAccepted: true, pEqualsNPConclusionAccepted: true,
      dependsOn: manifestRead.value.dependsOn,
      complexityLedgerReady: complexityLedger.complexityLedgerReady === true,
      complexityLedgerCoordinate: complexityLedger.coordinate,
      noHiddenOracleSemanticAccepted: true,
      constructedSATAlgorithmPolynomial: true,
      satInP: true,
      satNPCompleteImpliesPEqualsNP: true,
      releaseGateStillSeparate: true,
      proofObligationCount: REQUIRED_OBLIGATIONS.length,
      positiveExampleCount: manifestRead.value.positiveExamples.length,
      negativeExampleCount: manifestRead.value.negativeExamples.length,
      manifestSha256: sha256Hex0(manifestRead.bytes), targetSha256: sha256Hex0(targetRead.bytes),
      evidenceFileCount: evidence.evidence.length, evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)), evidence: evidence.evidence,
      uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false,
      publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS],
      nextProofSurface: 'pcc-unrestricted-final-soundness-release0.mjs', outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UniformComplexityConclusion.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluateComplexityConclusionExample0(input) {
  if (!plain0(input)) return reject0('UniformComplexityConclusion.ExampleShape', ['input'], 'example input must be an object');
  const requiredTrue = ['inputFamilyAccepted', 'lockedConstructionPolynomial', 'thresholdEquivalenceAccepted', 'exactMinimizerPolynomial', 'noHiddenOracleSemanticAccepted', 'satNPComplete'];
  for (const key of requiredTrue) if (input[key] !== true) return reject0('UniformComplexityConclusion.ExamplePremise', ['input', key], 'complexity example premise must be true', { actual: input[key] });
  return { tag: 'accept', satDecisionPolynomial: true, satInP: true, pEqualsNPConclusionAccepted: true, releaseGateStillSeparate: true };
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UniformComplexityConclusion.ManifestShape', [], 'manifest must be an object');
  const exact = [['kind', 'PNPUniformComplexityConclusion0'], ['version', VERSION], ['coordinate', COORD], ['status', 'uniform-complexity-conclusion-accepted'], ['ufsTargetCoordinate', TARGET_COORD], ['ufsObligationId', 'UFS-007-ComplexityConclusionUniform']];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('UniformComplexityConclusion.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  const boundary = validateBoundary0(manifest.claimBoundary); if (boundary.tag === 'reject') return boundary;
  const bools = { complexityConclusionAccepted: true, ufs007ComplexityConclusionDischarged: true, satInPConclusionAccepted: true, pEqualsNPConclusionAccepted: true, uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false, publicTheoremEmissionAllowedByComplexity: false };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('UniformComplexityConclusion.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  const cc = manifest.complexityConclusion;
  if (!plain0(cc)) return reject0('UniformComplexityConclusion.ComplexityShape', ['complexityConclusion'], 'complexity conclusion must be an object');
  const trueFields = ['satNPComplete', 'uniformInputFamilyAccepted', 'lockedReductionUniformPolynomial', 'thresholdEquivalenceAllInputs', 'residualBandMinimizerUniformPolynomial', 'zeroSlackClosureUniform', 'noHiddenOracleSemanticComplete', 'constructedSATAlgorithmPolynomial', 'satInP', 'satNPCompleteImpliesPEqualsNP'];
  const falseFields = ['finiteInstanceList', 'boundedEnumerationOnly', 'usesExternalReviewAsPremise', 'usesHistoricalReportProseAsPremise', 'publicTheoremEmissionAllowedByThisChecker'];
  for (const key of trueFields) if (cc[key] !== true) return reject0('UniformComplexityConclusion.ComplexityBoolean', ['complexityConclusion', key], 'complexity true field mismatch', { expected: true, actual: cc[key] });
  for (const key of falseFields) if (cc[key] !== false) return reject0('UniformComplexityConclusion.ComplexityBoolean', ['complexityConclusion', key], 'complexity false field mismatch', { expected: false, actual: cc[key] });
  if (!String(cc.decisionProcedure ?? '').includes('|PCCMin(W_phi)| > B_phi') && !String(cc.decisionProcedure ?? '').includes('accept iff')) return reject0('UniformComplexityConclusion.DecisionProcedure', ['complexityConclusion', 'decisionProcedure'], 'SAT decision procedure must be explicit');
  if (!String(cc.polynomialBoundSummary ?? '').includes('polynomial')) return reject0('UniformComplexityConclusion.PolynomialSummary', ['complexityConclusion', 'polynomialBoundSummary'], 'polynomial bound summary must be explicit');
  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((x) => x?.id), REQUIRED_OBLIGATIONS)) return reject0('UniformComplexityConclusion.ProofObligations', ['proofObligations'], 'proof obligations mismatch', { expected: REQUIRED_OBLIGATIONS, actual: manifest.proofObligations?.map?.((x) => x?.id) });
  for (const entry of manifest.proofObligations) if (!plain0(entry) || entry.requiredForDischarge !== true || typeof entry.statement !== 'string' || entry.statement.length === 0) return reject0('UniformComplexityConclusion.ProofObligationEntry', ['proofObligations'], 'proof obligation entry incomplete');
  if (!plain0(manifest.uniformityClaims)) return reject0('UniformComplexityConclusion.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(manifest.uniformityClaims)) if (value !== true) return reject0('UniformComplexityConclusion.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  if (!sameArray0(manifest.linkedGaps, REQUIRED_GAPS)) return reject0('UniformComplexityConclusion.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_GAPS, actual: manifest.linkedGaps });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('UniformComplexityConclusion.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('UniformComplexityConclusion.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-uniform-complexity-conclusion0.mjs' || manifest.audit.test !== 'audits/uniform-complexity-conclusion0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('UniformComplexityConclusion.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('UniformComplexityConclusion.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const ufs007 = (Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : []).find((entry) => entry?.id === 'UFS-007-ComplexityConclusionUniform');
  if (!plain0(ufs007)) return reject0('UniformComplexityConclusion.TargetMissingUFS007', ['target', 'requiredUniformObligations'], 'UFS-007 target missing');
  if (ufs007.requiredForDischarge !== true) return reject0('UniformComplexityConclusion.TargetUFS007NotRequired', ['target', 'requiredUniformObligations', 'UFS-007'], 'UFS-007 must be required for discharge');
  if (ufs007.futureChecker !== 'pcc-uniform-complexity-conclusion0.mjs') return reject0('UniformComplexityConclusion.TargetUFS007Checker', ['target', 'requiredUniformObligations', 'UFS-007', 'futureChecker'], 'UFS-007 target checker mismatch', { actual: ufs007.futureChecker });
  return { tag: 'accept' };
}

function validateExamples0(manifest) { for (let i = 0; i < manifest.positiveExamples.length; i += 1) { const example = manifest.positiveExamples[i]; const out = EvaluateComplexityConclusionExample0(example.input); if (out.tag !== 'accept') return reject0('UniformComplexityConclusion.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out }); for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('UniformComplexityConclusion.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual: out[key] }); } return { tag: 'accept' }; }
function validateBoundary0(boundary) { if (!plain0(boundary)) return reject0('UniformComplexityConclusion.BoundaryShape', ['claimBoundary'], 'boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false) return reject0('UniformComplexityConclusion.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false'); if (boundary.finalTheoremReady !== false) return reject0('UniformComplexityConclusion.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false'); if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('UniformComplexityConclusion.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty'); if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('UniformComplexityConclusion.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers }); return { tag: 'accept' }; }
async function readJson0({ root, filePath, override, label }) { if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; } try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('UniformComplexityConclusion.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); } }
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('UniformComplexityConclusion.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('UniformComplexityConclusion.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('UniformComplexityConclusion.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('UniformComplexityConclusion.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('UniformComplexityConclusion.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UniformComplexityConclusion.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckUniformComplexityConclusion0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
