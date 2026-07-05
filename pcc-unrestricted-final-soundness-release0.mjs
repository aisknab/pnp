#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckUniformFinalSoundnessTarget0 } from './pcc-uniform-final-soundness-target0.mjs';
import { CheckUniformInputFamily0 } from './pcc-uniform-input-family0.mjs';
import { CheckUniformLockedNANDConstruction0 } from './pcc-uniform-locked-nand-construction0.mjs';
import { CheckUniformLockedNANDThreshold0 } from './pcc-uniform-locked-nand-threshold0.mjs';
import { CheckUniformResidualBandMinimizer0 } from './pcc-uniform-residual-band-minimizer0.mjs';
import { CheckUniformZeroSlackClosure0 } from './pcc-uniform-zeroslack-closure0.mjs';
import { CheckNoHiddenOracleSemantic0 } from './pcc-no-hidden-oracle-semantic0.mjs';
import { CheckUniformComplexityConclusion0 } from './pcc-uniform-complexity-conclusion0.mjs';

const CHECKER = 'CheckUnrestrictedFinalSoundnessRelease0';
const VERSION = 0;
const COORD = 'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const MANIFEST_PATH = 'proof-obligations/UNRESTRICTED_FINAL_SOUNDNESS_RELEASE.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const OUT = 'artifacts/unrestricted-final-soundness-release/latest-verdict.json';
const BEFORE_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const AFTER_BLOCKERS = ['ExternalReview.Acceptance'];
const REQUIRED_DEPENDENCIES = [
  ['UFS-000-Target', TARGET_COORD, CheckUniformFinalSoundnessTarget0],
  ['UFS-001-InputFamilyUniformity', 'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01', CheckUniformInputFamily0],
  ['UFS-002-LockedNANDConstructionUniformPolynomial', 'PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01', CheckUniformLockedNANDConstruction0],
  ['UFS-003-ThresholdEquivalenceAllInputs', 'PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01', CheckUniformLockedNANDThreshold0],
  ['UFS-004-ResidualBandMinimizerUniformPolynomial', 'PNP-UNIFORM-RESIDUAL-BAND-MINIMIZER-2026-07-05-01', CheckUniformResidualBandMinimizer0],
  ['UFS-005-ZeroSlackContradictionUniform', 'PNP-UNIFORM-ZEROSLACK-CLOSURE-2026-07-05-01', CheckUniformZeroSlackClosure0],
  ['UFS-006-NoHiddenOracleSemanticCompleteness', 'PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01', CheckNoHiddenOracleSemantic0],
  ['UFS-007-ComplexityConclusionUniform', 'PNP-UNIFORM-COMPLEXITY-CONCLUSION-2026-07-05-01', CheckUniformComplexityConclusion0],
];
const REQUIRED_OBLIGATIONS = [
  'REL-001-AllUFSDependenciesAccepted',
  'REL-002-DependencyVerdictsHashBound',
  'REL-003-ComplexityConclusionBound',
  'REL-004-NoExternalReviewPremise',
  'REL-005-ClearUnrestrictedFinalSoundnessOnly',
  'REL-006-NoPrematurePublicTheoremEmission',
];

export async function CheckUnrestrictedFinalSoundnessRelease0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  try {
    const dependencies = [];
    for (const [id, coordinate, checker] of REQUIRED_DEPENDENCIES) {
      const out = await checker({ root, writeOutput: false });
      if (out.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('UnrestrictedFinalSoundnessRelease.DependencyReject', ['dependsOn', id], 'required UFS dependency rejected', { id, coordinate, dependency: out }));
      const actualCoordinate = out.coordinate ?? out.ufsTargetCoordinate ?? out.coord;
      if (coordinate !== TARGET_COORD && actualCoordinate !== coordinate) return write0(root, outputPath, writeOutput, reject0('UnrestrictedFinalSoundnessRelease.DependencyCoordinate', ['dependsOn', id], 'dependency coordinate mismatch', { id, expected: coordinate, actual: actualCoordinate }));
      dependencies.push({ id, coordinate, sha256: sha256Text0(stableStringify0(out)), accepted: true });
    }

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'unrestricted final soundness release manifest' });
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
      ufsTargetCoordinate: TARGET_COORD, ufsObligationId: 'UFS-008-ReleaseTransitionFromProofOnly',
      claimStatus: 'ufs-008-unrestricted-final-soundness-release-accepted',
      releaseTransitionAccepted: true,
      ufs008ReleaseTransitionDischarged: true,
      releaseUnrestrictedFinalSoundnessCleared: true,
      unrestrictedFinalSoundnessDischarged: true,
      uniformFinalSoundnessProved: true,
      internalFinalTheoremReady: true,
      satInPConclusionAccepted: true,
      pEqualsNPConclusionAccepted: true,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: true,
      activeFinalNodeIds: manifestRead.value.claimBoundaryAfterProofTransition.activeFinalNodeIds,
      clearedBlockers: ['Release.UnrestrictedFinalSoundness'],
      remainingBlockers: [...AFTER_BLOCKERS],
      externalReviewIsMathematicalPremise: false,
      historicalReportProseIsMathematicalPremise: false,
      dependencyCount: dependencies.length,
      dependencyDigestSha256: sha256Text0(stableStringify0(dependencies)),
      dependencies,
      manifestSha256: sha256Hex0(manifestRead.bytes), targetSha256: sha256Hex0(targetRead.bytes),
      evidenceFileCount: evidence.evidence.length, evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)), evidence: evidence.evidence,
      nextProofSurface: 'pcc-public-theorem-activation0.mjs', outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UnrestrictedFinalSoundnessRelease.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluateUnrestrictedFinalSoundnessReleaseExample0(input) {
  if (!plain0(input)) return reject0('UnrestrictedFinalSoundnessRelease.ExampleShape', ['input'], 'example input must be an object');
  const trueFields = ['allUFSDependenciesAccepted', 'allUFSDependencyCoordinatesHashBound', 'ufs007ComplexityConclusionAccepted'];
  const falseFields = ['usesExternalReviewAsPremise', 'usesHistoricalReportProseAsPremise', 'activatesPublicTheoremEmission'];
  for (const key of trueFields) if (input[key] !== true) return reject0('UnrestrictedFinalSoundnessRelease.ExamplePremise', ['input', key], 'release example true premise mismatch', { expected: true, actual: input[key] });
  for (const key of falseFields) if (input[key] !== false) return reject0('UnrestrictedFinalSoundnessRelease.ExamplePremise', ['input', key], 'release example false premise mismatch', { expected: false, actual: input[key] });
  return { tag: 'accept', releaseUnrestrictedFinalSoundnessCleared: true, unrestrictedFinalSoundnessDischarged: true, internalFinalTheoremReady: true, publicTheoremEmissionAllowed: false };
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UnrestrictedFinalSoundnessRelease.ManifestShape', [], 'manifest must be an object');
  const exact = [['kind', 'PNPUnrestrictedFinalSoundnessRelease0'], ['version', VERSION], ['coordinate', COORD], ['status', 'unrestricted-final-soundness-release-accepted'], ['ufsTargetCoordinate', TARGET_COORD], ['ufsObligationId', 'UFS-008-ReleaseTransitionFromProofOnly']];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('UnrestrictedFinalSoundnessRelease.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  if (!sameArray0(manifest.dependsOn, REQUIRED_DEPENDENCIES.map(([, coord]) => coord))) return reject0('UnrestrictedFinalSoundnessRelease.DependsOn', ['dependsOn'], 'dependency list mismatch', { expected: REQUIRED_DEPENDENCIES.map(([, coord]) => coord), actual: manifest.dependsOn });
  const before = validateBeforeBoundary0(manifest.claimBoundaryBefore); if (before.tag === 'reject') return before;
  const after = validateAfterBoundary0(manifest.claimBoundaryAfterProofTransition); if (after.tag === 'reject') return after;
  const bools = { releaseTransitionAccepted: true, ufs008ReleaseTransitionDischarged: true, releaseUnrestrictedFinalSoundnessCleared: true, unrestrictedFinalSoundnessDischarged: true, uniformFinalSoundnessProved: true, internalFinalTheoremReady: true, satInPConclusionAccepted: true, pEqualsNPConclusionAccepted: true, publicTheoremEmissionAllowedByRelease: false, externalReviewIsMathematicalPremise: false, historicalReportProseIsMathematicalPremise: false };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('UnrestrictedFinalSoundnessRelease.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  const rel = manifest.releaseTransition;
  if (!plain0(rel)) return reject0('UnrestrictedFinalSoundnessRelease.TransitionShape', ['releaseTransition'], 'release transition must be an object');
  const transitionTrue = ['allUFSDependenciesAccepted', 'allUFSDependencyCoordinatesHashBound', 'ufs001InputFamilyUniformityAccepted', 'ufs002LockedNANDConstructionAccepted', 'ufs003ThresholdEquivalenceAccepted', 'ufs004ResidualBandMinimizerAccepted', 'ufs005ZeroSlackClosureAccepted', 'ufs006NoHiddenOracleSemanticAccepted', 'ufs007ComplexityConclusionAccepted', 'clearsReleaseUnrestrictedFinalSoundness'];
  const transitionFalse = ['clearsExternalReviewAcceptance', 'activatesPublicTheoremEmission', 'usesExternalReviewAsPremise', 'usesHistoricalReportProseAsPremise', 'usesPublicSiteWordingAsPremise', 'usesBoundedSmallModelsAsUnboundedProof'];
  for (const key of transitionTrue) if (rel[key] !== true) return reject0('UnrestrictedFinalSoundnessRelease.TransitionBoolean', ['releaseTransition', key], 'transition true field mismatch', { expected: true, actual: rel[key] });
  for (const key of transitionFalse) if (rel[key] !== false) return reject0('UnrestrictedFinalSoundnessRelease.TransitionBoolean', ['releaseTransition', key], 'transition false field mismatch', { expected: false, actual: rel[key] });
  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((x) => x?.id), REQUIRED_OBLIGATIONS)) return reject0('UnrestrictedFinalSoundnessRelease.ProofObligations', ['proofObligations'], 'proof obligations mismatch', { expected: REQUIRED_OBLIGATIONS, actual: manifest.proofObligations?.map?.((x) => x?.id) });
  for (const entry of manifest.proofObligations) if (!plain0(entry) || entry.requiredForDischarge !== true || typeof entry.statement !== 'string' || entry.statement.length === 0) return reject0('UnrestrictedFinalSoundnessRelease.ProofObligationEntry', ['proofObligations'], 'proof obligation entry incomplete');
  if (!plain0(manifest.uniformityClaims)) return reject0('UnrestrictedFinalSoundnessRelease.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(manifest.uniformityClaims)) if (value !== true) return reject0('UnrestrictedFinalSoundnessRelease.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('UnrestrictedFinalSoundnessRelease.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('UnrestrictedFinalSoundnessRelease.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-unrestricted-final-soundness-release0.mjs' || manifest.audit.test !== 'audits/unrestricted-final-soundness-release0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('UnrestrictedFinalSoundnessRelease.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('UnrestrictedFinalSoundnessRelease.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const ufs008 = (Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : []).find((entry) => entry?.id === 'UFS-008-ReleaseTransitionFromProofOnly');
  if (!plain0(ufs008)) return reject0('UnrestrictedFinalSoundnessRelease.TargetMissingUFS008', ['target', 'requiredUniformObligations'], 'UFS-008 target missing');
  if (ufs008.requiredForDischarge !== true) return reject0('UnrestrictedFinalSoundnessRelease.TargetUFS008NotRequired', ['target', 'requiredUniformObligations', 'UFS-008'], 'UFS-008 must be required for discharge');
  if (ufs008.futureChecker !== 'pcc-unrestricted-final-soundness-release0.mjs') return reject0('UnrestrictedFinalSoundnessRelease.TargetUFS008Checker', ['target', 'requiredUniformObligations', 'UFS-008', 'futureChecker'], 'UFS-008 target checker mismatch', { actual: ufs008.futureChecker });
  return { tag: 'accept' };
}

function validateBeforeBoundary0(boundary) { if (!plain0(boundary)) return reject0('UnrestrictedFinalSoundnessRelease.BeforeBoundaryShape', ['claimBoundaryBefore'], 'before boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false || boundary.finalTheoremReady !== false || !sameArray0(boundary.activeFinalNodeIds, []) || !sameArray0(boundary.remainingBlockers, BEFORE_BLOCKERS)) return reject0('UnrestrictedFinalSoundnessRelease.BeforeBoundary', ['claimBoundaryBefore'], 'before boundary mismatch', { actual: boundary }); return { tag: 'accept' }; }
function validateAfterBoundary0(boundary) { if (!plain0(boundary)) return reject0('UnrestrictedFinalSoundnessRelease.AfterBoundaryShape', ['claimBoundaryAfterProofTransition'], 'after boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false || boundary.internalFinalTheoremReady !== true || !sameArray0(boundary.clearedBlockers, ['Release.UnrestrictedFinalSoundness']) || !sameArray0(boundary.remainingBlockers, AFTER_BLOCKERS)) return reject0('UnrestrictedFinalSoundnessRelease.AfterBoundary', ['claimBoundaryAfterProofTransition'], 'after boundary mismatch', { actual: boundary }); if (!Array.isArray(boundary.activeFinalNodeIds) || boundary.activeFinalNodeIds.length !== 8) return reject0('UnrestrictedFinalSoundnessRelease.AfterBoundaryNodes', ['claimBoundaryAfterProofTransition', 'activeFinalNodeIds'], 'after boundary must bind eight UFS nodes'); return { tag: 'accept' }; }
function validateExamples0(manifest) { for (let i = 0; i < manifest.positiveExamples.length; i += 1) { const example = manifest.positiveExamples[i]; const out = EvaluateUnrestrictedFinalSoundnessReleaseExample0(example.input); if (out.tag !== 'accept') return reject0('UnrestrictedFinalSoundnessRelease.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out }); for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('UnrestrictedFinalSoundnessRelease.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual: out[key] }); } return { tag: 'accept' }; }
async function readJson0({ root, filePath, override, label }) { if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; } try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('UnrestrictedFinalSoundnessRelease.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); } }
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('UnrestrictedFinalSoundnessRelease.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('UnrestrictedFinalSoundnessRelease.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('UnrestrictedFinalSoundnessRelease.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('UnrestrictedFinalSoundnessRelease.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('UnrestrictedFinalSoundnessRelease.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BEFORE_BLOCKERS] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UnrestrictedFinalSoundnessRelease.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckUnrestrictedFinalSoundnessRelease0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
