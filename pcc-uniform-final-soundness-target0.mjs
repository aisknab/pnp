#!/usr/bin/env node

import { EnforceHistoricalReplayCli0, LegacyReplayRequiredReject0 } from './pcc-legacy-replay-gate0.mjs';

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckUniformFinalSoundnessTarget0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const GAP_LEDGER_PATH = 'proof-obligations/GAP_LEDGER.json';
const OUT = 'artifacts/uniform-final-soundness-target/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_OBLIGATIONS = [
  'UFS-001-InputFamilyUniformity',
  'UFS-002-LockedNANDConstructionUniformPolynomial',
  'UFS-003-ThresholdEquivalenceAllInputs',
  'UFS-004-ResidualBandMinimizerUniformPolynomial',
  'UFS-005-ZeroSlackContradictionUniform',
  'UFS-006-NoHiddenOracleSemanticCompleteness',
  'UFS-007-ComplexityConclusionUniform',
  'UFS-008-ReleaseTransitionFromProofOnly',
];
const REQUIRED_GAPS = [
  'GAP-001-UnrestrictedFinalSoundness',
  'GAP-003-BoundedSmallModelsNotUniformProof',
  'GAP-004-FiniteToUnboundedUniformity',
  'GAP-005-NoHiddenOracleSemanticCompleteness',
];
const ACTIVATION_FALSE_FLAGS = [
  'uniformFinalSoundnessProved',
  'unrestrictedFinalSoundnessDischarged',
  'finiteToUnboundedUniformityDischarged',
  'boundedSmallModelsLiftedToUniformProof',
  'publicTheoremEmissionAllowedByTarget',
];

export async function CheckUniformFinalSoundnessTarget0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  if (options.historicalReplay !== true) return write0(root, outputPath, writeOutput, LegacyReplayRequiredReject0(CHECKER, BLOCKERS));
  try {
    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'uniform final soundness target manifest' });
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const gapRead = await readJson0({ root, filePath: options.gapLedgerPath ?? GAP_LEDGER_PATH, override: options.gapLedgerOverride, label: 'gap ledger' });
    if (gapRead.tag === 'reject') return write0(root, outputPath, writeOutput, gapRead);
    const gapCheck = validateGapLedger0(gapRead.value);
    if (gapCheck.tag === 'reject') return write0(root, outputPath, writeOutput, gapCheck);

    const evidence = await digestEvidence0({ root, paths: manifestRead.value.evidenceSurfaces });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      manifestPath: options.manifestPath ?? MANIFEST_PATH,
      gapLedgerPath: options.gapLedgerPath ?? GAP_LEDGER_PATH,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      gapLedgerSha256: sha256Hex0(gapRead.bytes),
      claimStatus: 'uniform-final-soundness-target-ready-not-discharged',
      uniformFinalSoundnessTargetReady: true,
      uniformFinalSoundnessProved: false,
      unrestrictedFinalSoundnessDischarged: false,
      finiteToUnboundedUniformityDischarged: false,
      requiredUniformObligationCount: REQUIRED_OBLIGATIONS.length,
      linkedGapCount: REQUIRED_GAPS.length,
      externalReviewIsMathematicalPremise: false,
      codeBoundUniformProofRequired: true,
      nextProofSurface: 'pcc-uniform-input-family0.mjs',
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('UniformFinalSoundnessTarget.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
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
    return reject0('UniformFinalSoundnessTarget.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('UniformFinalSoundnessTarget.ManifestShape', [], 'manifest must be an object');
  const exact = [
    ['kind', 'PNPUniformFinalSoundnessTarget0'],
    ['version', VERSION],
    ['coordinate', COORD],
    ['status', 'uniform-final-soundness-target-ready'],
  ];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('UniformFinalSoundnessTarget.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  if (manifest.uniformFinalSoundnessTargetReady !== true) return reject0('UniformFinalSoundnessTarget.ReadyFlag', ['uniformFinalSoundnessTargetReady'], 'target-ready flag must be true');
  for (const flag of ACTIVATION_FALSE_FLAGS) if (manifest[flag] !== false) return reject0('UniformFinalSoundnessTarget.ActivationOverclaim', [flag], `${flag} must remain false in target PR`, { actual: manifest[flag] });

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(manifest.theoremToDischarge) || !nonempty0(manifest.theoremToDischarge.statement)) return reject0('UniformFinalSoundnessTarget.TheoremShape', ['theoremToDischarge'], 'theorem target must be explicit');
  if (!String(manifest.theoremToDischarge.inputQuantifier ?? '').includes('all finite')) return reject0('UniformFinalSoundnessTarget.TheoremQuantifier', ['theoremToDischarge', 'inputQuantifier'], 'target must quantify over all finite inputs');
  if (!Array.isArray(manifest.theoremToDischarge.mustNotUse) || manifest.theoremToDischarge.mustNotUse.length < 4) return reject0('UniformFinalSoundnessTarget.MustNotUse', ['theoremToDischarge', 'mustNotUse'], 'mustNotUse list too small');

  if (!Array.isArray(manifest.requiredUniformObligations)) return reject0('UniformFinalSoundnessTarget.ObligationShape', ['requiredUniformObligations'], 'obligations must be an array');
  const ids = manifest.requiredUniformObligations.map((entry) => entry?.id);
  if (!sameArray0(ids, REQUIRED_OBLIGATIONS)) return reject0('UniformFinalSoundnessTarget.ObligationIds', ['requiredUniformObligations'], 'obligation ids mismatch', { expected: REQUIRED_OBLIGATIONS, actual: ids });
  for (let i = 0; i < manifest.requiredUniformObligations.length; i += 1) {
    const entry = manifest.requiredUniformObligations[i];
    if (!plain0(entry)) return reject0('UniformFinalSoundnessTarget.ObligationEntry', ['requiredUniformObligations', i], 'obligation entry must be an object');
    if (entry.currentStatus !== 'target-defined') return reject0('UniformFinalSoundnessTarget.ObligationStatus', ['requiredUniformObligations', i, 'currentStatus'], 'target PR may only define obligation targets');
    if (entry.requiredForDischarge !== true) return reject0('UniformFinalSoundnessTarget.ObligationRequired', ['requiredUniformObligations', i, 'requiredForDischarge'], 'every obligation must be required');
    if (!nonempty0(entry.statement) || !nonempty0(entry.futureChecker) || !nonempty0(entry.acceptanceCriterion)) return reject0('UniformFinalSoundnessTarget.ObligationCompleteness', ['requiredUniformObligations', i], 'obligation must have statement, futureChecker, and acceptanceCriterion');
    if (!entry.futureChecker.endsWith('.mjs')) return reject0('UniformFinalSoundnessTarget.ObligationChecker', ['requiredUniformObligations', i, 'futureChecker'], 'future checker must be an mjs file');
  }

  if (!sameArray0(manifest.linkedGaps, REQUIRED_GAPS)) return reject0('UniformFinalSoundnessTarget.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_GAPS, actual: manifest.linkedGaps });
  if (!plain0(manifest.activationDiscipline)) return reject0('UniformFinalSoundnessTarget.ActivationDisciplineShape', ['activationDiscipline'], 'activation discipline must be an object');
  if (manifest.activationDiscipline.externalReviewIsPremise !== false) return reject0('UniformFinalSoundnessTarget.ExternalReviewPremise', ['activationDiscipline', 'externalReviewIsPremise'], 'external review cannot be a mathematical premise');
  if (manifest.activationDiscipline.historicalReportProseIsPremise !== false) return reject0('UniformFinalSoundnessTarget.ReportProsePremise', ['activationDiscipline', 'historicalReportProseIsPremise'], 'historical report prose cannot be a premise');
  if (manifest.activationDiscipline.boundedEvidenceDischargesTheorem !== false) return reject0('UniformFinalSoundnessTarget.BoundedEvidenceOverclaim', ['activationDiscipline', 'boundedEvidenceDischargesTheorem'], 'bounded evidence cannot discharge theorem');
  if (manifest.activationDiscipline.uniformCodeProofRequired !== true) return reject0('UniformFinalSoundnessTarget.UniformCodeProof', ['activationDiscipline', 'uniformCodeProofRequired'], 'uniform code proof must be required');

  const evidenceCheck = validateStringArray0(manifest.evidenceSurfaces, ['evidenceSurfaces'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;
  const nonClaimsCheck = validateStringArray0(manifest.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;

  if (!plain0(manifest.audit)) return reject0('UniformFinalSoundnessTarget.AuditShape', ['audit'], 'audit must be an object');
  const auditExpected = { checker: CHECKER, script: 'pcc-uniform-final-soundness-target0.mjs', test: 'audits/uniform-final-soundness-target0.test.mjs', expectedAcceptTag: 'accept' };
  for (const [key, expected] of Object.entries(auditExpected)) if (manifest.audit[key] !== expected) return reject0('UniformFinalSoundnessTarget.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: manifest.audit[key] });
  return { tag: 'accept' };
}

function validateGapLedger0(gapLedger) {
  if (!plain0(gapLedger) || gapLedger.kind !== 'PNPGapLedger0') return reject0('UniformFinalSoundnessTarget.GapLedgerShape', ['gapLedger'], 'gap ledger must be PNPGapLedger0');
  const gaps = new Map((Array.isArray(gapLedger.gaps) ? gapLedger.gaps : []).map((entry) => [entry?.id, entry]));
  const expectations = {
    'GAP-001-UnrestrictedFinalSoundness': { status: 'blocked-release-gap', blocker: 'Release.UnrestrictedFinalSoundness' },
    'GAP-003-BoundedSmallModelsNotUniformProof': { status: 'bounded-seed-only', blocker: 'Release.UnrestrictedFinalSoundness' },
    'GAP-004-FiniteToUnboundedUniformity': { status: 'represented-not-discharged', blocker: 'Release.UnrestrictedFinalSoundness' },
    'GAP-005-NoHiddenOracleSemanticCompleteness': { status: 'represented-not-discharged', blocker: null },
  };
  for (const [id, expected] of Object.entries(expectations)) {
    const gap = gaps.get(id);
    if (!plain0(gap)) return reject0('UniformFinalSoundnessTarget.GapMissing', ['gapLedger', id], 'required gap missing');
    if (gap.status !== expected.status) return reject0('UniformFinalSoundnessTarget.GapStatus', ['gapLedger', id, 'status'], 'gap status mismatch', { expected: expected.status, actual: gap.status });
    if (gap.blocker !== expected.blocker) return reject0('UniformFinalSoundnessTarget.GapBlocker', ['gapLedger', id, 'blocker'], 'gap blocker mismatch', { expected: expected.blocker, actual: gap.blocker });
    if (gap.publicTheoremEmissionAllowedByGap !== false) return reject0('UniformFinalSoundnessTarget.GapEmission', ['gapLedger', id, 'publicTheoremEmissionAllowedByGap'], 'gap cannot allow theorem emission');
  }
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('UniformFinalSoundnessTarget.BoundaryShape', ['claimBoundary'], 'boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('UniformFinalSoundnessTarget.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false');
  if (boundary.finalTheoremReady !== false) return reject0('UniformFinalSoundnessTarget.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('UniformFinalSoundnessTarget.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('UniformFinalSoundnessTarget.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const rel of paths) {
    try {
      const abs = path.join(root, rel);
      const st = await stat(abs);
      if (!st.isFile()) return reject0('UniformFinalSoundnessTarget.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(abs);
      evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length });
    } catch (error) {
      return reject0('UniformFinalSoundnessTarget.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error));
    }
  }
  return { tag: 'accept', evidence };
}

function validateStringArray0(value, pathArray, nonempty) {
  if (!Array.isArray(value)) return reject0('UniformFinalSoundnessTarget.ArrayShape', pathArray, 'expected array');
  if (nonempty && value.length === 0) return reject0('UniformFinalSoundnessTarget.ArrayEmpty', pathArray, 'array must be non-empty');
  for (let i = 0; i < value.length; i += 1) if (!nonempty0(value[i])) return reject0('UniformFinalSoundnessTarget.ArrayEntry', [...pathArray, i], 'array entry must be non-empty string');
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
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { EnforceHistoricalReplayCli0({ entrypoint: 'pcc-uniform-final-soundness-target0.mjs' }); let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('UniformFinalSoundnessTarget.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } options.historicalReplay = true; const verdict = await CheckUniformFinalSoundnessTarget0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
