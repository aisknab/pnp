#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckFiniteToUnboundedFamilyAudit0';
const VERSION = 0;
const MANIFEST_PATH = 'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json';
const GAP_LEDGER_PATH = 'proof-obligations/GAP_LEDGER.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/finite-to-unbounded-family-audit/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_CRITERIA = [
  'Uniform.InputFamily',
  'Uniform.Generator',
  'Uniform.PolynomialBound',
  'Uniform.SemanticPreservation',
  'Uniform.NoFiniteExtrapolation',
];
const EXPECTED_LINKED_GAPS = [
  'GAP-001-UnrestrictedFinalSoundness',
  'GAP-003-BoundedSmallModelsNotUniformProof',
  'GAP-004-FiniteToUnboundedUniformity',
];
const EXPECTED_LINKED_OBLIGATIONS = [
  'OBL-010-ComplexityImplicationLedger',
  'OBL-014-UnrestrictedFinalSoundnessBlocked',
];

export async function CheckFiniteToUnboundedFamilyAudit0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const gapLedgerPath = options.gapLedgerPath ?? GAP_LEDGER_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readJson0({ root, filePath: manifestPath, override: options.manifestOverride, label: 'finite-to-unbounded audit manifest' });
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);

    const manifestValidation = validateManifest0(manifestRead.value);
    if (manifestValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestValidation);

    const gapRead = await readJson0({ root, filePath: gapLedgerPath, override: options.gapLedgerOverride, label: 'gap ledger' });
    if (gapRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, gapRead);

    const gapValidation = validateGapLedgerLink0(gapRead.value);
    if (gapValidation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, gapValidation);

    const evidenceDigest = await digestEvidence0({ root, paths: manifestRead.value.evidenceSurfaces });
    if (evidenceDigest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, evidenceDigest);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'finite-to-unbounded-family-audit-accepted-under-public-review-boundary',
      manifestPath,
      gapLedgerPath,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      gapLedgerSha256: sha256Hex0(gapRead.bytes),
      finiteToUnboundedFamilyAuditReady: true,
      uniformityRepresented: true,
      uniformAllInputSizesCoverageProved: false,
      polynomialUniformGeneratorProved: false,
      unrestrictedFinalSoundnessDischarged: false,
      publicTheoremEmissionAllowedByAudit: false,
      linkedGap: 'GAP-004-FiniteToUnboundedUniformity',
      gapStatus: gapValidation.gap.status,
      gapSeverity: gapValidation.gap.severity,
      gapBlocker: gapValidation.gap.blocker,
      requiredUniformityCriteria: [...EXPECTED_CRITERIA],
      evidenceFileCount: evidenceDigest.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidenceDigest.evidence)),
      evidence: evidenceDigest.evidence,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('FiniteToUnboundedAudit.UnhandledException', [], 'finite-to-unbounded audit checker threw unexpectedly', normalizeError0(error)));
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
    return reject0('FiniteToUnboundedAudit.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('FiniteToUnboundedAudit.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPFiniteToUnboundedFamilyAudit0') return reject0('FiniteToUnboundedAudit.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('FiniteToUnboundedAudit.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('FiniteToUnboundedAudit.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: manifest.coordinate });
  if (manifest.status !== 'finite-to-unbounded-family-audit-ready') return reject0('FiniteToUnboundedAudit.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.finiteToUnboundedFamilyAuditReady !== true) return reject0('FiniteToUnboundedAudit.ReadyFlag', ['finiteToUnboundedFamilyAuditReady'], 'finiteToUnboundedFamilyAuditReady must be true');
  if (manifest.uniformAllInputSizesCoverageProved !== false) return reject0('FiniteToUnboundedAudit.UniformCoverageOverclaim', ['uniformAllInputSizesCoverageProved'], 'audit cannot claim all input sizes are covered');
  if (manifest.polynomialUniformGeneratorProved !== false) return reject0('FiniteToUnboundedAudit.PolynomialGeneratorOverclaim', ['polynomialUniformGeneratorProved'], 'audit cannot claim a polynomial uniform generator is proved');
  if (manifest.unrestrictedFinalSoundnessDischarged !== false) return reject0('FiniteToUnboundedAudit.UnrestrictedSoundnessOverclaim', ['unrestrictedFinalSoundnessDischarged'], 'audit cannot discharge unrestricted final soundness');
  if (manifest.publicTheoremEmissionAllowedByAudit !== false) return reject0('FiniteToUnboundedAudit.PublicEmissionByAudit', ['publicTheoremEmissionAllowedByAudit'], 'audit cannot allow public theorem emission');

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!plain0(manifest.boundedEvidencePolicy)) return reject0('FiniteToUnboundedAudit.BoundedPolicyShape', ['boundedEvidencePolicy'], 'boundedEvidencePolicy must be an object');
  const policy = manifest.boundedEvidencePolicy;
  if (policy.boundedSmallModelsMaySupportUniformity !== true) return reject0('FiniteToUnboundedAudit.BoundedPolicySupport', ['boundedEvidencePolicy', 'boundedSmallModelsMaySupportUniformity'], 'boundedSmallModelsMaySupportUniformity must be true');
  if (policy.boundedSmallModelsDischargeUniformity !== false) return reject0('FiniteToUnboundedAudit.BoundedPolicyDischarge', ['boundedEvidencePolicy', 'boundedSmallModelsDischargeUniformity'], 'bounded small models cannot discharge uniformity');
  if (policy.finiteTablesMayRepresentSchemaFamilies !== true) return reject0('FiniteToUnboundedAudit.FiniteTablesRepresent', ['boundedEvidencePolicy', 'finiteTablesMayRepresentSchemaFamilies'], 'finite tables may represent schema families');
  if (policy.finiteTablesDischargeAllInputSizesWithoutUniformGenerator !== false) return reject0('FiniteToUnboundedAudit.FiniteTablesDischargeOverclaim', ['boundedEvidencePolicy', 'finiteTablesDischargeAllInputSizesWithoutUniformGenerator'], 'finite tables cannot discharge all input sizes without uniform generator');

  if (!Array.isArray(manifest.requiredUniformityCriteria)) return reject0('FiniteToUnboundedAudit.CriteriaShape', ['requiredUniformityCriteria'], 'criteria must be an array');
  const criteriaIds = manifest.requiredUniformityCriteria.map((entry) => entry?.id);
  if (!sameArray0(criteriaIds, EXPECTED_CRITERIA)) return reject0('FiniteToUnboundedAudit.CriteriaIds', ['requiredUniformityCriteria'], 'criteria ids must stay exact and ordered', { expected: EXPECTED_CRITERIA, actual: criteriaIds });
  for (let index = 0; index < manifest.requiredUniformityCriteria.length; index += 1) {
    const entry = manifest.requiredUniformityCriteria[index];
    if (!plain0(entry) || !nonempty0(entry.description)) return reject0('FiniteToUnboundedAudit.CriteriaEntry', ['requiredUniformityCriteria', index], 'criterion entry must have description');
    if (entry.currentStatus !== 'represented-not-discharged') return reject0('FiniteToUnboundedAudit.CriteriaStatus', ['requiredUniformityCriteria', index, 'currentStatus'], 'criterion status must remain represented-not-discharged');
  }

  if (!sameArray0(manifest.linkedGaps, EXPECTED_LINKED_GAPS)) return reject0('FiniteToUnboundedAudit.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: EXPECTED_LINKED_GAPS, actual: manifest.linkedGaps });
  if (!sameArray0(manifest.linkedObligations, EXPECTED_LINKED_OBLIGATIONS)) return reject0('FiniteToUnboundedAudit.LinkedObligations', ['linkedObligations'], 'linked obligations mismatch', { expected: EXPECTED_LINKED_OBLIGATIONS, actual: manifest.linkedObligations });
  const evidenceCheck = validateStringArray0(manifest.evidenceSurfaces, ['evidenceSurfaces'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;

  if (!plain0(manifest.currentVerdict)) return reject0('FiniteToUnboundedAudit.CurrentVerdictShape', ['currentVerdict'], 'currentVerdict must be an object');
  if (manifest.currentVerdict.uniformityRepresented !== true) return reject0('FiniteToUnboundedAudit.UniformityRepresentedFlag', ['currentVerdict', 'uniformityRepresented'], 'uniformityRepresented must be true');
  if (manifest.currentVerdict.uniformityClosed !== false) return reject0('FiniteToUnboundedAudit.UniformityClosedOverclaim', ['currentVerdict', 'uniformityClosed'], 'uniformityClosed must be false');
  if (manifest.currentVerdict.activationBlockerCleared !== false) return reject0('FiniteToUnboundedAudit.ActivationBlockerClearedOverclaim', ['currentVerdict', 'activationBlockerCleared'], 'activationBlockerCleared must be false');
  if (!nonempty0(manifest.currentVerdict.reason)) return reject0('FiniteToUnboundedAudit.CurrentVerdictReason', ['currentVerdict', 'reason'], 'current verdict reason must be non-empty');

  const nonClaimsCheck = validateStringArray0(manifest.nonClaims, ['nonClaims'], true);
  if (nonClaimsCheck.tag === 'reject') return nonClaimsCheck;

  if (!plain0(manifest.audit)) return reject0('FiniteToUnboundedAudit.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-finite-to-unbounded-family-audit0.mjs',
    test: 'audits/finite-to-unbounded-family-audit0.test.mjs',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('FiniteToUnboundedAudit.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: manifest.audit[key] });
  }

  return { tag: 'accept' };
}

function validateGapLedgerLink0(gapLedger) {
  if (!plain0(gapLedger)) return reject0('FiniteToUnboundedAudit.GapLedgerShape', ['gapLedger'], 'gap ledger must be an object');
  if (gapLedger.kind !== 'PNPGapLedger0') return reject0('FiniteToUnboundedAudit.GapLedgerKind', ['gapLedger', 'kind'], 'gap ledger kind mismatch');
  const gap = Array.isArray(gapLedger.gaps) ? gapLedger.gaps.find((entry) => entry?.id === 'GAP-004-FiniteToUnboundedUniformity') : null;
  if (!plain0(gap)) return reject0('FiniteToUnboundedAudit.Gap004Missing', ['gapLedger', 'gaps'], 'GAP-004 must exist in gap ledger');
  if (gap.status !== 'represented-not-discharged') return reject0('FiniteToUnboundedAudit.Gap004Status', ['gapLedger', 'GAP-004-FiniteToUnboundedUniformity', 'status'], 'GAP-004 must be represented-not-discharged after this audit', { actual: gap.status });
  if (gap.severity !== 'activation-blocking') return reject0('FiniteToUnboundedAudit.Gap004Severity', ['gapLedger', 'GAP-004-FiniteToUnboundedUniformity', 'severity'], 'GAP-004 must remain activation-blocking');
  if (gap.blocker !== 'Release.UnrestrictedFinalSoundness') return reject0('FiniteToUnboundedAudit.Gap004Blocker', ['gapLedger', 'GAP-004-FiniteToUnboundedUniformity', 'blocker'], 'GAP-004 must remain tied to Release.UnrestrictedFinalSoundness');
  if (gap.ownerSurface !== 'finite-to-unbounded-family-audit') return reject0('FiniteToUnboundedAudit.Gap004Owner', ['gapLedger', 'GAP-004-FiniteToUnboundedUniformity', 'ownerSurface'], 'GAP-004 owner surface mismatch', { actual: gap.ownerSurface });
  const requiredEvidence = [
    'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json',
    'pcc-finite-to-unbounded-family-audit0.mjs',
    'audits/finite-to-unbounded-family-audit0.test.mjs',
  ];
  for (const evidence of requiredEvidence) {
    if (!Array.isArray(gap.evidenceFiles) || !gap.evidenceFiles.includes(evidence)) return reject0('FiniteToUnboundedAudit.Gap004Evidence', ['gapLedger', 'GAP-004-FiniteToUnboundedUniformity', 'evidenceFiles'], 'GAP-004 must include finite-to-unbounded audit evidence', { missing: evidence });
  }
  if (gap.publicTheoremEmissionAllowedByGap !== false) return reject0('FiniteToUnboundedAudit.Gap004PublicEmission', ['gapLedger', 'GAP-004-FiniteToUnboundedUniformity', 'publicTheoremEmissionAllowedByGap'], 'GAP-004 cannot allow public theorem emission');
  return { tag: 'accept', gap };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('FiniteToUnboundedAudit.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('FiniteToUnboundedAudit.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('FiniteToUnboundedAudit.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('FiniteToUnboundedAudit.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('FiniteToUnboundedAudit.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function digestEvidence0({ root, paths }) {
  const evidence = [];
  for (const relativePath of paths) {
    const file = await digestFile0(root, relativePath, ['evidenceSurfaces']);
    if (file.tag === 'reject') return file;
    evidence.push(file);
  }
  return { tag: 'accept', evidence };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('FiniteToUnboundedAudit.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('FiniteToUnboundedAudit.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('FiniteToUnboundedAudit.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('FiniteToUnboundedAudit.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('FiniteToUnboundedAudit.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!nonempty0(value[index])) return reject0('FiniteToUnboundedAudit.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
  }
  return { tag: 'accept' };
}

function safeJoin0(root, relativePath) {
  if (!nonempty0(relativePath) || path.isAbsolute(relativePath)) return null;
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(resolvedRoot, relativePath);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return null;
  return resolved;
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

function stableStringify0(value) {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map((entry) => stableStringify0(entry)).join(',')}]`;
  return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
}

function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), manifestPath: MANIFEST_PATH, gapLedgerPath: GAP_LEDGER_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--manifest') options.manifestPath = requireValue0(argv, ++index, '--manifest');
    else if (arg === '--gap-ledger') options.gapLedgerPath = requireValue0(argv, ++index, '--gap-ledger');
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
  console.log(`Usage: node pcc-finite-to-unbounded-family-audit0.mjs [options]\n\nOptions:\n  --json                 Emit verdict JSON.\n  --no-write             Do not write artifacts/finite-to-unbounded-family-audit/latest-verdict.json.\n  --root <path>          Repository root. Defaults to cwd.\n  --manifest <path>      Audit manifest path relative to root.\n  --gap-ledger <path>    Gap ledger path relative to root.\n  --output <path>        Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad finite-to-unbounded audit CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckFiniteToUnboundedFamilyAudit0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
