#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckGapLedger0';
const VERSION = 0;
const LEDGER_PATH = 'proof-obligations/GAP_LEDGER.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/gap-ledger/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-GAP-LEDGER-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const ALLOWED_STATUSES = [
  'blocked-release-gap',
  'known-unresolved',
  'represented-not-discharged',
  'explicit-external-trust',
  'bounded-seed-only',
  'reproducibility-hardening-gap',
];
const ALLOWED_SEVERITIES = ['activation-blocking', 'trust-base', 'hardening', 'documentation-boundary'];
const EXPECTED_GAP_IDS = [
  'GAP-001-UnrestrictedFinalSoundness',
  'GAP-002-ExternalReviewAcceptance',
  'GAP-003-BoundedSmallModelsNotUniformProof',
  'GAP-004-FiniteToUnboundedUniformity',
  'GAP-005-NoHiddenOracleSemanticCompleteness',
  'GAP-006-JavaScriptRuntimeTrust',
  'GAP-007-SHA256AndGitIntegrityTrust',
  'GAP-008-FormalSemanticsExtraction',
  'GAP-009-IndependentVerifierCoverage',
  'GAP-010-ContainerDigestPinning',
  'GAP-011-DeterminismScope',
  'GAP-012-HistoricalReportSupersession',
];

export async function CheckGapLedger0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const ledgerPath = options.ledgerPath ?? LEDGER_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const read = await readLedger0({ root, ledgerPath, override: options.ledgerOverride });
    if (read.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, read);

    const validation = validateLedger0(read.ledger);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, validation);

    const digest = await digestGapEvidence0({ root, gaps: read.ledger.gaps });
    if (digest.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, digest);

    const statusCounts = countBy0(read.ledger.gaps.map((gap) => gap.status));
    const severityCounts = countBy0(read.ledger.gaps.map((gap) => gap.severity));
    const activationBlockingGapCount = read.ledger.gaps.filter((gap) => gap.severity === 'activation-blocking').length;
    const externalTrustGapCount = read.ledger.gaps.filter((gap) => gap.status === 'explicit-external-trust').length;

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'gap-ledger-accepted-under-public-review-boundary',
      ledgerPath,
      ledgerSha256: sha256Hex0(read.bytes),
      gapLedgerReady: true,
      allKnownGapsRepresented: true,
      gapLedgerClaimsNoRemainingGaps: false,
      fullGapClosureProved: false,
      publicTheoremEmissionAllowedByLedger: false,
      gapCount: read.ledger.gaps.length,
      gapIds: EXPECTED_GAP_IDS,
      statusCounts,
      severityCounts,
      activationBlockingGapCount,
      externalTrustGapCount,
      evidenceFileCount: digest.evidenceFileCount,
      gapEvidenceDigestLedgerSha256: sha256Text0(stableStringify0(digest.gapDigests)),
      gapDigests: digest.gapDigests,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('GapLedger.UnhandledException', [], 'gap ledger checker threw unexpectedly', normalizeError0(error)));
  }
}

async function readLedger0({ root, ledgerPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', ledger: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, ledgerPath));
    return { tag: 'accept', ledger: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('GapLedger.ReadOrParseFailed', [ledgerPath], 'could not read or parse gap ledger JSON', normalizeError0(error));
  }
}

function validateLedger0(ledger) {
  if (!plain0(ledger)) return reject0('GapLedger.Shape', [], 'ledger must be an object');
  if (ledger.kind !== 'PNPGapLedger0') return reject0('GapLedger.Kind', ['kind'], 'ledger kind mismatch');
  if (ledger.version !== VERSION) return reject0('GapLedger.Version', ['version'], 'ledger version mismatch');
  if (ledger.coordinate !== EXPECTED_COORDINATE) return reject0('GapLedger.Coordinate', ['coordinate'], 'ledger coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: ledger.coordinate });
  if (ledger.status !== 'gap-ledger-ready') return reject0('GapLedger.Status', ['status'], 'ledger status mismatch');
  if (ledger.gapLedgerReady !== true) return reject0('GapLedger.ReadyFlag', ['gapLedgerReady'], 'gapLedgerReady must be true');
  if (ledger.allKnownGapsRepresented !== true) return reject0('GapLedger.AllKnownRepresentedFlag', ['allKnownGapsRepresented'], 'allKnownGapsRepresented must be true');
  if (ledger.gapLedgerClaimsNoRemainingGaps !== false) return reject0('GapLedger.NoRemainingGapsOverclaim', ['gapLedgerClaimsNoRemainingGaps'], 'gap ledger cannot claim no remaining gaps');
  if (ledger.fullGapClosureProved !== false) return reject0('GapLedger.FullClosureOverclaim', ['fullGapClosureProved'], 'gap ledger cannot claim full closure');
  if (ledger.publicTheoremEmissionAllowedByLedger !== false) return reject0('GapLedger.PublicEmissionByLedger', ['publicTheoremEmissionAllowedByLedger'], 'gap ledger cannot allow public theorem emission');

  const boundary = validateBoundary0(ledger.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  const legendCheck = validateLegend0(ledger.gapStatusLegend, ALLOWED_STATUSES, ['gapStatusLegend']);
  if (legendCheck.tag === 'reject') return legendCheck;
  const severityLegendCheck = validateLegend0(ledger.severityLegend, ALLOWED_SEVERITIES, ['severityLegend']);
  if (severityLegendCheck.tag === 'reject') return severityLegendCheck;

  if (!Array.isArray(ledger.gaps)) return reject0('GapLedger.GapsShape', ['gaps'], 'gaps must be an array');
  const actualIds = ledger.gaps.map((gap) => gap?.id);
  if (!sameArray0(actualIds, EXPECTED_GAP_IDS)) return reject0('GapLedger.GapIds', ['gaps'], 'gap ids must stay exact and ordered', { expected: EXPECTED_GAP_IDS, actual: actualIds });

  const seen = new Set();
  for (let index = 0; index < ledger.gaps.length; index += 1) {
    const gap = ledger.gaps[index];
    const check = validateGap0(gap, ['gaps', index], seen);
    if (check.tag === 'reject') return check;
    seen.add(gap.id);
  }

  if (!plain0(ledger.audit)) return reject0('GapLedger.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'pcc-gap-ledger0.mjs',
    test: 'audits/gap-ledger0.test.mjs',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (ledger.audit[key] !== expected) return reject0('GapLedger.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: ledger.audit[key] });
  }

  return { tag: 'accept' };
}

function validateLegend0(legend, expectedKeys, pathArray) {
  if (!plain0(legend)) return reject0('GapLedger.LegendShape', pathArray, 'legend must be an object');
  for (const key of expectedKeys) {
    if (!nonempty0(legend[key])) return reject0('GapLedger.LegendMissing', [...pathArray, key], 'legend is missing required key');
  }
  return { tag: 'accept' };
}

function validateGap0(gap, gapPath, seen) {
  if (!plain0(gap)) return reject0('GapLedger.GapShape', gapPath, 'gap must be an object');
  if (seen.has(gap.id)) return reject0('GapLedger.DuplicateGapId', [...gapPath, 'id'], 'gap ids must be unique', { id: gap.id });
  for (const field of ['id', 'statement', 'status', 'severity', 'ownerSurface', 'closeCondition']) {
    if (!nonempty0(gap[field])) return reject0('GapLedger.GapField', [...gapPath, field], 'gap field must be a non-empty string');
  }
  if (!ALLOWED_STATUSES.includes(gap.status)) return reject0('GapLedger.GapStatus', [...gapPath, 'status'], 'gap status is not allowed', { allowed: ALLOWED_STATUSES, actual: gap.status });
  if (!ALLOWED_SEVERITIES.includes(gap.severity)) return reject0('GapLedger.GapSeverity', [...gapPath, 'severity'], 'gap severity is not allowed', { allowed: ALLOWED_SEVERITIES, actual: gap.severity });
  if (gap.publicTheoremEmissionAllowedByGap !== false) return reject0('GapLedger.GapPublicEmission', [...gapPath, 'publicTheoremEmissionAllowedByGap'], 'individual gap cannot allow public theorem emission');
  const obligationCheck = validateStringArray0(gap.relatedObligations, [...gapPath, 'relatedObligations'], true);
  if (obligationCheck.tag === 'reject') return obligationCheck;
  const evidenceCheck = validateStringArray0(gap.evidenceFiles, [...gapPath, 'evidenceFiles'], true);
  if (evidenceCheck.tag === 'reject') return evidenceCheck;

  const hasBlocker = gap.blocker !== null;
  if (hasBlocker && !EXPECTED_BLOCKERS.includes(gap.blocker)) return reject0('GapLedger.UnknownBlocker', [...gapPath, 'blocker'], 'gap blocker must be one of the active blockers or null', { actual: gap.blocker });
  if (gap.severity === 'activation-blocking' && !hasBlocker) return reject0('GapLedger.ActivationGapNeedsBlocker', gapPath, 'activation-blocking gaps must name an active blocker');
  if (gap.status === 'blocked-release-gap' && !hasBlocker) return reject0('GapLedger.BlockedReleaseGapNeedsBlocker', gapPath, 'blocked release gaps must name an active blocker');
  if (gap.status !== 'blocked-release-gap' && gap.id.startsWith('GAP-00') && gap.severity === 'activation-blocking' && !hasBlocker) return reject0('GapLedger.ActivationGapMissingBlocker', gapPath, 'activation gap is missing blocker');
  if (gap.status === 'explicit-external-trust' && gap.severity !== 'trust-base') return reject0('GapLedger.ExternalTrustSeverity', gapPath, 'explicit external trust gaps must have trust-base severity');
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('GapLedger.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('GapLedger.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('GapLedger.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('GapLedger.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('GapLedger.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact', { expected: EXPECTED_BLOCKERS, actual: boundary.remainingBlockers });
  return { tag: 'accept' };
}

async function digestGapEvidence0({ root, gaps }) {
  const gapDigests = [];
  let evidenceFileCount = 0;
  for (const gap of gaps) {
    const evidenceFiles = [];
    for (const relativePath of gap.evidenceFiles) {
      const file = await digestFile0(root, relativePath, ['gaps', gap.id, 'evidenceFiles']);
      if (file.tag === 'reject') return file;
      evidenceFiles.push(file);
      evidenceFileCount += 1;
    }
    gapDigests.push({
      id: gap.id,
      status: gap.status,
      severity: gap.severity,
      blocker: gap.blocker,
      relatedObligationDigest: sha256Text0(stableStringify0(gap.relatedObligations)),
      evidenceDigest: sha256Text0(stableStringify0(evidenceFiles)),
      evidenceFiles,
    });
  }
  return { tag: 'accept', gapDigests, evidenceFileCount };
}

async function digestFile0(root, relativePath, pathArray) {
  const safePath = safeJoin0(root, relativePath);
  if (safePath === null) return reject0('GapLedger.UnsafePath', [...pathArray, relativePath], 'file path must stay inside repository root');
  try {
    const info = await stat(safePath);
    if (!info.isFile()) return reject0('GapLedger.PathNotFile', [...pathArray, relativePath], 'path must be a file');
    const bytes = await readFile(safePath);
    return { path: relativePath, sha256: sha256Hex0(bytes), size: bytes.length };
  } catch (error) {
    return reject0('GapLedger.PathMissing', [...pathArray, relativePath], 'file path is missing', normalizeError0(error));
  }
}

function validateStringArray0(value, pathArray, nonEmpty) {
  if (!Array.isArray(value)) return reject0('GapLedger.StringArrayShape', pathArray, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return reject0('GapLedger.StringArrayEmpty', pathArray, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!nonempty0(value[index])) return reject0('GapLedger.StringArrayEntry', [...pathArray, index], 'array entry must be a non-empty string');
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

function countBy0(values) {
  const map = new Map();
  for (const value of values) map.set(value, (map.get(value) ?? 0) + 1);
  return Object.fromEntries([...map.entries()].sort(([left], [right]) => left.localeCompare(right)));
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
  const options = { root: process.cwd(), ledgerPath: LEDGER_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--ledger') options.ledgerPath = requireValue0(argv, ++index, '--ledger');
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
  console.log(`Usage: node pcc-gap-ledger0.mjs [options]\n\nOptions:\n  --json             Emit verdict JSON.\n  --no-write         Do not write artifacts/gap-ledger/latest-verdict.json.\n  --root <path>      Repository root. Defaults to cwd.\n  --ledger <path>    Gap ledger path relative to root.\n  --output <path>    Verdict output path relative to root.\n`);
}

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad gap ledger CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await CheckGapLedger0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
