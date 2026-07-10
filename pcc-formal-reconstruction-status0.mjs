#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckFormalReconstructionStatus0';
const VERSION = 0;
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-10-02';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const SITE_PATH = 'public/pnp-status.json';
const OUTPUT_PATH = 'artifacts/formal-reconstruction-status/latest-verdict.json';

export const FORMAL_RECONSTRUCTION_BLOCKERS0 = Object.freeze([
  'Formal.PinnedLeanBuildAndRootTarget',
  'Formal.ConcreteComplexityModel',
  'Formal.ConcreteSAT',
  'Formal.LockedNANDThreshold',
  'Formal.ResidualBandMinimizer',
  'Formal.ZeroSlack',
  'Formal.PolynomialRuntimeAndCertificateBounds',
  'Formal.RootTheoremAndAxiomAudit',
]);

const VERIFICATION_COMMANDS = Object.freeze([
  'node pcc-formal-reconstruction-status0.mjs --json',
  'node pcc-formal-public-surface0.mjs --json',
  'npm run legacy:v0:check',
  'npm run pnp:verify -- --no-write',
  'lake build PNP',
]);

const NON_CLAIMS = Object.freeze([
  'The repository does not currently establish P = NP.',
  'Legacy JavaScript checker acceptance verifies assertion-bearing records under implemented predicates; it is not a formal proof of the named mathematical propositions.',
  'The current Lean bridge is partial and does not contain the required concrete, assumption-audited root theorem.',
  'External review is optional audit evidence and is not a mathematical premise or release blocker.',
  'Historical releases and coordinates are preserved for auditability but are not current theorem-status authority.',
  'The designated legacy-v0 command replays pinned assertion-checker behavior only; it is neither current theorem authority nor a mathematical proof.',
]);

const SUPERSEDED_COORDINATES = Object.freeze([
  'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01',
  'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01',
  'PNP-ACTIVATED-STATUS-2026-07-05-01',
]);

const SUBORDINATE_LEGACY_SURFACES = Object.freeze([
  'PNP_STATUS.json',
  'status/ACTIVATED_PNP_STATUS.json',
  'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json',
  'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.md',
  'proof-obligations/UNIFORM_INPUT_FAMILY.json',
  'proof-obligations/UNIFORM_INPUT_FAMILY.md',
  'proof-obligations/UNIFORM_LOCKED_NAND_CONSTRUCTION.json',
  'proof-obligations/UNIFORM_LOCKED_NAND_CONSTRUCTION.md',
  'proof-obligations/UNIFORM_LOCKED_NAND_THRESHOLD.json',
  'proof-obligations/UNIFORM_LOCKED_NAND_THRESHOLD.md',
  'proof-obligations/UNIFORM_RESIDUAL_BAND_MINIMIZER.json',
  'proof-obligations/UNIFORM_RESIDUAL_BAND_MINIMIZER.md',
  'proof-obligations/UNIFORM_ZEROSLACK_CLOSURE.json',
  'proof-obligations/UNIFORM_ZEROSLACK_CLOSURE.md',
  'proof-obligations/UNIFORM_NO_HIDDEN_ORACLE_SEMANTIC.json',
  'proof-obligations/UNIFORM_NO_HIDDEN_ORACLE_SEMANTIC.md',
  'proof-obligations/UNIFORM_COMPLEXITY_CONCLUSION.json',
  'proof-obligations/UNIFORM_COMPLEXITY_CONCLUSION.md',
  'proof-obligations/UNRESTRICTED_FINAL_SOUNDNESS_RELEASE.json',
  'proof-obligations/UNRESTRICTED_FINAL_SOUNDNESS_RELEASE.md',
  'proof-obligations/PUBLIC_THEOREM_ACTIVATION.json',
  'proof-obligations/PUBLIC_THEOREM_ACTIVATION.md',
  'proof-obligations/OBLIGATION_LEDGER.json',
  'proof-obligations/GAP_LEDGER.json',
  'proof-obligations/GAP_LEDGER.md',
  'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json',
  'proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.md',
  'complexity/COMPLEXITY_LEDGER.json',
  'complexity/COMPLEXITY_LEDGER.md',
  'trust-base/TRUST_BASE.json',
  'trust-base/SHRINK_PLAN.json',
  'trust-base/SHRINK_PLAN.md',
  'release/PUBLIC_REVIEW_BOUNDARY.json',
  'release/PUBLIC_REVIEW_BOUNDARY.md',
  'release/PUBLIC_REVIEW_HANDOFF.json',
  'release/PUBLIC_REVIEW_HANDOFF.md',
  'review/PUBLIC_REVIEW_CHECKLIST.json',
  'review/PUBLIC_REVIEW_CHECKLIST.md',
  'release/PUBLIC_THEOREM_EMISSION_DENIAL.json',
  'release/PUBLIC_THEOREM_EMISSION_DENIAL.md',
  'release/PUBLIC_THEOREM_EMISSION_GATE.json',
  'release/PUBLIC_THEOREM_EMISSION_GATE.md',
  'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json',
  'release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.md',
  'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json',
  'release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.md',
  'release/RELEASE_BLOCKER_CLEARANCE.json',
  'release/RELEASE_BLOCKER_CLEARANCE.md',
  'review/EXTERNAL_REVIEW_STATUS.md',
  'canonical_proof_report.tex',
  'canonical_proof_report.pdf',
  'REVIEWER_MAP.md',
  'TRUST_BASE.md',
  'PUBLIC_REVIEW.json',
  'PUBLIC_REVIEW.md',
  'RELEASE_LADDER.md',
  'release/RELEASE_LADDER.json',
  'review/EXTERNAL_REVIEW_STATUS.json',
]);

const SUBORDINATE_LEGACY_SURFACE_ROOTS = Object.freeze([
  'checker-cycles/',
  'checker-mutations/',
  'checker-totality/',
  'complexity/',
  'independent-verifiers/',
  'kernel/',
  'oracle-audit/',
  'proof-obligations/',
  'release/',
  'report-bindings/',
  'reproducibility/',
  'review/',
  'trust-base/',
  'artifacts/multi-platform-ci/',
  'artifacts/regeneration/',
  'archive/legacy-v0/',
]);

const ACTIVE_CORE_WORKFLOWS = Object.freeze([
  '.github/workflows/ci.yml',
  '.github/workflows/lean-bridge.yml',
  '.github/workflows/pnp-verify-all.yml',
  '.github/workflows/proof-development.yml',
]);

const HISTORICAL_REPLAY_WORKFLOWS = Object.freeze([
  '.github/workflows/legacy-v0-replay.yml',
]);

const ACTIVE_COMPANION_WORKFLOWS = Object.freeze([
  '.github/workflows/ci.yml',
  '.github/workflows/pnp-public-payloads.yml',
  '.github/workflows/pnp-upstream-status-consistency.yml',
  '.github/workflows/pnp-verification-run-issue-ingest.yml',
  '.github/workflows/pnp-verifier-run-import.yml',
  '.github/workflows/sync-public-access-report.yml',
]);

const EXACT_FIELDS = Object.freeze({
  kind: 'PNPFormalReconstructionStatus0',
  version: VERSION,
  project: 'PNP',
  coordinate: COORDINATE,
  status: 'formal-reconstruction-in-progress',
  claimStatus: 'formal-reconstruction-in-progress',
  currentStatusAuthority: true,
  targetTheorem: 'P = NP',
  mathematicalTheoremEstablished: false,
  publicTheoremEmissionAllowed: false,
  publicTheoremStatement: null,
  publicTheoremConclusion: null,
  finalTheoremReady: false,
  internalFinalTheoremReady: false,
  unrestrictedFinalSoundnessDischarged: false,
  uniformFinalSoundnessProved: false,
  satInPConclusionAccepted: false,
  pEqualsNPConclusionAccepted: false,
  rootLeanTheorem: 'PNP.Main.p_eq_np',
  rootLeanTheoremPresent: false,
  rootLeanTheoremBuilt: false,
  rootLeanTheoremAxiomAuditPassed: false,
  projectSpecificAxiomsRemaining: true,
  sorryOrAdmitInRootDependencyClosure: null,
  checkerAcceptanceIsMathematicalProof: false,
  legacyCheckerStackStatus: 'historical-assertion-checker-evidence-only',
  externalReviewIsMathematicalPremise: false,
  statusVerificationCommand: 'node pcc-formal-reconstruction-status0.mjs --json',
  legacyCheckerArchiveManifest: 'archive/legacy-v0/ARCHIVE.json',
  legacyCheckerArchiveCheckCommand: 'npm run legacy:v0:check',
  legacyCheckerReplayCommand: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
  publicSurfaceBaselineCoordinate: 'PUBLIC-SURFACE-BASELINE-2026-07-10-LEGACY-V0-ARCHIVED-02',
  formalReconstructionStatusPayload: STATUS_PATH,
  siteStatusPayload: SITE_PATH,
  historicalActivatedStatusCoordinate: 'PNP-ACTIVATED-STATUS-2026-07-05-01',
  reconstructionNotice: 'docs/FORMAL_RECONSTRUCTION.md',
});

export async function CheckFormalReconstructionStatus0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  try {
    const statusRead = await readJson0({
      root,
      filePath: options.statusPath ?? STATUS_PATH,
      override: options.statusOverride,
      bytesOverride: options.statusBytesOverride,
      label: STATUS_PATH,
    });
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);

    const siteRead = await readJson0({
      root,
      filePath: options.sitePath ?? SITE_PATH,
      override: options.siteOverride,
      bytesOverride: options.siteBytesOverride,
      label: SITE_PATH,
    });
    if (siteRead.tag === 'reject') return write0(root, outputPath, writeOutput, siteRead);

    const statusCheck = validateStatus0(statusRead.value, STATUS_PATH);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);
    const siteCheck = validateStatus0(siteRead.value, SITE_PATH);
    if (siteCheck.tag === 'reject') return write0(root, outputPath, writeOutput, siteCheck);

    if (!statusRead.bytes.equals(siteRead.bytes)) {
      return write0(root, outputPath, writeOutput, reject0(
        'FormalReconstructionStatus.SiteMirrorMismatch',
        [SITE_PATH],
        'public status payload must byte-for-byte mirror the formal reconstruction status',
      ));
    }

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORDINATE,
      claimStatus: 'formal-reconstruction-status-accepted',
      formalReconstructionStatusAccepted: true,
      targetTheorem: 'P = NP',
      mathematicalTheoremEstablished: false,
      publicTheoremEmissionAllowed: false,
      publicTheoremStatement: null,
      publicTheoremConclusion: null,
      finalTheoremReady: false,
      internalFinalTheoremReady: false,
      unrestrictedFinalSoundnessDischarged: false,
      uniformFinalSoundnessProved: false,
      satInPConclusionAccepted: false,
      pEqualsNPConclusionAccepted: false,
      rootLeanTheoremPresent: false,
      rootLeanTheoremBuilt: false,
      rootLeanTheoremAxiomAuditPassed: false,
      projectSpecificAxiomsRemaining: true,
      externalReviewIsMathematicalPremise: false,
      legacyCheckerArchiveManifest: 'archive/legacy-v0/ARCHIVE.json',
      legacyCheckerReplayCommand: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
      remainingFormalObligations: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
      remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
      statusPayload: STATUS_PATH,
      siteStatusPayload: SITE_PATH,
      statusSha256: sha2560(statusRead.bytes),
      siteStatusSha256: sha2560(siteRead.bytes),
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0(
      'FormalReconstructionStatus.UnhandledException',
      [],
      'status checker threw unexpectedly',
      normalizeError0(error),
    ));
  }
}

function validateStatus0(status, label) {
  if (!plainObject0(status)) return reject0('FormalReconstructionStatus.Shape', [label], 'status payload must be an object');
  const expectedKeys = [
    ...Object.keys(EXACT_FIELDS),
    'activeFinalNodeIds',
    'activeCoreWorkflows',
    'historicalReplayWorkflows',
    'activeCompanionWorkflows',
    'supersededCoordinates',
    'subordinateLegacySurfaces',
    'subordinateLegacySurfaceRoots',
    'remainingFormalObligations',
    'remainingBlockers',
    'verificationCommands',
    'nonClaims',
  ].sort();
  const actualKeys = Object.keys(status).sort();
  if (!sameArray0(actualKeys, expectedKeys)) {
    return reject0('FormalReconstructionStatus.Keys', [label], 'status payload keys must match the closed schema', {
      expectedKeys,
      actualKeys,
      missingKeys: expectedKeys.filter((key) => !actualKeys.includes(key)),
      extraKeys: actualKeys.filter((key) => !expectedKeys.includes(key)),
    });
  }
  for (const [field, expected] of Object.entries(EXACT_FIELDS)) {
    if (status[field] !== expected) {
      return reject0('FormalReconstructionStatus.Field', [label, field], 'status field mismatch', {
        expected,
        actual: status[field],
      });
    }
  }
  if (!sameArray0(status.activeFinalNodeIds, [])) {
    return reject0('FormalReconstructionStatus.ActiveFinalNodes', [label, 'activeFinalNodeIds'], 'active final nodes must be empty');
  }
  if (!sameArray0(status.activeCoreWorkflows, ACTIVE_CORE_WORKFLOWS)) {
    return reject0('FormalReconstructionStatus.CoreWorkflows', [label, 'activeCoreWorkflows'], 'active core workflow inventory mismatch');
  }
  if (!sameArray0(status.historicalReplayWorkflows, HISTORICAL_REPLAY_WORKFLOWS)) {
    return reject0('FormalReconstructionStatus.HistoricalReplayWorkflows', [label, 'historicalReplayWorkflows'], 'historical replay workflow inventory mismatch');
  }
  if (!sameArray0(status.activeCompanionWorkflows, ACTIVE_COMPANION_WORKFLOWS)) {
    return reject0('FormalReconstructionStatus.CompanionWorkflows', [label, 'activeCompanionWorkflows'], 'active companion workflow inventory mismatch');
  }
  if (!sameArray0(status.supersededCoordinates, SUPERSEDED_COORDINATES)) {
    return reject0('FormalReconstructionStatus.SupersededCoordinates', [label, 'supersededCoordinates'], 'superseded activation coordinates mismatch');
  }
  if (!sameArray0(status.subordinateLegacySurfaces, SUBORDINATE_LEGACY_SURFACES)) {
    return reject0('FormalReconstructionStatus.LegacySurfaces', [label, 'subordinateLegacySurfaces'], 'subordinate legacy surface list mismatch');
  }
  if (!sameArray0(status.subordinateLegacySurfaceRoots, SUBORDINATE_LEGACY_SURFACE_ROOTS)) {
    return reject0('FormalReconstructionStatus.LegacySurfaceRoots', [label, 'subordinateLegacySurfaceRoots'], 'subordinate legacy surface root list mismatch');
  }
  if (!sameArray0(status.remainingFormalObligations, FORMAL_RECONSTRUCTION_BLOCKERS0)) {
    return reject0('FormalReconstructionStatus.FormalObligations', [label, 'remainingFormalObligations'], 'formal obligations mismatch');
  }
  if (!sameArray0(status.remainingBlockers, FORMAL_RECONSTRUCTION_BLOCKERS0)) {
    return reject0('FormalReconstructionStatus.Blockers', [label, 'remainingBlockers'], 'formal blockers mismatch');
  }
  if (!sameArray0(status.verificationCommands, VERIFICATION_COMMANDS)) {
    return reject0('FormalReconstructionStatus.Commands', [label, 'verificationCommands'], 'verification commands must exactly match the conservative command list', {
      expected: VERIFICATION_COMMANDS,
      actual: status.verificationCommands,
    });
  }
  if (!sameArray0(status.nonClaims, NON_CLAIMS)) {
    return reject0('FormalReconstructionStatus.NonClaims', [label, 'nonClaims'], 'non-claims must exactly match the conservative boundary', {
      expected: NON_CLAIMS,
      actual: status.nonClaims,
    });
  }
  return { tag: 'accept' };
}

async function readJson0({ root, filePath, override, bytesOverride, label }) {
  if (bytesOverride !== undefined) {
    try {
      const bytes = Buffer.isBuffer(bytesOverride) ? bytesOverride : Buffer.from(String(bytesOverride), 'utf8');
      return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
    } catch (error) {
      return reject0('FormalReconstructionStatus.ReadOrParseFailed', [filePath], `could not parse ${label} bytes override`, normalizeError0(error));
    }
  }
  if (override !== undefined) {
    const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, filePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('FormalReconstructionStatus.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error));
  }
}

async function write0(root, outputPath, enabled, verdict) {
  const rendered = { ...verdict, outputPath: enabled ? outputPath : null };
  if (enabled) {
    const absolute = path.join(root, outputPath);
    await mkdir(path.dirname(absolute), { recursive: true });
    await writeFile(absolute, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
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
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    remainingBlockers: [...FORMAL_RECONSTRUCTION_BLOCKERS0],
  };
}

function plainObject0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function sameArray0(left, right) {
  return Array.isArray(left) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function stableStringify0(value) {
  if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`;
  if (plainObject0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
  return JSON.stringify(value);
}

function sha2560(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}

function parseArgs0(argv) {
  const options = { json: false, writeOutput: true };
  for (const arg of argv) {
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    console.error(JSON.stringify(reject0('FormalReconstructionStatus.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)), null, 2));
    process.exit(2);
  }
  const verdict = await CheckFormalReconstructionStatus0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
