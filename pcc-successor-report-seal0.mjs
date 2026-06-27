import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewVerificationKeyFileHashLedger0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_COORDINATE0,
  makeExternalReviewVerificationKeyFileHashLedgerInput0,
} from './pcc-external-review-verification-key-file-hash-ledger0.mjs';

import {
  PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
} from './pcc-publication-coordinate-gate0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_COORDINATE0 =
  'PNP-REPORT-SEAL-2026-06-27-01';

export const SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_FILE_ENTRIES0 = Object.freeze([
  Object.freeze({
    path: 'successor-report-seals/PNP-REPORT-SEAL-2026-06-27-01/SEAL.json',
    sha256:
      'cb9b44715de8899f1bac5e63b01b2964f4ec4aaea1ce1cd742a0bcfa124fd79d',
  }),
  Object.freeze({
    path: 'successor-report-seals/PNP-REPORT-SEAL-2026-06-27-01/README.md',
    sha256:
      'b163493c6d5296230469d10aeac3d4174fe69bc2b470457ab916c130115e052a',
  }),
]);

export const SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0 = Object.freeze({
  kind: 'SuccessorPublicReviewReportSeal0',
  version: CHECKER_VERSION,
  sealCoordinate: SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_COORDINATE0,
  sealDate: '2026-06-27',
  predecessorReleaseLayerCoordinate:
    EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewVerificationKeyFileHashLedger0',
  predecessorDocumentationCoordinate:
    PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0.coordinateId,
  documentationRevisionPath:
    'documentation-revisions/PNP-DOC-CPR-2026-06-26-01/',
  reportTeXPayloadSha256:
    '9ad7ed91a48662b98432e2b6000beaf06b3ebd2212de3a6d820a7dcbd27e8d9a',
  reportPDFPayloadSha256:
    'f6848d37eb8982f59ca1436352e06559e35aad8ee56956705de2650de1cc45a7',
  sealDirectory:
    'successor-report-seals/PNP-REPORT-SEAL-2026-06-27-01/',
  sha256SumsPath:
    'successor-report-seals/PNP-REPORT-SEAL-2026-06-27-01/SHA256SUMS',
  sealFileEntries: SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_FILE_ENTRIES0,
  sealFileEntryCount: SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_FILE_ENTRIES0.length,
  publicRepository: 'https://github.com/aisknab/pnp',
  historicalSourceTag: 'final-pnp-proof-report-hardened-7072f8d',
  historicalSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
  historicalArtifactTag:
    'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
  historicalReleaseNotOverwritten: true,
  successorSealPurpose: 'public-review-report-framing-and-access-correction',
  publicationFraming: 'public-review',
  sourceAndArtifactAccessPublicWithoutRequest: true,
  directTheoremEmissionReframedAsReviewStatus: true,
  successorReportSealReady: true,
  successorReportArtifactReleaseReady: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIds: Object.freeze([]),
  unrestrictedFinalSoundnessReady: false,
  externalReviewAcceptanceReady: false,
  remainingBlockers: Object.freeze([
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ]),
});

export const SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_POLICY0 = Object.freeze({
  kind: 'SuccessorPublicReviewReportSealPolicy0',
  version: CHECKER_VERSION,
  requiresVerificationKeyFileHashLedgerAcceptance: true,
  requiresExactSuccessorReportSeal: true,
  requiresSuccessorReportSealHashes: true,
  requiresHistoricalReleasePreserved: true,
  requiresPublicReviewFraming: true,
  requiresPublicSourceAndArtifactAccess: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeSuccessorPublicReviewReportSealSuite0({
  ReportSeal = SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0,
} = {}) {
  const base = Object.freeze({
    kind: 'SuccessorPublicReviewReportSealBinding0',
    version: CHECKER_VERSION,
    coordinate: SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_COORDINATE0,
    reportSealDigest: digestCanonical0(ReportSeal),
    policyDigest: digestCanonical0(SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_POLICY0),
  });
  return Object.freeze({
    kind: 'SuccessorPublicReviewReportSealSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.successor-public-review-report-seal.phase55',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_POLICY0 },
  });
}

export function makeSuccessorPublicReviewReportSealInput0({
  PredecessorInput = makeExternalReviewVerificationKeyFileHashLedgerInput0(),
  ReportSeal = SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0,
  ReportSealGate = makeSuccessorPublicReviewReportSealSuite0({ ReportSeal }),
} = {}) {
  return Object.freeze({
    kind: 'SuccessorPublicReviewReportSealInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    ReportSeal,
    ReportSealGate,
    Policy: { ...SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_POLICY0 },
  });
}

export async function CheckSuccessorPublicReviewReportSeal0(input) {
  const checker = 'CheckSuccessorPublicReviewReportSeal0';
  const shape = validateInputShape0(input);
  if (!shape.ok) return reject0(checker, `${checker}.input`, shape.path, shape.witness);
  const seal = validateReportSeal0(input.ReportSeal);
  if (!seal.ok) return reject0(checker, `${checker}.reportSeal`, seal.path, seal.witness);
  const suite = validateGateSuite0(input.ReportSealGate, input.ReportSeal);
  if (!suite.ok) return reject0(checker, `${checker}.reportSealGate`, suite.path, suite.witness);

  const predecessor = await callChecker0(
    'CheckExternalReviewVerificationKeyFileHashLedger0',
    () => CheckExternalReviewVerificationKeyFileHashLedger0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'successor report seal requires an accepted verification-key file hash-ledger predecessor',
      inner: predecessor.ok ? compactRecord0(predecessor.record) : predecessor.witness,
    });
  }

  const remainingBlockers = [
    blocker0(
      UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
      'unrestricted final soundness remains blocked',
    ),
    blocker0(
      EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
      'successor report seal does not supply external-review acceptance',
    ),
  ];
  const nf = {
    kind: 'SuccessorPublicReviewReportSeal0NF',
    checker,
    version: CHECKER_VERSION,
    successorReportSealReady: true,
    successorReportArtifactReleaseReady: false,
    successorReportSeal: input.ReportSeal,
    successorReportSealDigest: digestCanonical0(input.ReportSeal),
    successorReportSealCoordinate: input.ReportSeal.sealCoordinate,
    reportTeXPayloadSha256: input.ReportSeal.reportTeXPayloadSha256,
    reportPDFPayloadSha256: input.ReportSeal.reportPDFPayloadSha256,
    sealFileEntryCount: input.ReportSeal.sealFileEntryCount,
    historicalReleaseNotOverwritten: true,
    sourceAndArtifactAccessPublicWithoutRequest: true,
    directTheoremEmissionReframedAsReviewStatus: true,
    publicReviewPublicationFraming: true,
    unrestrictedFinalSoundnessReady: false,
    externalReviewAcceptanceReady: false,
    remainingBlockers,
    remainingBlockerCoordinates: remainingBlockers.map((entry) => entry.coordinate),
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    sealedReleaseNotOverwritten: true,
    policyDigest: digestCanonical0(input.Policy),
  };
  const digest = digestCanonical0(nf);
  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    nf,
    digest,
  };
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) return validationReject0([], 'successor report seal input must be an object');
  if (input.kind !== 'SuccessorPublicReviewReportSealInput0') return validationReject0(['kind'], 'successor report seal input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'successor report seal input version mismatch');
  const required = ['PredecessorInput', 'ReportSeal', 'ReportSealGate', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'successor report seal input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL_POLICY0)) return validationReject0(['Policy'], 'successor report seal policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'successor report seal checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateReportSeal0(reportSeal) {
  if (!sameCanonical0(reportSeal, SUCCESSOR_PUBLIC_REVIEW_REPORT_SEAL0)) return validationReject0(['ReportSeal'], 'successor report seal checker requires the exact successor public-review report seal');
  return { ok: true };
}

function validateGateSuite0(suite, reportSeal) {
  const expected = makeSuccessorPublicReviewReportSealSuite0({
    ReportSeal: reportSeal,
  });
  if (!sameCanonical0(suite, expected)) return validationReject0(['ReportSealGate'], 'successor report seal suite must match the computed report-seal binding');
  return { ok: true };
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) return { ok: false, witness: { reason: `${name} returned a non-total record`, actual: record } };
    return { ok: true, record };
  } catch (error) {
    return { ok: false, witness: { reason: `${name} threw`, errorName: error?.name ?? null, errorMessage: error?.message ?? String(error) } };
  }
}

function blocker0(coordinate, reason) {
  return Object.freeze({ coordinate, ready: false, reason, digest: digestCanonical0({ coordinate, reason }) });
}

function compactRecord0(record) {
  return { tag: record?.tag ?? null, checker: record?.checker ?? null, coord: record?.Coord ?? record?.coord ?? null, digest: record?.Digest ?? record?.digest ?? null };
}

function reject0(checker, coord, path, witness) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness };
  const digest = digestCanonical0(nf);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, coord, path, witness, digest };
}

function validationReject0(path, reason) { return { ok: false, path, witness: { reason } }; }
function sameCanonical0(left, right) { return stableStringify0(left) === stableStringify0(right); }
function isPlainObject0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
