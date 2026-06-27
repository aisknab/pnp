import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewVerificationKeyFiles0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_COORDINATE0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_DIRECTORY0,
  makeExternalReviewVerificationKeyFilesInput0,
} from './pcc-external-review-verification-key-files0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_COORDINATE0 =
  'ExternalReview.VerificationKeyFileHashes';

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0 = Object.freeze([
  Object.freeze({
    path: 'external-review/keys/MANIFEST.json',
    sha256:
      'b2859ad352602aedb407d73d915e39f83bdd2968f8021352a244ccdeda4ed2d3',
  }),
  Object.freeze({
    path: 'external-review/keys/README.md',
    sha256:
      '17630eefbe0ae41b4178514014eed9f8e666660ff4dd7b018b995d8125942712',
  }),
]);

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0 = Object.freeze({
  kind: 'ExternalReviewVerificationKeyFileHashLedger0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewVerificationKeyFiles0',
  keyDirectory: EXTERNAL_REVIEW_VERIFICATION_KEY_DIRECTORY0,
  sha256SumsPath: 'external-review/keys/SHA256SUMS',
  manifestPath: 'external-review/keys/MANIFEST.json',
  readmePath: 'external-review/keys/README.md',
  entries: EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0,
  entryCount: EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_ENTRIES0.length,
  manifestDigest: digestCanonical0(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0),
  verificationKeyFileCount: 0,
  trustedReviewerKeyFileCount: 0,
  revokedReviewerKeyFileCount: 0,
  externalReviewVerificationKeyFileHashesReady: true,
  externalReviewVerificationKeyFilesReady: false,
  externalReviewVerificationKeysReady: false,
  externalReviewVerifiedSignaturesReady: false,
  externalReviewAcceptanceReady: false,
  externalReviewAcceptanceReleased: false,
  externalReviewAcceptanceNotClaimed: true,
  unrestrictedFinalSoundnessReady: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  sealedReleaseNotOverwritten: true,
});

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_POLICY0 = Object.freeze({
  kind: 'ExternalReviewVerificationKeyFileHashLedgerPolicy0',
  version: CHECKER_VERSION,
  requiresVerificationKeyFileGateAcceptance: true,
  requiresExactVerificationKeyFileHashLedger: true,
  requiresSha256SumsVerification: true,
  requiresEmptyVerificationKeyFileIntake: true,
  requiresNoTrustedReviewerKeyWithoutDigestBoundKeyFile: true,
  requiresNoCallerSuppliedAcceptance: true,
  representsVerificationKeyFileHashLedgerOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeExternalReviewVerificationKeyFileHashLedgerSuite0({
  HashLedger = EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewVerificationKeyFileHashLedgerBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_COORDINATE0,
    hashLedgerDigest: digestCanonical0(HashLedger),
    policyDigest:
      digestCanonical0(EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewVerificationKeyFileHashLedgerSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.verification-key-file-hashes.phase54',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_POLICY0 },
  });
}

export function makeExternalReviewVerificationKeyFileHashLedgerInput0({
  PredecessorInput = makeExternalReviewVerificationKeyFilesInput0(),
  HashLedger = EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0,
  HashLedgerGate = makeExternalReviewVerificationKeyFileHashLedgerSuite0({
    HashLedger,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewVerificationKeyFileHashLedgerInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    HashLedger,
    HashLedgerGate,
    Policy: { ...EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_POLICY0 },
  });
}

export async function CheckExternalReviewVerificationKeyFileHashLedger0(input) {
  const checker = 'CheckExternalReviewVerificationKeyFileHashLedger0';
  const shape = validateInputShape0(input);
  if (!shape.ok) return reject0(checker, `${checker}.input`, shape.path, shape.witness);
  const ledger = validateHashLedger0(input.HashLedger);
  if (!ledger.ok) return reject0(checker, `${checker}.hashLedger`, ledger.path, ledger.witness);
  const suite = validateGateSuite0(input.HashLedgerGate, input.HashLedger);
  if (!suite.ok) return reject0(checker, `${checker}.hashLedgerGate`, suite.path, suite.witness);

  const predecessor = await callChecker0(
    'CheckExternalReviewVerificationKeyFiles0',
    () => CheckExternalReviewVerificationKeyFiles0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'verification-key file hash ledger requires an accepted key-file predecessor',
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
      'verification-key file hash ledger binds an empty intake and supplies no verified acceptance',
    ),
  ];
  const nf = {
    kind: 'ExternalReviewVerificationKeyFileHashLedger0NF',
    checker,
    version: CHECKER_VERSION,
    externalReviewVerificationKeyFileHashLedgerReady: true,
    externalReviewVerificationKeyFileHashesReady: true,
    externalReviewVerificationKeyFilesReady: false,
    externalReviewVerificationKeysReady: false,
    externalReviewVerifiedSignaturesReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    hashLedger: input.HashLedger,
    hashLedgerDigest: digestCanonical0(input.HashLedger),
    sha256SumsPath: input.HashLedger.sha256SumsPath,
    hashLedgerEntryCount: input.HashLedger.entryCount,
    verificationKeyFileCount: input.HashLedger.verificationKeyFileCount,
    trustedReviewerKeyFileCount: input.HashLedger.trustedReviewerKeyFileCount,
    revokedReviewerKeyFileCount: input.HashLedger.revokedReviewerKeyFileCount,
    remainingBlockers,
    remainingBlockerCoordinates: remainingBlockers.map((entry) => entry.coordinate),
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    sealedReleaseNotOverwritten: true,
    externalReviewAcceptanceNotClaimed: true,
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
  if (!isPlainObject0(input)) return validationReject0([], 'verification-key file hash-ledger input must be an object');
  if (input.kind !== 'ExternalReviewVerificationKeyFileHashLedgerInput0') return validationReject0(['kind'], 'verification-key file hash-ledger input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'verification-key file hash-ledger input version mismatch');
  const required = ['PredecessorInput', 'HashLedger', 'HashLedgerGate', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'verification-key file hash-ledger input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER_POLICY0)) return validationReject0(['Policy'], 'verification-key file hash-ledger policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'verification-key file hash-ledger checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateHashLedger0(hashLedger) {
  if (!sameCanonical0(hashLedger, EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_HASH_LEDGER0)) return validationReject0(['HashLedger'], 'verification-key file hash-ledger checker requires the exact empty-intake SHA256 ledger');
  return { ok: true };
}

function validateGateSuite0(suite, hashLedger) {
  const expected = makeExternalReviewVerificationKeyFileHashLedgerSuite0({
    HashLedger: hashLedger,
  });
  if (!sameCanonical0(suite, expected)) return validationReject0(['HashLedgerGate'], 'verification-key file hash-ledger suite must match the computed hash-ledger binding');
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
