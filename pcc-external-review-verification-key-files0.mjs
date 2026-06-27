import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewVerificationKeyRegistry0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY0,
  EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_COORDINATE0,
  makeExternalReviewVerificationKeyRegistryInput0,
} from './pcc-external-review-verification-key-registry0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_COORDINATE0 =
  'ExternalReview.VerificationKeyFiles';

export const EXTERNAL_REVIEW_VERIFICATION_KEY_DIRECTORY0 =
  'external-review/keys/';

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0 = Object.freeze({
  kind: 'ExternalReviewVerificationKeyFileManifest0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewVerificationKeyRegistry0',
  keyDirectory: EXTERNAL_REVIEW_VERIFICATION_KEY_DIRECTORY0,
  manifestPath: 'external-review/keys/MANIFEST.json',
  readmePath: 'external-review/keys/README.md',
  acceptedKeyFileExtensions: Object.freeze(['.pub', '.asc', '.minisig.pub']),
  registryDigest: digestCanonical0(EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY0),
  registryStatus: 'pending-reviewer-key-files',
  verificationKeyFileCount: 0,
  trustedReviewerKeyFileCount: 0,
  revokedReviewerKeyFileCount: 0,
  reviewerKeyFiles: Object.freeze([]),
  externalReviewVerificationKeyFileIntakeReady: true,
  externalReviewVerificationKeyFilesReady: false,
  externalReviewVerificationKeysReady: false,
  externalReviewVerifiedSignaturesReady: false,
  externalReviewSignedFindingFilesReady: false,
  externalReviewSignedFindingsReady: false,
  externalReviewAcceptanceReady: false,
  externalReviewAcceptanceReleased: false,
  externalReviewAcceptanceNotClaimed: true,
  unrestrictedFinalSoundnessReady: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  sealedReleaseNotOverwritten: true,
});

export const EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_POLICY0 = Object.freeze({
  kind: 'ExternalReviewVerificationKeyFilesPolicy0',
  version: CHECKER_VERSION,
  requiresVerificationKeyRegistryAcceptance: true,
  requiresExactEmptyVerificationKeyFileManifest: true,
  requiresNoTrustedReviewerKeyWithoutDigestBoundKeyFile: true,
  requiresNoVerifiedSignatureWithoutTrustedReviewerKey: true,
  requiresNoCallerSuppliedAcceptance: true,
  representsVerificationKeyFileIntakeOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeExternalReviewVerificationKeyFilesSuite0({
  KeyFileManifest = EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewVerificationKeyFilesBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_COORDINATE0,
    keyFileManifestDigest: digestCanonical0(KeyFileManifest),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewVerificationKeyFilesSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.verification-key-files.phase53',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_POLICY0 },
  });
}

export function makeExternalReviewVerificationKeyFilesInput0({
  PredecessorInput = makeExternalReviewVerificationKeyRegistryInput0(),
  KeyFileManifest = EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0,
  KeyFilesGate = makeExternalReviewVerificationKeyFilesSuite0({
    KeyFileManifest,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewVerificationKeyFilesInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    KeyFileManifest,
    KeyFilesGate,
    Policy: { ...EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_POLICY0 },
  });
}

export async function CheckExternalReviewVerificationKeyFiles0(input) {
  const checker = 'CheckExternalReviewVerificationKeyFiles0';
  const shape = validateInputShape0(input);
  if (!shape.ok) return reject0(checker, `${checker}.input`, shape.path, shape.witness);
  const manifest = validateKeyFileManifest0(input.KeyFileManifest);
  if (!manifest.ok) return reject0(checker, `${checker}.keyFileManifest`, manifest.path, manifest.witness);
  const suite = validateGateSuite0(input.KeyFilesGate, input.KeyFileManifest);
  if (!suite.ok) return reject0(checker, `${checker}.keyFilesGate`, suite.path, suite.witness);

  const predecessor = await callChecker0(
    'CheckExternalReviewVerificationKeyRegistry0',
    () => CheckExternalReviewVerificationKeyRegistry0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'verification-key file gate requires an accepted key-registry predecessor',
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
      'verification-key file intake supplies no trusted reviewer key or verified acceptance',
    ),
  ];
  const nf = {
    kind: 'ExternalReviewVerificationKeyFiles0NF',
    checker,
    version: CHECKER_VERSION,
    externalReviewVerificationKeyFileIntakeReady: true,
    externalReviewVerificationKeyFilesReady: false,
    externalReviewVerificationKeysReady: false,
    externalReviewVerifiedSignaturesReady: false,
    externalReviewSignedFindingFilesReady: false,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    keyFileManifest: input.KeyFileManifest,
    keyFileManifestDigest: digestCanonical0(input.KeyFileManifest),
    verificationKeyFileCount: input.KeyFileManifest.verificationKeyFileCount,
    trustedReviewerKeyFileCount: input.KeyFileManifest.trustedReviewerKeyFileCount,
    revokedReviewerKeyFileCount: input.KeyFileManifest.revokedReviewerKeyFileCount,
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
  if (!isPlainObject0(input)) return validationReject0([], 'verification-key file input must be an object');
  if (input.kind !== 'ExternalReviewVerificationKeyFilesInput0') return validationReject0(['kind'], 'verification-key file input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'verification-key file input version mismatch');
  const required = ['PredecessorInput', 'KeyFileManifest', 'KeyFilesGate', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'verification-key file input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_VERIFICATION_KEY_FILES_POLICY0)) return validationReject0(['Policy'], 'verification-key file policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'verification-key file checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateKeyFileManifest0(manifest) {
  if (!sameCanonical0(manifest, EXTERNAL_REVIEW_VERIFICATION_KEY_FILE_MANIFEST0)) return validationReject0(['KeyFileManifest'], 'verification-key file checker requires the exact empty key-file manifest');
  return { ok: true };
}

function validateGateSuite0(suite, keyFileManifest) {
  const expected = makeExternalReviewVerificationKeyFilesSuite0({
    KeyFileManifest: keyFileManifest,
  });
  if (!sameCanonical0(suite, expected)) return validationReject0(['KeyFilesGate'], 'verification-key file suite must match the computed key-file binding');
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
