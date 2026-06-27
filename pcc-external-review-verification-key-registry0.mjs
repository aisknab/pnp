import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewSignaturePolicy0,
  EXTERNAL_REVIEW_SIGNATURE_POLICY0,
  EXTERNAL_REVIEW_SIGNATURE_POLICY_COORDINATE0,
  makeExternalReviewSignaturePolicyInput0,
} from './pcc-external-review-signature-policy0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_COORDINATE0 =
  'ExternalReview.VerificationKeyRegistry';

export const EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY0 = Object.freeze({
  kind: 'ExternalReviewVerificationKeyRegistry0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_SIGNATURE_POLICY_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewSignaturePolicy0',
  signaturePolicyDigest: digestCanonical0(EXTERNAL_REVIEW_SIGNATURE_POLICY0),
  registryStatus: 'pending-reviewer-keys',
  verificationKeyCount: 0,
  trustedReviewerKeyCount: 0,
  revokedReviewerKeyCount: 0,
  reviewerKeyRecords: Object.freeze([]),
  acceptedKeyDigestAlgorithm: 'SHA256',
  reviewerIdentityDigestRequired: true,
  reviewScopeDigestRequired: true,
  externalReviewVerificationKeyRegistryReady: true,
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

export const EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_POLICY0 = Object.freeze({
  kind: 'ExternalReviewVerificationKeyRegistryPolicy0',
  version: CHECKER_VERSION,
  requiresSignaturePolicyAcceptance: true,
  requiresExactEmptyVerificationKeyRegistry: true,
  requiresNoVerifiedSignatureWithoutRegisteredReviewerKey: true,
  requiresNoCallerSuppliedAcceptance: true,
  representsKeyRegistryOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeExternalReviewVerificationKeyRegistrySuite0({
  KeyRegistry = EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewVerificationKeyRegistryBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_COORDINATE0,
    keyRegistryDigest: digestCanonical0(KeyRegistry),
    policyDigest:
      digestCanonical0(EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewVerificationKeyRegistrySuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.verification-key-registry.phase52',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_POLICY0 },
  });
}

export function makeExternalReviewVerificationKeyRegistryInput0({
  PredecessorInput = makeExternalReviewSignaturePolicyInput0(),
  KeyRegistry = EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY0,
  KeyRegistryGate = makeExternalReviewVerificationKeyRegistrySuite0({
    KeyRegistry,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewVerificationKeyRegistryInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    KeyRegistry,
    KeyRegistryGate,
    Policy: { ...EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_POLICY0 },
  });
}

export async function CheckExternalReviewVerificationKeyRegistry0(input) {
  const checker = 'CheckExternalReviewVerificationKeyRegistry0';
  const shape = validateInputShape0(input);
  if (!shape.ok) return reject0(checker, `${checker}.input`, shape.path, shape.witness);
  const registry = validateKeyRegistry0(input.KeyRegistry);
  if (!registry.ok) return reject0(checker, `${checker}.keyRegistry`, registry.path, registry.witness);
  const suite = validateGateSuite0(input.KeyRegistryGate, input.KeyRegistry);
  if (!suite.ok) return reject0(checker, `${checker}.keyRegistryGate`, suite.path, suite.witness);

  const predecessor = await callChecker0(
    'CheckExternalReviewSignaturePolicy0',
    () => CheckExternalReviewSignaturePolicy0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'verification-key registry requires an accepted signature-policy predecessor',
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
      'verification-key registry supplies no verified signed external-review acceptance',
    ),
  ];
  const nf = {
    kind: 'ExternalReviewVerificationKeyRegistry0NF',
    checker,
    version: CHECKER_VERSION,
    externalReviewVerificationKeyRegistryReady: true,
    externalReviewVerificationKeysReady: false,
    externalReviewVerifiedSignaturesReady: false,
    externalReviewSignedFindingFilesReady: false,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    keyRegistry: input.KeyRegistry,
    keyRegistryDigest: digestCanonical0(input.KeyRegistry),
    verificationKeyCount: input.KeyRegistry.verificationKeyCount,
    trustedReviewerKeyCount: input.KeyRegistry.trustedReviewerKeyCount,
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
  if (!isPlainObject0(input)) return validationReject0([], 'verification-key registry input must be an object');
  if (input.kind !== 'ExternalReviewVerificationKeyRegistryInput0') return validationReject0(['kind'], 'verification-key registry input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'verification-key registry input version mismatch');
  const required = ['PredecessorInput', 'KeyRegistry', 'KeyRegistryGate', 'Policy'];
  for (const field of required) {
    if (!Object.hasOwn(input, field)) return validationReject0([field], 'verification-key registry input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY_POLICY0)) return validationReject0(['Policy'], 'verification-key registry policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'verification-key registry checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateKeyRegistry0(registry) {
  if (!sameCanonical0(registry, EXTERNAL_REVIEW_VERIFICATION_KEY_REGISTRY0)) return validationReject0(['KeyRegistry'], 'verification-key registry checker requires the exact empty registry');
  return { ok: true };
}

function validateGateSuite0(suite, keyRegistry) {
  const expected = makeExternalReviewVerificationKeyRegistrySuite0({
    KeyRegistry: keyRegistry,
  });
  if (!sameCanonical0(suite, expected)) return validationReject0(['KeyRegistryGate'], 'verification-key registry suite must match the computed registry binding');
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
