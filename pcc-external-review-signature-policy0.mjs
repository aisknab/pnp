import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewTemplateShape0,
  EXTERNAL_REVIEW_TEMPLATE_SHAPE_COORDINATE0,
  EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0,
  makeExternalReviewTemplateShapeInput0,
} from './pcc-external-review-template-shape0.mjs';

import {
  SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0,
} from './pcc-external-review-signed-findings0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_SIGNATURE_POLICY_COORDINATE0 =
  'ExternalReview.SignaturePolicy';

export const EXTERNAL_REVIEW_SIGNATURE_ARTIFACT_CLASSES0 = Object.freeze([
  Object.freeze({
    class: 'detached-ascii-armored-signature',
    extension: '.json.asc',
    digestField: 'signatureDigest',
    verificationStatus: 'not-supplied',
  }),
  Object.freeze({
    class: 'minisign-detached-signature',
    extension: '.minisig',
    digestField: 'signatureDigest',
    verificationStatus: 'not-supplied',
  }),
]);

export const EXTERNAL_REVIEW_SIGNATURE_POLICY0 = Object.freeze({
  kind: 'ExternalReviewSignaturePolicy0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_SIGNATURE_POLICY_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_TEMPLATE_SHAPE_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewTemplateShape0',
  signedFindingSchemaDigest:
    digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
  templateShapeLedgerDigest:
    digestCanonical0(EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0),
  signatureArtifactClasses: EXTERNAL_REVIEW_SIGNATURE_ARTIFACT_CLASSES0,
  acceptedSignatureDigestAlgorithm: 'SHA256',
  signatureDigestRepresentsSignatureBytesOnly: true,
  signedFindingDigestRepresentsCanonicalFindingPayload: true,
  reviewerIdentityDigestRequired: true,
  reviewScopeDigestRequired: true,
  detachedSignatureRequiredForAcceptance: true,
  signatureVerificationKeyNotBundled: true,
  signedFindingFileCount: 0,
  verifiedSignatureCount: 0,
  acceptedSignatureCount: 0,
  rejectedSignatureCount: 0,
  externalReviewSignaturePolicyReady: true,
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

export const EXTERNAL_REVIEW_SIGNATURE_GATE_POLICY0 = Object.freeze({
  kind: 'ExternalReviewSignatureGatePolicy0',
  version: CHECKER_VERSION,
  requiresTemplateShapeAcceptance: true,
  requiresExactSignaturePolicy: true,
  requiresDetachedSignatureForFutureAcceptance: true,
  requiresNoSignatureWithoutDigestBoundFindingFile: true,
  requiresNoCallerSuppliedAcceptance: true,
  representsSignaturePolicyOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeExternalReviewSignaturePolicySuite0({
  SignaturePolicy = EXTERNAL_REVIEW_SIGNATURE_POLICY0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewSignaturePolicyBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_SIGNATURE_POLICY_COORDINATE0,
    signaturePolicyDigest: digestCanonical0(SignaturePolicy),
    gatePolicyDigest: digestCanonical0(EXTERNAL_REVIEW_SIGNATURE_GATE_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewSignaturePolicySuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.signature-policy.phase51',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_SIGNATURE_GATE_POLICY0 },
  });
}

export function makeExternalReviewSignaturePolicyInput0({
  PredecessorInput = makeExternalReviewTemplateShapeInput0(),
  SignaturePolicy = EXTERNAL_REVIEW_SIGNATURE_POLICY0,
  SignatureGate = makeExternalReviewSignaturePolicySuite0({ SignaturePolicy }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewSignaturePolicyInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    SignaturePolicy,
    SignatureGate,
    Policy: { ...EXTERNAL_REVIEW_SIGNATURE_GATE_POLICY0 },
  });
}

export async function CheckExternalReviewSignaturePolicy0(input) {
  const checker = 'CheckExternalReviewSignaturePolicy0';
  const shape = validateInputShape0(input);
  if (!shape.ok) return reject0(checker, `${checker}.input`, shape.path, shape.witness);
  const policy = validateSignaturePolicy0(input.SignaturePolicy);
  if (!policy.ok) return reject0(checker, `${checker}.signaturePolicy`, policy.path, policy.witness);
  const suite = validateGateSuite0(input.SignatureGate, input.SignaturePolicy);
  if (!suite.ok) return reject0(checker, `${checker}.signatureGate`, suite.path, suite.witness);

  const predecessor = await callChecker0(
    'CheckExternalReviewTemplateShape0',
    () => CheckExternalReviewTemplateShape0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'signature policy gate requires an accepted template-shape predecessor',
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
      'signature policy does not supply verified signed external-review acceptance',
    ),
  ];
  const nf = {
    kind: 'ExternalReviewSignaturePolicy0NF',
    checker,
    version: CHECKER_VERSION,
    externalReviewSignaturePolicyReady: true,
    externalReviewVerifiedSignaturesReady: false,
    externalReviewSignedFindingFilesReady: false,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    signaturePolicy: input.SignaturePolicy,
    signaturePolicyDigest: digestCanonical0(input.SignaturePolicy),
    signatureArtifactClassCount:
      input.SignaturePolicy.signatureArtifactClasses.length,
    verifiedSignatureCount: input.SignaturePolicy.verifiedSignatureCount,
    acceptedSignatureCount: input.SignaturePolicy.acceptedSignatureCount,
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
  if (!isPlainObject0(input)) return validationReject0([], 'signature-policy input must be an object');
  if (input.kind !== 'ExternalReviewSignaturePolicyInput0') return validationReject0(['kind'], 'signature-policy input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'signature-policy input version mismatch');
  const required = ['PredecessorInput', 'SignaturePolicy', 'SignatureGate', 'Policy'];
  for (const field of required) {
    if (!Object.hasOwn(input, field)) return validationReject0([field], 'signature-policy input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_SIGNATURE_GATE_POLICY0)) return validationReject0(['Policy'], 'signature-policy gate policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'signature-policy checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateSignaturePolicy0(policy) {
  if (!sameCanonical0(policy, EXTERNAL_REVIEW_SIGNATURE_POLICY0)) return validationReject0(['SignaturePolicy'], 'signature-policy checker requires the exact non-activating signature policy');
  return { ok: true };
}

function validateGateSuite0(suite, signaturePolicy) {
  const expected = makeExternalReviewSignaturePolicySuite0({
    SignaturePolicy: signaturePolicy,
  });
  if (!sameCanonical0(suite, expected)) return validationReject0(['SignatureGate'], 'signature-policy gate suite must match the computed signature-policy binding');
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
