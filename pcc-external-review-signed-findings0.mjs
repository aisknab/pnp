import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewFindingsRegistry0,
  EXTERNAL_REVIEW_FINDING_KINDS0,
  EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0,
  EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0,
  makeExternalReviewFindingsRegistryInput0,
} from './pcc-external-review-findings-registry0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0 =
  'ExternalReview.SignedFindings';

export const SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0 = Object.freeze({
  kind: 'SignedExternalReviewFindingSchema0',
  version: CHECKER_VERSION,
  coordinate: SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0,
  allowedFindingKinds: [...EXTERNAL_REVIEW_FINDING_KINDS0],
  requiredFindingFields: [...EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0],
  acceptedFindingValues: Object.freeze([
    'accept',
    'reject',
    'revision-request',
  ]),
  requiresReviewerIdentityDigest: true,
  requiresReviewScopeDigest: true,
  requiresFindingDigest: true,
  requiresSignatureDigest: true,
  requiresDocumentationCoordinate: true,
  requiresSealedReleaseCoordinate: true,
  acceptanceRequiresUnrestrictedFinalSoundnessRelease: true,
  publicTheoremEmissionAllowed: false,
});

export const SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0 = Object.freeze({
  kind: 'SignedExternalReviewFindingsBundle0',
  version: CHECKER_VERSION,
  coordinate: SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0,
  registryStatus: 'pending-signed-findings',
  signedFindingCount: 0,
  acceptanceFindingCount: 0,
  rejectionFindingCount: 0,
  revisionRequestFindingCount: 0,
  signedFindings: Object.freeze([]),
  schemaDigest: digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
  signedExternalReviewFindingsReady: false,
  externalReviewAcceptanceReady: false,
  externalReviewAcceptanceReleased: false,
  externalReviewAcceptanceNotClaimed: true,
  unrestrictedFinalSoundnessReady: false,
  unrestrictedFinalSoundnessRequiredForAcceptance: true,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  sealedReleaseNotOverwritten: true,
});

export const SIGNED_EXTERNAL_REVIEW_FINDINGS_POLICY0 = Object.freeze({
  kind: 'SignedExternalReviewFindingsPolicy0',
  version: CHECKER_VERSION,
  requiresFindingsRegistryAcceptance: true,
  requiresFindingsRegistryStillPending: true,
  requiresExactPendingSignedFindingsBundle: true,
  requiresSignedFindingSchemaBinding: true,
  requiresEmptyBundleUntilSignedFindingsExist: true,
  requiresNoUnsignedAcceptance: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const SIGNED_EXTERNAL_REVIEW_FINDINGS_CONTRACT0 = Object.freeze({
  kind: 'SignedExternalReviewFindingsContract0',
  version: CHECKER_VERSION,
  coordinate: SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewFindingsRegistry0',
  bundleKind: SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0.kind,
  schemaDigest: digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
  publicTheoremEmissionAllowed: false,
});

export function makeSignedExternalReviewFindingsSuite0({
  SignedFindingsBundle = SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0,
} = {}) {
  const base = Object.freeze({
    kind: 'SignedExternalReviewFindingsBinding0',
    version: CHECKER_VERSION,
    coordinate: SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0,
    signedFindingsBundleDigest: digestCanonical0(SignedFindingsBundle),
    signedFindingSchemaDigest:
      digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
    checkerContractDigest:
      digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDINGS_CONTRACT0),
    policyDigest: digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDINGS_POLICY0),
  });
  return Object.freeze({
    kind: 'SignedExternalReviewFindingsSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.signed-findings.phase46',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...SIGNED_EXTERNAL_REVIEW_FINDINGS_POLICY0 },
  });
}

export function makeSignedExternalReviewFindingsInput0({
  PredecessorInput = makeExternalReviewFindingsRegistryInput0(),
  SignedFindingsBundle = SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0,
  SignedFindingsGate = makeSignedExternalReviewFindingsSuite0({
    SignedFindingsBundle,
  }),
} = {}) {
  return Object.freeze({
    kind: 'SignedExternalReviewFindingsInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    SignedFindingsBundle,
    SignedFindingsGate,
    Policy: { ...SIGNED_EXTERNAL_REVIEW_FINDINGS_POLICY0 },
  });
}

export async function CheckSignedExternalReviewFindings0(input) {
  const checker = 'CheckSignedExternalReviewFindings0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckExternalReviewFindingsRegistry0',
    () => CheckExternalReviewFindingsRegistry0(input.PredecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckExternalReviewFindingsRegistry0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.findingsRegistryPredecessor.exception`,
      path: ['PredecessorInput'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.findingsRegistryPredecessor`,
      path: ['PredecessorInput'],
      witness: {
        reason: 'signed external-review findings gate requires an accepted findings-registry predecessor',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }

  const predecessorNF = predecessorCall.record.NF
    ?? predecessorCall.record.nf
    ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'findingsRegistryPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.findingsRegistryPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const bundle = validateSignedFindingsBundle0(input.SignedFindingsBundle);
  ledger.push(makeLedgerEntry0(
    'signedFindingsBundle',
    bundle.ok,
    bundle.nf ?? bundle.witness,
  ));
  if (!bundle.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.signedFindingsBundle`,
      bundle,
      ledger,
    );
  }

  const suite = validateGateSuite0(
    input.SignedFindingsGate,
    input.SignedFindingsBundle,
  );
  ledger.push(makeLedgerEntry0(
    'signedFindingsGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.signedFindingsGateSuite`,
      suite,
      ledger,
    );
  }

  const remainingBlockers = [
    Object.freeze({
      coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
      ready: false,
      reason: 'unrestricted final soundness remains blocked until independent unrestricted-soundness review is supplied',
      digest: digestCanonical0({
        coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
    Object.freeze({
      coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
      ready: false,
      reason: 'signed external-review findings bundle is pending; no signed acceptance artifact is supplied',
      signedFindingsBundleDigest: digestCanonical0(input.SignedFindingsBundle),
      digest: digestCanonical0({
        coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
        signedFindingsBundleDigest: digestCanonical0(input.SignedFindingsBundle),
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
  ];

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SignedExternalReviewFindings0NF',
      checker,
      version: CHECKER_VERSION,
      signedExternalReviewFindingsGateReady: true,
      signedExternalReviewFindingsSchemaReady: true,
      signedExternalReviewFindingsBundleReady: true,
      signedExternalReviewFindingsReady: false,
      externalReviewSignedFindingsReady: false,
      externalReviewAcceptanceReady: false,
      externalReviewAcceptanceReleased: false,
      externalReviewAcceptanceBlocked: true,
      unrestrictedFinalSoundnessReady: false,
      unrestrictedFinalSoundnessBlocked: true,

      findingsRegistryPredecessorAccepted: true,
      findingsRegistryPredecessorChecker: predecessorCall.record.checker,
      findingsRegistryPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      predecessorRemainingBlockerCoordinates:
        predecessorNF.remainingBlockerCoordinates ?? [],

      signedFindingSchema:
        SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0,
      signedFindingSchemaDigest:
        digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
      signedFindingsBundle: input.SignedFindingsBundle,
      signedFindingsBundleDigest:
        digestCanonical0(input.SignedFindingsBundle),
      signedFindingCount: input.SignedFindingsBundle.signedFindingCount,
      acceptanceFindingCount:
        input.SignedFindingsBundle.acceptanceFindingCount,
      rejectionFindingCount:
        input.SignedFindingsBundle.rejectionFindingCount,
      revisionRequestFindingCount:
        input.SignedFindingsBundle.revisionRequestFindingCount,
      allowedFindingKinds: [...EXTERNAL_REVIEW_FINDING_KINDS0],
      requiredFindingFields: [...EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0],

      gateBinding: input.SignedFindingsGate.binding,
      gateBindingDigest: input.SignedFindingsGate.binding.bindingDigest,
      remainingBlockers,
      remainingBlockerCoordinates:
        remainingBlockers.map((entry) => entry.coordinate),
      releasePublicTheoremEmissionBlocked: true,
      releasePublicTheoremEmissionBlockerDigest:
        digestCanonical0(remainingBlockers),
      globalSemanticNodeDerivationsReady: true,
      globalFinalDerivationsReady: true,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
      sealedReleaseNotOverwritten: true,
      externalReviewAcceptanceNotClaimed: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'signed external-review findings input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'SignedExternalReviewFindingsInput0') {
    return validationReject0(
      ['kind'],
      'signed external-review findings input kind must be SignedExternalReviewFindingsInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `signed external-review findings input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  const required = [
    'PredecessorInput',
    'SignedFindingsBundle',
    'SignedFindingsGate',
    'Policy',
  ];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'signed external-review findings input is missing a required field',
        { field },
      );
    }
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'signed external-review findings dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (!sameCanonical0(input.Policy, SIGNED_EXTERNAL_REVIEW_FINDINGS_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'signed external-review findings policy must match the fail-closed policy',
      { expected: SIGNED_EXTERNAL_REVIEW_FINDINGS_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'signed external-review findings checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'SignedExternalReviewFindingsInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    externalReviewFindingsRegistryRepresentedReady: true,
    externalReviewFindingsRegistryReady: true,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceReleased: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    unrestrictedFinalSoundnessBlocked: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    releasePublicTheoremEmissionBlocked: true,
    sealedReleaseNotOverwritten: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['FindingsRegistryPredecessor', 'NF', field],
        'findings-registry predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  const expectedBlockers = [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ];
  if (!sameCanonical0(nf.activeFinalNodeIds, [])
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || !sameCanonical0(nf.remainingBlockerCoordinates, expectedBlockers)) {
    return validationReject0(
      ['FindingsRegistryPredecessor', 'NF', 'remainingBlockerCoordinates'],
      'findings-registry predecessor must expose only unrestricted-soundness and external-review blockers',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
        remainingBlockerCoordinates: nf.remainingBlockerCoordinates,
      },
    );
  }
  return validationAccept0({
    kind: 'SignedExternalReviewFindingsPredecessorBoundary0NF',
    ...expected,
    remainingBlockerCoordinates: expectedBlockers,
  });
}

function validateSignedFindingsBundle0(bundle) {
  if (!sameCanonical0(bundle, SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0)) {
    return validationReject0(
      ['SignedFindingsBundle'],
      'signed external-review findings checker requires the exact pending empty signed-findings bundle',
      { expected: SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0, actual: bundle },
    );
  }
  return validationAccept0({
    kind: 'SignedExternalReviewFindingsBundle0NF',
    coordinate: bundle.coordinate,
    signedFindingCount: bundle.signedFindingCount,
    signedFindingsBundleDigest: digestCanonical0(bundle),
  });
}

function validateGateSuite0(suite, signedFindingsBundle) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SignedFindingsGate'],
      'signed external-review findings gate suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makeSignedExternalReviewFindingsSuite0({
    SignedFindingsBundle: signedFindingsBundle,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SignedFindingsGate'],
      'signed external-review findings gate suite must exactly match the computed bundle and policy binding',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'SignedExternalReviewFindingsSuite0NF',
    suiteId: suite.suiteId,
    bindingDigest: suite.binding.bindingDigest,
  });
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: `${name} did not return a total accept/reject record`,
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: `${name} threw instead of returning a reject record`,
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    };
  }
}

function compactRecord0(record) {
  return {
    tag: record?.tag ?? null,
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: record?.Digest ?? record?.digest ?? null,
  };
}

function makeLedgerEntry0(phase, ok, material) {
  return {
    phase,
    status: ok ? 'pass' : 'fail',
    digest: digestCanonical0(material ?? null),
  };
}

function makeAcceptRecord0({ checker, nf, ledger }) {
  const digest = digestCanonical0(nf);
  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectFromValidation0(checker, coord, result, ledger) {
  return makeRejectRecord0({
    checker,
    coord,
    path: result.path,
    witness: result.witness,
    ledger,
  });
}

function makeRejectRecord0({ checker, coord, path, witness, ledger }) {
  const nf = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };
  const digest = digestCanonical0(nf);
  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: path,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path,
    witness,
    digest,
    ledger,
  };
}

function validationAccept0(nf) {
  return { ok: true, nf };
}

function validationReject0(path, reason, details = {}) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      ...(details ?? {}),
    },
  };
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
