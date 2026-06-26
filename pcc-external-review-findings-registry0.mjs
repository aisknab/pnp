import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewGate0,
  EXTERNAL_REVIEW_REQUEST_PACKET0,
  makeExternalReviewGateInput0,
} from './pcc-external-review-gate0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

import {
  PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
} from './pcc-publication-coordinate-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0 =
  'ExternalReview.FindingsRegistry';

export const EXTERNAL_REVIEW_FINDING_KINDS0 = Object.freeze([
  'ExternalReviewAcceptanceFinding0',
  'ExternalReviewRejectionFinding0',
  'ExternalReviewRevisionRequestFinding0',
]);

export const EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0 = Object.freeze([
  'kind',
  'version',
  'reviewerIdentityDigest',
  'reviewScopeDigest',
  'documentationCoordinate',
  'sealedSourceCommit',
  'sealedArtifactTag',
  'finding',
  'findingDigest',
  'signatureDigest',
]);

export const EXTERNAL_REVIEW_FINDINGS_REGISTRY0 = Object.freeze({
  kind: 'ExternalReviewFindingsRegistry0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewGate0',
  predecessorRequestPacketRepresented: true,
  documentationCoordinate:
    PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0.coordinateId,
  externalReviewRequestPacketDigest:
    digestCanonical0(EXTERNAL_REVIEW_REQUEST_PACKET0),
  sealedSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
  sealedArtifactTag:
    'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
  sealedReleaseNotOverwritten: true,
  sourceAndArtifactAccessPublicWithoutRequest: true,
  registryStatus: 'pending-signed-findings',
  signedFindingCount: 0,
  acceptanceFindingCount: 0,
  rejectionFindingCount: 0,
  revisionRequestFindingCount: 0,
  signedFindings: Object.freeze([]),
  acceptedFindingKinds: [...EXTERNAL_REVIEW_FINDING_KINDS0],
  requiredFindingFields: [...EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0],
  externalReviewFindingsRegistryRepresented: true,
  externalReviewSignedFindingsReady: false,
  externalReviewAcceptanceReady: false,
  externalReviewAcceptanceReleased: false,
  externalReviewAcceptanceNotClaimed: true,
  unrestrictedFinalSoundnessReady: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
});

export const EXTERNAL_REVIEW_FINDINGS_REGISTRY_POLICY0 = Object.freeze({
  kind: 'ExternalReviewFindingsRegistryPolicy0',
  version: CHECKER_VERSION,
  requiresExternalReviewGateAcceptance: true,
  requiresExternalReviewAcceptanceStillBlocked: true,
  requiresExactPendingFindingsRegistry: true,
  requiresNoUnsignedAcceptance: true,
  requiresNoCallerSuppliedFindingsAcceptance: true,
  representsFindingsRegistryOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const EXTERNAL_REVIEW_FINDINGS_REGISTRY_CONTRACT0 = Object.freeze({
  kind: 'ExternalReviewFindingsRegistryContract0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewGate0',
  registryKind: EXTERNAL_REVIEW_FINDINGS_REGISTRY0.kind,
  allowedFindingKinds: [...EXTERNAL_REVIEW_FINDING_KINDS0],
  requiredFindingFields: [...EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0],
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
  publicTheoremEmissionAllowed: false,
});

export function makeExternalReviewFindingsRegistrySuite0({
  FindingsRegistry = EXTERNAL_REVIEW_FINDINGS_REGISTRY0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewFindingsRegistryBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_FINDINGS_REGISTRY_COORDINATE0,
    findingsRegistryDigest: digestCanonical0(FindingsRegistry),
    checkerContractDigest:
      digestCanonical0(EXTERNAL_REVIEW_FINDINGS_REGISTRY_CONTRACT0),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_FINDINGS_REGISTRY_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewFindingsRegistrySuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.findings-registry.phase45',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_FINDINGS_REGISTRY_POLICY0 },
  });
}

export function makeExternalReviewFindingsRegistryInput0({
  PredecessorInput = makeExternalReviewGateInput0(),
  FindingsRegistry = EXTERNAL_REVIEW_FINDINGS_REGISTRY0,
  FindingsRegistryGate = makeExternalReviewFindingsRegistrySuite0({
    FindingsRegistry,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewFindingsRegistryInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    FindingsRegistry,
    FindingsRegistryGate,
    Policy: { ...EXTERNAL_REVIEW_FINDINGS_REGISTRY_POLICY0 },
  });
}

export async function CheckExternalReviewFindingsRegistry0(input) {
  const checker = 'CheckExternalReviewFindingsRegistry0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckExternalReviewGate0',
    () => CheckExternalReviewGate0(input.PredecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckExternalReviewGate0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.externalReviewPredecessor.exception`,
      path: ['PredecessorInput'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.externalReviewPredecessor`,
      path: ['PredecessorInput'],
      witness: {
        reason: 'external-review findings registry requires an accepted external-review request predecessor',
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
    'externalReviewPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.externalReviewPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const registry = validateFindingsRegistry0(input.FindingsRegistry);
  ledger.push(makeLedgerEntry0(
    'findingsRegistry',
    registry.ok,
    registry.nf ?? registry.witness,
  ));
  if (!registry.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.findingsRegistry`,
      registry,
      ledger,
    );
  }

  const suite = validateGateSuite0(
    input.FindingsRegistryGate,
    input.FindingsRegistry,
  );
  ledger.push(makeLedgerEntry0(
    'findingsRegistryGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.findingsRegistryGateSuite`,
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
      reason: 'external review findings registry is pending signed findings; no acceptance artifact is supplied',
      findingsRegistryDigest: digestCanonical0(input.FindingsRegistry),
      digest: digestCanonical0({
        coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
        findingsRegistryDigest: digestCanonical0(input.FindingsRegistry),
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
  ];

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'ExternalReviewFindingsRegistry0NF',
      checker,
      version: CHECKER_VERSION,
      externalReviewFindingsRegistryRepresentedReady: true,
      externalReviewFindingsRegistryReady: true,
      externalReviewSignedFindingsReady: false,
      externalReviewAcceptanceReady: false,
      externalReviewAcceptanceReleased: false,
      externalReviewAcceptanceBlocked: true,
      unrestrictedFinalSoundnessReady: false,
      unrestrictedFinalSoundnessBlocked: true,

      externalReviewPredecessorAccepted: true,
      externalReviewPredecessorChecker: predecessorCall.record.checker,
      externalReviewPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      predecessorRemainingBlockerCoordinates:
        predecessorNF.remainingBlockerCoordinates ?? [],

      findingsRegistry: input.FindingsRegistry,
      findingsRegistryDigest: digestCanonical0(input.FindingsRegistry),
      signedFindingCount: input.FindingsRegistry.signedFindingCount,
      acceptanceFindingCount: input.FindingsRegistry.acceptanceFindingCount,
      rejectionFindingCount: input.FindingsRegistry.rejectionFindingCount,
      revisionRequestFindingCount:
        input.FindingsRegistry.revisionRequestFindingCount,
      acceptedFindingKinds: [...EXTERNAL_REVIEW_FINDING_KINDS0],
      requiredFindingFields: [...EXTERNAL_REVIEW_FINDING_REQUIRED_FIELDS0],

      gateBinding: input.FindingsRegistryGate.binding,
      gateBindingDigest: input.FindingsRegistryGate.binding.bindingDigest,
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
      sourceAndArtifactAccessPublicWithoutRequest: true,
      externalReviewAcceptanceNotClaimed: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'external-review findings registry input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'ExternalReviewFindingsRegistryInput0') {
    return validationReject0(
      ['kind'],
      'external-review findings registry input kind must be ExternalReviewFindingsRegistryInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `external-review findings registry input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  const required = [
    'PredecessorInput',
    'FindingsRegistry',
    'FindingsRegistryGate',
    'Policy',
  ];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'external-review findings registry input is missing a required field',
        { field },
      );
    }
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'external-review findings registry dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_FINDINGS_REGISTRY_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'external-review findings registry policy must match the fail-closed policy',
      { expected: EXTERNAL_REVIEW_FINDINGS_REGISTRY_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'external-review findings registry rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'ExternalReviewFindingsRegistryInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    externalReviewGateRepresentedReady: true,
    externalReviewRequestPacketReady: true,
    externalReviewRequestRepresentedReady: true,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceReleased: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    unrestrictedFinalSoundnessBlocked: true,
    globalSemanticNodeDerivationsReady: true,
    globalFinalDerivationsReady: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    releasePublicTheoremEmissionBlocked: true,
    sealedReleaseNotOverwritten: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['ExternalReviewPredecessor', 'NF', field],
        'external-review predecessor boundary mismatch',
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
      ['ExternalReviewPredecessor', 'NF', 'remainingBlockerCoordinates'],
      'external-review predecessor must expose only unrestricted-soundness and external-review blockers',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
        remainingBlockerCoordinates: nf.remainingBlockerCoordinates,
      },
    );
  }
  return validationAccept0({
    kind: 'ExternalReviewFindingsRegistryPredecessorBoundary0NF',
    ...expected,
    remainingBlockerCoordinates: expectedBlockers,
  });
}

function validateFindingsRegistry0(registry) {
  if (!sameCanonical0(registry, EXTERNAL_REVIEW_FINDINGS_REGISTRY0)) {
    return validationReject0(
      ['FindingsRegistry'],
      'external-review findings registry requires the exact pending registry with no signed findings',
      { expected: EXTERNAL_REVIEW_FINDINGS_REGISTRY0, actual: registry },
    );
  }
  return validationAccept0({
    kind: 'ExternalReviewFindingsRegistry0NF',
    coordinate: registry.coordinate,
    signedFindingCount: registry.signedFindingCount,
    findingsRegistryDigest: digestCanonical0(registry),
  });
}

function validateGateSuite0(suite, findingsRegistry) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['FindingsRegistryGate'],
      'external-review findings registry gate suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makeExternalReviewFindingsRegistrySuite0({
    FindingsRegistry: findingsRegistry,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['FindingsRegistryGate'],
      'external-review findings registry gate suite must exactly match the computed registry and policy binding',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'ExternalReviewFindingsRegistryGateSuite0NF',
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
