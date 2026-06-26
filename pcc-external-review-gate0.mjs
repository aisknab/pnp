import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckUnrestrictedFinalSoundnessGate0,
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0,
  makeUnrestrictedFinalSoundnessGateInput0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

import {
  PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
} from './pcc-publication-coordinate-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0 = Object.freeze([
  'ExternalReview.Scope.StatementAndClaimBoundary',
  'ExternalReview.Reproduce.PublicReviewDocumentationCoordinate',
  'ExternalReview.Reproduce.SealedSourceAndArtifactRelease',
  'ExternalReview.CheckerSoundness.SemanticKernelStack',
  'ExternalReview.CheckerSoundness.ReleaseGateStack',
  'ExternalReview.MathematicalSoundness.UnrestrictedFinalSoundness',
  'ExternalReview.Report.AcceptRejectWithSignedFindings',
]);

export const EXTERNAL_REVIEW_REQUEST_PACKET0 = Object.freeze({
  kind: 'ExternalReviewRequestPacket0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  predecessorCoordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
  predecessorChecker: 'CheckUnrestrictedFinalSoundnessGate0',
  predecessorReviewPacketRepresented: true,
  documentationCoordinate:
    PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0.coordinateId,
  publicRepository: 'https://github.com/aisknab/pnp',
  reviewerGuidePath: 'docs/reviewer_guide.md',
  reproducibilityGuidePath: 'docs/reproducibility.md',
  sealedSourceTag: 'final-pnp-proof-report-hardened-7072f8d',
  sealedSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
  sealedArtifactTag:
    'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
  sealedReleaseNotOverwritten: true,
  sourceAndArtifactAccessPublicWithoutRequest: true,
  externalReviewRequestRepresented: true,
  externalReviewAcceptanceReady: false,
  externalReviewAcceptanceReleased: false,
  externalReviewAcceptanceNotClaimed: true,
  unrestrictedFinalSoundnessReady: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  reviewRequestChannels: Object.freeze([
    'public-github-review',
    'review@pnplabs.com.au',
    'security@pnplabs.com.au',
  ]),
  reviewRequestObligations: [...EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0],
  inheritedUnrestrictedSoundnessObligations:
    [...UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0],
});

export const EXTERNAL_REVIEW_GATE_POLICY0 = Object.freeze({
  kind: 'ExternalReviewGatePolicy0',
  version: CHECKER_VERSION,
  requiresUnrestrictedFinalSoundnessGateAcceptance: true,
  requiresUnrestrictedFinalSoundnessStillBlocked: true,
  requiresExternalReviewAcceptanceStillBlocked: true,
  requiresExactExternalReviewRequestPacket: true,
  requiresReviewRequestToRemainNonActivating: true,
  requiresActiveFinalNodeSetEmpty: true,
  representsExternalReviewRequestOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const EXTERNAL_REVIEW_GATE_CONTRACT0 = Object.freeze({
  kind: 'ExternalReviewGateContract0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  predecessorChecker: 'CheckUnrestrictedFinalSoundnessGate0',
  reviewRequestPacketKind: EXTERNAL_REVIEW_REQUEST_PACKET0.kind,
  reviewRequestObligations: [...EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0],
  inheritedUnrestrictedSoundnessObligations:
    [...UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0],
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
  publicTheoremEmissionAllowed: false,
});

export function makeExternalReviewGateSuite0({
  ReviewRequestPacket = EXTERNAL_REVIEW_REQUEST_PACKET0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewGateBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
    reviewRequestPacketDigest: digestCanonical0(ReviewRequestPacket),
    checkerContractDigest: digestCanonical0(EXTERNAL_REVIEW_GATE_CONTRACT0),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_GATE_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewGateSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.gate.phase44',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_GATE_POLICY0 },
  });
}

export function makeExternalReviewGateInput0({
  PredecessorInput = makeUnrestrictedFinalSoundnessGateInput0(),
  ReviewRequestPacket = EXTERNAL_REVIEW_REQUEST_PACKET0,
  ExternalReviewGate = makeExternalReviewGateSuite0({
    ReviewRequestPacket,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewGateInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    ReviewRequestPacket,
    ExternalReviewGate,
    Policy: { ...EXTERNAL_REVIEW_GATE_POLICY0 },
  });
}

export async function CheckExternalReviewGate0(input) {
  const checker = 'CheckExternalReviewGate0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckUnrestrictedFinalSoundnessGate0',
    () => CheckUnrestrictedFinalSoundnessGate0(input.PredecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckUnrestrictedFinalSoundnessGate0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.unrestrictedFinalSoundnessPredecessor.exception`,
      path: ['PredecessorInput'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.unrestrictedFinalSoundnessPredecessor`,
      path: ['PredecessorInput'],
      witness: {
        reason: 'external-review gate requires an accepted unrestricted final-soundness predecessor',
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
    'unrestrictedFinalSoundnessPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.unrestrictedFinalSoundnessPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const requestPacket = validateReviewRequestPacket0(input.ReviewRequestPacket);
  ledger.push(makeLedgerEntry0(
    'externalReviewRequestPacket',
    requestPacket.ok,
    requestPacket.nf ?? requestPacket.witness,
  ));
  if (!requestPacket.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.externalReviewRequestPacket`,
      requestPacket,
      ledger,
    );
  }

  const suite = validateGateSuite0(input.ExternalReviewGate, input.ReviewRequestPacket);
  ledger.push(makeLedgerEntry0(
    'externalReviewGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.externalReviewGateSuite`,
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
      reason: 'external review request is represented, but external acceptance is not supplied',
      reviewRequestPacketDigest: digestCanonical0(input.ReviewRequestPacket),
      digest: digestCanonical0({
        coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
        reviewRequestPacketDigest: digestCanonical0(input.ReviewRequestPacket),
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
  ];

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'ExternalReviewGate0NF',
      checker,
      version: CHECKER_VERSION,
      externalReviewGateRepresentedReady: true,
      externalReviewRequestPacketReady: true,
      externalReviewRequestRepresentedReady: true,
      externalReviewAcceptanceReady: false,
      externalReviewAcceptanceReleased: false,
      externalReviewAcceptanceBlocked: true,
      unrestrictedFinalSoundnessReady: false,
      unrestrictedFinalSoundnessBlocked: true,

      unrestrictedFinalSoundnessPredecessorAccepted: true,
      unrestrictedFinalSoundnessPredecessorChecker:
        predecessorCall.record.checker,
      unrestrictedFinalSoundnessPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      predecessorRemainingBlockerCoordinates:
        predecessorNF.remainingBlockerCoordinates ?? [],

      reviewRequestPacket: input.ReviewRequestPacket,
      reviewRequestPacketDigest: digestCanonical0(input.ReviewRequestPacket),
      reviewRequestObligationCoordinates:
        [...EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0],
      reviewRequestObligationCount:
        EXTERNAL_REVIEW_REQUEST_OBLIGATIONS0.length,
      inheritedUnrestrictedSoundnessObligationCount:
        UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0.length,
      reviewRequestChannels:
        [...input.ReviewRequestPacket.reviewRequestChannels],

      gateBinding: input.ExternalReviewGate.binding,
      gateBindingDigest: input.ExternalReviewGate.binding.bindingDigest,
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
    return validationReject0([], 'external-review gate input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'ExternalReviewGateInput0') {
    return validationReject0(
      ['kind'],
      'external-review gate input kind must be ExternalReviewGateInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `external-review gate input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  const required = [
    'PredecessorInput',
    'ReviewRequestPacket',
    'ExternalReviewGate',
    'Policy',
  ];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'external-review gate input is missing a required field',
        { field },
      );
    }
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'external-review gate dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_GATE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'external-review gate policy must match the fail-closed policy',
      { expected: EXTERNAL_REVIEW_GATE_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'external-review gate rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'ExternalReviewGateInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    unrestrictedFinalSoundnessGateRepresentedReady: true,
    unrestrictedFinalSoundnessReviewPacketReady: true,
    unrestrictedFinalSoundnessReady: false,
    unrestrictedFinalSoundnessReleased: false,
    unrestrictedFinalSoundnessBlocked: true,
    externalReviewAcceptanceReady: false,
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
        ['UnrestrictedFinalSoundnessPredecessor', 'NF', field],
        'unrestricted final-soundness predecessor boundary mismatch',
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
      ['UnrestrictedFinalSoundnessPredecessor', 'NF', 'remainingBlockerCoordinates'],
      'unrestricted final-soundness predecessor must expose only unrestricted-soundness and external-review blockers',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
        remainingBlockerCoordinates: nf.remainingBlockerCoordinates,
      },
    );
  }
  return validationAccept0({
    kind: 'ExternalReviewPredecessorBoundary0NF',
    ...expected,
    remainingBlockerCoordinates: expectedBlockers,
  });
}

function validateReviewRequestPacket0(packet) {
  if (!sameCanonical0(packet, EXTERNAL_REVIEW_REQUEST_PACKET0)) {
    return validationReject0(
      ['ReviewRequestPacket'],
      'external-review gate requires the exact external-review request packet',
      { expected: EXTERNAL_REVIEW_REQUEST_PACKET0, actual: packet },
    );
  }
  return validationAccept0({
    kind: 'ExternalReviewRequestPacket0NF',
    coordinate: packet.coordinate,
    reviewRequestObligationCount: packet.reviewRequestObligations.length,
    reviewRequestPacketDigest: digestCanonical0(packet),
  });
}

function validateGateSuite0(suite, reviewRequestPacket) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['ExternalReviewGate'],
      'external-review gate suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makeExternalReviewGateSuite0({
    ReviewRequestPacket: reviewRequestPacket,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['ExternalReviewGate'],
      'external-review gate suite must exactly match the computed request-packet and policy binding',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'ExternalReviewGateSuite0NF',
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
