import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  makeGlobalRowSemanticSuite0,
} from './pcc-global-row-semantic0.mjs';

import {
  makeSyntheticLocalPackages0,
} from './pcc-local-packages0.mjs';

import {
  makeGlobalPackageSemanticSuite0,
} from './pcc-global-package-semantic0.mjs';

import {
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticSuite0,
} from './pcc-global-final-prefix-semantic0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from './pcc-global-final-sat-reduction-semantic0.mjs';

import {
  makeGlobalFinalComplexitySemanticSuite0,
} from './pcc-global-final-complexity-semantic0.mjs';

import {
  CheckPublicationCoordinateGate0,
  PUBLICATION_COORDINATE_REMAINING_BLOCKERS0,
  PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
  makePublicationCoordinateGateInput0,
  makePublicationCoordinateGateSuite0,
} from './pcc-publication-coordinate-gate0.mjs';

const CHECKER_VERSION = 0;

export const UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0 =
  'Release.UnrestrictedFinalSoundness';

export const EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0 =
  'ExternalReview.Acceptance';

export const UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0 = Object.freeze([
  'Review.CheckerSoundness.TotalAcceptRejectRecords',
  'Review.CheckerSoundness.SemanticRuleFamilies',
  'Review.CheckerSoundness.GeneratedPackageSufficiency',
  'Review.CheckerSoundness.SATReductionFamilySoundness',
  'Review.CheckerSoundness.ComplexityClassImplication',
  'Review.MathematicalSoundness.FiniteCertificateToUnboundedFamily',
  'Review.MathematicalSoundness.NoHiddenOracleOrMinimization',
  'Review.Reproducibility.IndependentCleanReplay',
]);

export const UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_PACKET0 = Object.freeze({
  kind: 'UnrestrictedFinalSoundnessReviewPacket0',
  version: CHECKER_VERSION,
  coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
  predecessorGate: 'CheckPublicationCoordinateGate0',
  predecessorDocumentationCoordinate:
    PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0.coordinateId,
  boundedSemanticDAGCoverageComplete: true,
  globalFinalDerivationsReadyInBoundedSemanticDAG: true,
  publicReviewDocumentationCoordinateBound: true,
  documentationBlockerDischarged: true,
  unrestrictedFinalSoundnessReviewPacketRepresented: true,
  unrestrictedFinalSoundnessReady: false,
  unrestrictedFinalSoundnessReleased: false,
  externalReviewAcceptanceRequired: true,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  sealedReleaseNotOverwritten: true,
  sourceAndArtifactAccessPublicWithoutRequest: true,
  reviewObligations:
    [...UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0],
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
});

export const UNRESTRICTED_FINAL_SOUNDNESS_GATE_POLICY0 = Object.freeze({
  kind: 'UnrestrictedFinalSoundnessGatePolicy0',
  version: CHECKER_VERSION,
  requiresPublicationCoordinateGateAcceptance: true,
  requiresDocumentationBlockerAlreadyDischarged: true,
  requiresExactReviewPacket: true,
  requiresReviewPacketToRemainNonActivating: true,
  requiresActiveFinalNodeSetEmpty: true,
  representsReviewPacketOnly: true,
  dischargesUnrestrictedFinalSoundness: false,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  leavesExternalReviewAcceptanceBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const UNRESTRICTED_FINAL_SOUNDNESS_GATE_CONTRACT0 = Object.freeze({
  kind: 'UnrestrictedFinalSoundnessGateContract0',
  version: CHECKER_VERSION,
  coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
  predecessorChecker: 'CheckPublicationCoordinateGate0',
  reviewPacketKind: UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_PACKET0.kind,
  reviewObligations: [...UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0],
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
  publicTheoremEmissionAllowed: false,
});

export function makeUnrestrictedFinalSoundnessGateSuite0({
  ReviewPacket = UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_PACKET0,
} = {}) {
  const base = Object.freeze({
    kind: 'UnrestrictedFinalSoundnessGateBinding0',
    version: CHECKER_VERSION,
    coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    reviewPacketDigest: digestCanonical0(ReviewPacket),
    checkerContractDigest:
      digestCanonical0(UNRESTRICTED_FINAL_SOUNDNESS_GATE_CONTRACT0),
    policyDigest: digestCanonical0(UNRESTRICTED_FINAL_SOUNDNESS_GATE_POLICY0),
  });
  return Object.freeze({
    kind: 'UnrestrictedFinalSoundnessGateSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.unrestricted-final-soundness.gate.phase43',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...UNRESTRICTED_FINAL_SOUNDNESS_GATE_POLICY0 },
  });
}

export function makeUnrestrictedFinalSoundnessGateInput0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  RowSemanticDerivations = makeGlobalRowSemanticSuite0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
  }),
  LocalPackages = makeSyntheticLocalPackages0(),
  PackageSemanticDerivations = makeGlobalPackageSemanticSuite0({
    LegacyGlobalProofDAG,
    LocalPackages,
  }),
  PCCPack = makeGlobalFinalPrefixPCCPack0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
    LocalPackages,
  }),
  FinalPrefixSemanticDerivations = makeGlobalFinalPrefixSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  SATReductionSemanticDerivations = makeGlobalFinalSATReductionSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  ComplexitySemanticDerivations = makeGlobalFinalComplexitySemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  PublicationDocumentationCoordinate = PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
  PublicationCoordinateGate = makePublicationCoordinateGateSuite0({
    PublicationDocumentationCoordinate,
  }),
  ReviewPacket = UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_PACKET0,
  UnrestrictedFinalSoundnessGate = makeUnrestrictedFinalSoundnessGateSuite0({
    ReviewPacket,
  }),
} = {}) {
  return Object.freeze({
    kind: 'UnrestrictedFinalSoundnessGateInput0',
    version: CHECKER_VERSION,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    RowSemanticDerivations,
    LocalPackages,
    PackageSemanticDerivations,
    PCCPack,
    FinalPrefixSemanticDerivations,
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
    PublicationDocumentationCoordinate,
    PublicationCoordinateGate,
    ReviewPacket,
    UnrestrictedFinalSoundnessGate,
    Policy: { ...UNRESTRICTED_FINAL_SOUNDNESS_GATE_POLICY0 },
  });
}

export async function CheckUnrestrictedFinalSoundnessGate0(input) {
  const checker = 'CheckUnrestrictedFinalSoundnessGate0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckPublicationCoordinateGate0',
    () => CheckPublicationCoordinateGate0(
      makePublicationCoordinateGateInput0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        LocalPackages: input.LocalPackages,
        PackageSemanticDerivations: input.PackageSemanticDerivations,
        PCCPack: input.PCCPack,
        FinalPrefixSemanticDerivations:
          input.FinalPrefixSemanticDerivations,
        SATReductionSemanticDerivations:
          input.SATReductionSemanticDerivations,
        ComplexitySemanticDerivations:
          input.ComplexitySemanticDerivations,
        PublicationDocumentationCoordinate:
          input.PublicationDocumentationCoordinate,
        PublicationCoordinateGate: input.PublicationCoordinateGate,
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckPublicationCoordinateGate0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.publicationCoordinatePredecessor.exception`,
      path: ['PublicationCoordinateGate'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.publicationCoordinatePredecessor`,
      path: ['PublicationCoordinateGate'],
      witness: {
        reason: 'unrestricted final-soundness gate requires an accepted publication-coordinate predecessor',
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
    'publicationCoordinatePredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.publicationCoordinatePredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const packet = validateReviewPacket0(input.ReviewPacket);
  ledger.push(makeLedgerEntry0(
    'reviewPacket',
    packet.ok,
    packet.nf ?? packet.witness,
  ));
  if (!packet.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.reviewPacket`,
      packet,
      ledger,
    );
  }

  const suite = validateGateSuite0(input.UnrestrictedFinalSoundnessGate, input.ReviewPacket);
  ledger.push(makeLedgerEntry0(
    'unrestrictedFinalSoundnessGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.unrestrictedFinalSoundnessGateSuite`,
      suite,
      ledger,
    );
  }

  const remainingBlockers = [
    Object.freeze({
      coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
      ready: false,
      reason: 'unrestricted final soundness has a represented review packet, but no independent unrestricted-soundness release is supplied',
      reviewPacketDigest: digestCanonical0(input.ReviewPacket),
      digest: digestCanonical0({
        coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
        reviewPacketDigest: digestCanonical0(input.ReviewPacket),
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
    Object.freeze({
      coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
      ready: false,
      reason: 'external review acceptance is not represented by this unrestricted-soundness review-packet gate',
      digest: digestCanonical0({
        coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
  ];

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'UnrestrictedFinalSoundnessGate0NF',
      checker,
      version: CHECKER_VERSION,
      unrestrictedFinalSoundnessGateRepresentedReady: true,
      unrestrictedFinalSoundnessReviewPacketReady: true,
      unrestrictedFinalSoundnessReady: false,
      unrestrictedFinalSoundnessReleased: false,
      unrestrictedFinalSoundnessBlocked: true,
      externalReviewAcceptanceReady: false,

      publicationCoordinatePredecessorAccepted: true,
      publicationCoordinatePredecessorChecker: predecessorCall.record.checker,
      publicationCoordinatePredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      documentationImmutablePublicRevisionReady: true,
      publicationDocumentationCoordinateReady: true,
      priorRemainingBlockerCoordinates:
        [...PUBLICATION_COORDINATE_REMAINING_BLOCKERS0],

      reviewPacket: input.ReviewPacket,
      reviewPacketDigest: digestCanonical0(input.ReviewPacket),
      reviewObligationCoordinates:
        [...UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0],
      reviewObligationCount:
        UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0.length,
      independentMathematicalReviewStillRequired: true,
      independentCheckerSoundnessReviewStillRequired: true,
      externalReviewAcceptanceRequired: true,

      gateBinding: input.UnrestrictedFinalSoundnessGate.binding,
      gateBindingDigest:
        input.UnrestrictedFinalSoundnessGate.binding.bindingDigest,
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
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'unrestricted final-soundness gate input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'UnrestrictedFinalSoundnessGateInput0') {
    return validationReject0(
      ['kind'],
      'unrestricted final-soundness gate input kind must be UnrestrictedFinalSoundnessGateInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `unrestricted final-soundness gate input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  const required = [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowPack',
    'RowFamG',
    'RowSemanticDerivations',
    'LocalPackages',
    'PackageSemanticDerivations',
    'PCCPack',
    'FinalPrefixSemanticDerivations',
    'SATReductionSemanticDerivations',
    'ComplexitySemanticDerivations',
    'PublicationDocumentationCoordinate',
    'PublicationCoordinateGate',
    'ReviewPacket',
    'UnrestrictedFinalSoundnessGate',
    'Policy',
  ];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'unrestricted final-soundness gate input is missing a required field',
        { field },
      );
    }
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'unrestricted final-soundness gate dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'unrestricted final-soundness gate input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Policy, UNRESTRICTED_FINAL_SOUNDNESS_GATE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'unrestricted final-soundness gate policy must match the fail-closed policy',
      { expected: UNRESTRICTED_FINAL_SOUNDNESS_GATE_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'unrestricted final-soundness gate rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'UnrestrictedFinalSoundnessGateInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    publicationCoordinateGateReady: true,
    publicationCoordinateGateRepresentedReady: true,
    documentationImmutablePublicRevisionReady: true,
    documentationImmutablePublicRevisionBlocked: false,
    unrestrictedFinalSoundnessReady: false,
    externalReviewAcceptanceReady: false,
    globalSemanticNodeDerivationsReady: true,
    globalFinalDerivationsReady: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    releasePublicTheoremEmissionBlocked: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PublicationCoordinatePredecessor', 'NF', field],
        'publication-coordinate predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.activeFinalNodeIds, [])
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || !sameCanonical0(nf.remainingBlockerCoordinates, PUBLICATION_COORDINATE_REMAINING_BLOCKERS0)) {
    return validationReject0(
      ['PublicationCoordinatePredecessor', 'NF', 'remainingBlockerCoordinates'],
      'publication-coordinate predecessor must expose only unrestricted-soundness and external-review blockers',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
        remainingBlockerCoordinates: nf.remainingBlockerCoordinates,
      },
    );
  }
  return validationAccept0({
    kind: 'UnrestrictedFinalSoundnessPredecessorBoundary0NF',
    ...expected,
    remainingBlockerCoordinates: [...PUBLICATION_COORDINATE_REMAINING_BLOCKERS0],
  });
}

function validateReviewPacket0(packet) {
  if (!sameCanonical0(packet, UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_PACKET0)) {
    return validationReject0(
      ['ReviewPacket'],
      'unrestricted final-soundness gate requires the exact review packet',
      { expected: UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_PACKET0, actual: packet },
    );
  }
  return validationAccept0({
    kind: 'UnrestrictedFinalSoundnessReviewPacket0NF',
    coordinate: packet.coordinate,
    reviewObligationCount: packet.reviewObligations.length,
    reviewPacketDigest: digestCanonical0(packet),
  });
}

function validateGateSuite0(suite, reviewPacket) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['UnrestrictedFinalSoundnessGate'],
      'unrestricted final-soundness gate suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makeUnrestrictedFinalSoundnessGateSuite0({
    ReviewPacket: reviewPacket,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['UnrestrictedFinalSoundnessGate'],
      'unrestricted final-soundness gate suite must exactly match the computed review-packet and policy binding',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'UnrestrictedFinalSoundnessGateSuite0NF',
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
