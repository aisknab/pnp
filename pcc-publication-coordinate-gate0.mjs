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
  CheckGlobalProofDAGPublicEmissionSuccessor0,
  makeGlobalProofDAGPublicEmissionSuccessor0,
} from './pcc-global-proof-dag-public-emission-successor0.mjs';

import {
  PUBLIC_EMISSION_BLOCKERS0,
  PUBLIC_THEOREM_EMISSION_COORDINATE0,
} from './pcc-public-emission-gate0.mjs';

const CHECKER_VERSION = 0;

export const PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0 = Object.freeze({
  kind: 'ImmutablePublicReviewDocumentationCoordinate0',
  version: CHECKER_VERSION,
  coordinateId: 'PNP-DOC-CPR-2026-06-26-01',
  revisionDate: '2026-06-26',
  repositoryPath:
    'documentation-revisions/PNP-DOC-CPR-2026-06-26-01/',
  baseDocumentationCommit: 'f52e04b9963ea2f10cfccafbf705b9e316ed25a6',
  previousDocumentationCoordinate: 'PNP-DOC-CPR-2026-06-20-01',
  sealedSourceTag: 'final-pnp-proof-report-hardened-7072f8d',
  sealedSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
  sealedArtifactTag:
    'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
  sealedReleaseNotOverwritten: true,
  documentationOnlyRevision: true,
  publicReviewPublicationFraming: true,
  directTheoremEmissionReframedAsReviewStatus: true,
  publicTheoremEmissionNotActivated: true,
  independentMathematicalReviewStillRequired: true,
  independentCheckerSoundnessReviewStillRequired: true,
  sourceAndArtifactAccessPublicWithoutRequest: true,
  publicRepository: 'https://github.com/aisknab/pnp',
  reviewerGuidePath: 'docs/reviewer_guide.md',
  reproducibilityGuidePath: 'docs/reproducibility.md',
  texPayloadSha256:
    '9ad7ed91a48662b98432e2b6000beaf06b3ebd2212de3a6d820a7dcbd27e8d9a',
  pdfPayloadSha256:
    'f6848d37eb8982f59ca1436352e06559e35aad8ee56956705de2650de1cc45a7',
  texPatchSha256:
    'effbcf2e20436535248b39e59170538422abd4348de7b8dbf43035118609367a',
  texPatchPath:
    'documentation-revisions/PNP-DOC-CPR-2026-06-26-01/canonical_proof_report.tex.patch',
  sha256SumsPath:
    'documentation-revisions/PNP-DOC-CPR-2026-06-26-01/SHA256SUMS',
  patchSha256SumsPath:
    'documentation-revisions/PNP-DOC-CPR-2026-06-26-01/PATCH_SHA256SUMS',
});

export const PUBLICATION_COORDINATE_DISCHARGED_BLOCKERS0 = Object.freeze([
  'Documentation.ImmutablePublicRevision',
]);

export const PUBLICATION_COORDINATE_REMAINING_BLOCKERS0 = Object.freeze([
  'Release.UnrestrictedFinalSoundness',
  'ExternalReview.Acceptance',
]);

export const PUBLICATION_COORDINATE_GATE_POLICY0 = Object.freeze({
  kind: 'PublicationCoordinateGatePolicy0',
  version: CHECKER_VERSION,
  requiresPriorPublicEmissionGateAcceptance: true,
  requiresPriorDocumentationBlockerPresent: true,
  requiresNewPublicReviewDocumentationCoordinate: true,
  requiresSealedReleaseNotOverwritten: true,
  requiresSourceAndArtifactAccessPublicWithoutRequest: true,
  dischargesOnlyDocumentationImmutablePublicRevision: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  leavesExternalReviewAcceptanceBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const PUBLICATION_COORDINATE_GATE_CONTRACT0 = Object.freeze({
  kind: 'PublicationCoordinateGateContract0',
  version: CHECKER_VERSION,
  coordinate: 'Release.PublicationCoordinateGate',
  predecessorChecker: 'CheckGlobalProofDAGPublicEmissionSuccessor0',
  publicEmissionCoordinate: PUBLIC_THEOREM_EMISSION_COORDINATE0,
  documentationCoordinate:
    PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0.coordinateId,
  dischargedBlockers: PUBLICATION_COORDINATE_DISCHARGED_BLOCKERS0,
  remainingBlockers: PUBLICATION_COORDINATE_REMAINING_BLOCKERS0,
  publicTheoremEmissionAllowed: false,
});

export function makePublicationCoordinateGateSuite0({
  PublicationDocumentationCoordinate = PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0,
} = {}) {
  const base = Object.freeze({
    kind: 'PublicationCoordinateGateBinding0',
    version: CHECKER_VERSION,
    coordinate: 'Release.PublicationCoordinateGate',
    documentationCoordinateId:
      PublicationDocumentationCoordinate.coordinateId ?? null,
    documentationCoordinateDigest:
      digestCanonical0(PublicationDocumentationCoordinate),
    checkerContractDigest:
      digestCanonical0(PUBLICATION_COORDINATE_GATE_CONTRACT0),
    policyDigest: digestCanonical0(PUBLICATION_COORDINATE_GATE_POLICY0),
  });
  return Object.freeze({
    kind: 'PublicationCoordinateGateSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.publication-coordinate.gate.phase42',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...PUBLICATION_COORDINATE_GATE_POLICY0 },
  });
}

export function makePublicationCoordinateGateInput0({
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
} = {}) {
  return Object.freeze({
    kind: 'PublicationCoordinateGateInput0',
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
    Policy: { ...PUBLICATION_COORDINATE_GATE_POLICY0 },
  });
}

export async function CheckPublicationCoordinateGate0(input) {
  const checker = 'CheckPublicationCoordinateGate0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGPublicEmissionSuccessor0',
    () => CheckGlobalProofDAGPublicEmissionSuccessor0(
      makeGlobalProofDAGPublicEmissionSuccessor0({
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
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGPublicEmissionSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.publicEmissionPredecessor.exception`,
      path: ['PublicationCoordinateGate'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.publicEmissionPredecessor`,
      path: ['PublicationCoordinateGate'],
      witness: {
        reason: 'publication coordinate gate requires an accepted public-emission predecessor',
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
    'publicEmissionPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.publicEmissionPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const docs = validatePublicationDocumentationCoordinate0(
    input.PublicationDocumentationCoordinate,
  );
  ledger.push(makeLedgerEntry0(
    'publicationDocumentationCoordinate',
    docs.ok,
    docs.nf ?? docs.witness,
  ));
  if (!docs.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.publicationDocumentationCoordinate`,
      docs,
      ledger,
    );
  }

  const suite = validateGateSuite0(
    input.PublicationCoordinateGate,
    input.PublicationDocumentationCoordinate,
  );
  ledger.push(makeLedgerEntry0(
    'publicationCoordinateGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.publicationCoordinateGateSuite`,
      suite,
      ledger,
    );
  }

  const remainingBlockers = PUBLICATION_COORDINATE_REMAINING_BLOCKERS0.map(
    (coordinate) => Object.freeze({
      coordinate,
      ready: false,
      reason: publicationCoordinateBlockerReason0(coordinate),
      digest: digestCanonical0({
        coordinate,
        documentationCoordinate:
          input.PublicationDocumentationCoordinate.coordinateId,
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
  );
  const dischargedBlockers = PUBLICATION_COORDINATE_DISCHARGED_BLOCKERS0.map(
    (coordinate) => Object.freeze({
      coordinate,
      ready: true,
      reason: null,
      digest: digestCanonical0({
        coordinate,
        documentationCoordinate:
          input.PublicationDocumentationCoordinate.coordinateId,
        documentationCoordinateDigest:
          digestCanonical0(input.PublicationDocumentationCoordinate),
      }),
    }),
  );

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'PublicationCoordinateGate0NF',
      checker,
      version: CHECKER_VERSION,
      publicationCoordinateGateReady: true,
      publicationCoordinateGateRepresentedReady: true,
      publicEmissionPredecessorAccepted: true,
      publicEmissionPredecessorChecker: predecessorCall.record.checker,
      publicEmissionPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      priorBlockerCoordinates: [...PUBLIC_EMISSION_BLOCKERS0],
      documentationImmutablePublicRevisionReady: true,
      documentationImmutablePublicRevisionBlocked: false,
      publicationDocumentationCoordinateReady: true,
      publicationDocumentationCoordinate:
        input.PublicationDocumentationCoordinate,
      publicationDocumentationCoordinateDigest:
        digestCanonical0(input.PublicationDocumentationCoordinate),
      publicationCoordinateGateBinding: input.PublicationCoordinateGate.binding,
      publicationCoordinateGateBindingDigest:
        input.PublicationCoordinateGate.binding.bindingDigest,
      dischargedBlockers,
      dischargedBlockerCoordinates:
        dischargedBlockers.map((entry) => entry.coordinate),
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
      publicReviewPublicationFraming: true,
      independentMathematicalReviewStillRequired: true,
      independentCheckerSoundnessReviewStillRequired: true,
      unrestrictedFinalSoundnessReady: false,
      externalReviewAcceptanceReady: false,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'publication coordinate gate input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'PublicationCoordinateGateInput0') {
    return validationReject0(
      ['kind'],
      'publication coordinate gate input kind must be PublicationCoordinateGateInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `publication coordinate gate input version must be ${CHECKER_VERSION}`,
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
    'Policy',
  ];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'publication coordinate gate input is missing a required field',
        { field },
      );
    }
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'publication coordinate gate dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'publication coordinate gate input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Policy, PUBLICATION_COORDINATE_GATE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'publication coordinate gate policy must match the fail-closed policy',
      { expected: PUBLICATION_COORDINATE_GATE_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'publication coordinate gate rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'PublicationCoordinateGateInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    publicEmissionGateRepresentedReady: true,
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
        ['PublicEmissionPredecessor', 'NF', field],
        'public-emission predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.activeFinalNodeIds, [])
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || !sameCanonical0(nf.releasePublicTheoremEmissionBlockers, PUBLIC_EMISSION_BLOCKERS0)
      || !nf.releasePublicTheoremEmissionBlockers.includes(
        'Documentation.ImmutablePublicRevision',
      )) {
    return validationReject0(
      ['PublicEmissionPredecessor', 'NF', 'releasePublicTheoremEmissionBlockers'],
      'public-emission predecessor must expose the documentation blocker before phase-42 discharge',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
        releasePublicTheoremEmissionBlockers:
          nf.releasePublicTheoremEmissionBlockers,
      },
    );
  }
  return validationAccept0({
    kind: 'PublicationCoordinatePredecessorBoundary0NF',
    ...expected,
    priorBlockerCoordinates: [...PUBLIC_EMISSION_BLOCKERS0],
  });
}

function validatePublicationDocumentationCoordinate0(coordinate) {
  if (!sameCanonical0(coordinate, PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0)) {
    return validationReject0(
      ['PublicationDocumentationCoordinate'],
      'publication coordinate gate requires the exact public-review documentation coordinate',
      { expected: PUBLIC_REVIEW_DOCUMENTATION_COORDINATE0, actual: coordinate },
    );
  }
  return validationAccept0({
    kind: 'PublicationDocumentationCoordinate0NF',
    coordinateId: coordinate.coordinateId,
    sealedReleaseNotOverwritten: true,
    sourceAndArtifactAccessPublicWithoutRequest: true,
    publicReviewPublicationFraming: true,
  });
}

function validateGateSuite0(suite, publicationDocumentationCoordinate) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['PublicationCoordinateGate'],
      'publication coordinate gate suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makePublicationCoordinateGateSuite0({
    PublicationDocumentationCoordinate: publicationDocumentationCoordinate,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['PublicationCoordinateGate'],
      'publication coordinate gate suite must exactly match the computed publication-coordinate and policy binding',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'PublicationCoordinateGateSuite0NF',
    suiteId: suite.suiteId,
    bindingDigest: suite.binding.bindingDigest,
  });
}

function publicationCoordinateBlockerReason0(coordinate) {
  if (coordinate === 'Release.UnrestrictedFinalSoundness') {
    return 'bounded semantic DAG coverage is complete, but unrestricted final soundness is not represented by this documentation-coordinate gate';
  }
  return 'external review acceptance is not represented by this documentation-coordinate gate';
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
