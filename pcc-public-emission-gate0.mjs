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
  CheckGlobalProofDAGFinalComplexitySuccessor0,
  makeGlobalProofDAGFinalComplexitySuccessor0,
} from './pcc-global-proof-dag-final-complexity-successor0.mjs';

const CHECKER_VERSION = 0;

export const PUBLIC_THEOREM_EMISSION_COORDINATE0 =
  'Release.PublicTheoremEmission';

export const PUBLIC_EMISSION_BLOCKERS0 = Object.freeze([
  'Release.UnrestrictedFinalSoundness',
  'Documentation.ImmutablePublicRevision',
  'ExternalReview.Acceptance',
]);

export const PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0 = Object.freeze({
  kind: 'PublicEmissionDocumentationCoordinate0',
  version: CHECKER_VERSION,
  coordinateId: 'PNP-DOC-CPR-2026-06-20-01',
  sealedSourceTag: 'final-pnp-proof-report-hardened-7072f8d',
  sealedSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
  sealedArtifactTag:
    'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
  sealedArtifactDirectory:
    'proof-artifacts/final-pnp-proof-report-hardened-7072f8d/',
  patchPath:
    'documentation-revisions/PNP-DOC-CPR-2026-06-20-01/canonical_proof_report.tex.patch',
  publicRepository: 'https://github.com/aisknab/pnp',
  sourceAndArtifactAccessPublicWithoutRequest: true,
  reviewerGuidePath: 'docs/reviewer_guide.md',
  reproducibilityGuidePath: 'docs/reproducibility.md',
  sealedReleaseNotOverwritten: true,
  documentationOnlyRevision: true,
  directPNPClaimTextStillSealedHistoricalText: true,
  publicEmissionRequiresNewImmutablePublicationCoordinate: true,
});

export const PUBLIC_EMISSION_GATE_POLICY0 = Object.freeze({
  kind: 'PublicTheoremEmissionGatePolicy0',
  version: CHECKER_VERSION,
  requiresFinalComplexitySuccessorAcceptance: true,
  requiresCompleteBoundedSemanticDAGCoverage: true,
  requiresAllFinalNodesSemanticallyRefined: true,
  requiresAllFinalNodesPubliclyQuarantined: true,
  requiresActiveFinalNodeSetEmpty: true,
  requiresDocumentationCoordinateBinding: true,
  requiresSealedReleaseNotOverwritten: true,
  requiresPublicAccessInstructionsDocumented: true,
  requiresNewImmutablePublicationCoordinateBeforeEmission: true,
  callerReadinessAssertionsForbidden: true,
  publicTheoremEmissionAllowed: false,
});

export const PUBLIC_EMISSION_GATE_CONTRACT0 = Object.freeze({
  kind: 'PublicTheoremEmissionGateContract0',
  version: CHECKER_VERSION,
  coordinate: PUBLIC_THEOREM_EMISSION_COORDINATE0,
  predecessorChecker: 'CheckGlobalProofDAGFinalComplexitySuccessor0',
  requiresGlobalSemanticNodeDerivationsReady: true,
  requiresGlobalFinalDerivationsReady: true,
  requiresPublicTheoremEmissionReady: false,
  requiresPublicTheoremEmissionAllowed: false,
  requiresActiveFinalNodeIds: Object.freeze([]),
  requiresQuarantinedFinalNodeIds: GLOBAL_DAG_REQUIRED_FINALS0,
  documentationCoordinate:
    PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0.coordinateId,
  blockers: PUBLIC_EMISSION_BLOCKERS0,
});

export function makePublicTheoremEmissionGateSuite0({
  DocumentationCoordinate = PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0,
} = {}) {
  const base = Object.freeze({
    kind: 'PublicTheoremEmissionGateBinding0',
    version: CHECKER_VERSION,
    coordinate: PUBLIC_THEOREM_EMISSION_COORDINATE0,
    documentationCoordinateId: DocumentationCoordinate.coordinateId ?? null,
    documentationCoordinateDigest: digestCanonical0(DocumentationCoordinate),
    checkerContractDigest: digestCanonical0(PUBLIC_EMISSION_GATE_CONTRACT0),
    policyDigest: digestCanonical0(PUBLIC_EMISSION_GATE_POLICY0),
  });
  return Object.freeze({
    kind: 'PublicTheoremEmissionGateSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.public-theorem-emission.gate.phase40',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...PUBLIC_EMISSION_GATE_POLICY0 },
  });
}

export function makePublicTheoremEmissionGateInput0({
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
  DocumentationCoordinate = PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0,
  PublicEmissionGate = makePublicTheoremEmissionGateSuite0({
    DocumentationCoordinate,
  }),
} = {}) {
  return Object.freeze({
    kind: 'PublicTheoremEmissionGateInput0',
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
    DocumentationCoordinate,
    PublicEmissionGate,
    Policy: { ...PUBLIC_EMISSION_GATE_POLICY0 },
  });
}

export async function CheckPublicTheoremEmissionGate0(input) {
  const checker = 'CheckPublicTheoremEmissionGate0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGFinalComplexitySuccessor0',
    () => CheckGlobalProofDAGFinalComplexitySuccessor0(
      makeGlobalProofDAGFinalComplexitySuccessor0({
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
    'CheckGlobalProofDAGFinalComplexitySuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalComplexityPredecessor.exception`,
      path: ['ComplexitySemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalComplexityPredecessor`,
      path: ['ComplexitySemanticDerivations'],
      witness: {
        reason: 'public-emission gate requires an accepted final-complexity predecessor',
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
    'finalComplexityPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalComplexityPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const docs = validateDocumentationCoordinate0(input.DocumentationCoordinate);
  ledger.push(makeLedgerEntry0(
    'documentationCoordinate',
    docs.ok,
    docs.nf ?? docs.witness,
  ));
  if (!docs.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.documentationCoordinate`,
      docs,
      ledger,
    );
  }

  const suite = validateGateSuite0(
    input.PublicEmissionGate,
    input.DocumentationCoordinate,
  );
  ledger.push(makeLedgerEntry0(
    'publicEmissionGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.publicEmissionGateSuite`,
      suite,
      ledger,
    );
  }

  const blockers = PUBLIC_EMISSION_BLOCKERS0.map((coordinate) => Object.freeze({
    coordinate,
    ready: false,
    reason: publicEmissionBlockerReason0(coordinate),
    digest: digestCanonical0({
      coordinate,
      documentationCoordinate: input.DocumentationCoordinate.coordinateId,
      predecessorDigest: predecessorCall.record.Digest ?? predecessorCall.record.digest,
    }),
  }));

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'PublicTheoremEmissionGate0NF',
      checker,
      version: CHECKER_VERSION,
      publicEmissionGateRepresentedReady: true,
      publicEmissionCoordinate: PUBLIC_THEOREM_EMISSION_COORDINATE0,

      finalComplexityPredecessorAccepted: true,
      finalComplexityPredecessorChecker: predecessorCall.record.checker,
      finalComplexityPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalSemanticNodeDerivationsReady: true,
      globalFinalDerivationsReady: true,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

      documentationCoordinate: input.DocumentationCoordinate,
      documentationCoordinateDigest:
        digestCanonical0(input.DocumentationCoordinate),
      sealedReleaseNotOverwritten: true,
      sourceAndArtifactAccessPublicWithoutRequest: true,
      publicAccessInstructionsDocumented: true,
      directPNPClaimTextStillSealedHistoricalText: true,
      publicEmissionRequiresNewImmutablePublicationCoordinate: true,

      binding: input.PublicEmissionGate.binding,
      bindingDigest: input.PublicEmissionGate.binding.bindingDigest,
      checkerContractDigest: digestCanonical0(PUBLIC_EMISSION_GATE_CONTRACT0),
      blockers,
      blockerCoordinates: blockers.map((entry) => entry.coordinate),
      releasePublicTheoremEmissionBlocked: true,
      releasePublicTheoremEmissionBlockerDigest: digestCanonical0(blockers),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'public theorem emission gate input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'PublicTheoremEmissionGateInput0') {
    return validationReject0(
      ['kind'],
      'public theorem emission gate input kind must be PublicTheoremEmissionGateInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `public theorem emission gate input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
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
    'DocumentationCoordinate',
    'PublicEmissionGate',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'public theorem emission gate input is missing a required field',
        { field },
      );
    }
  }
  for (const field of [
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
    'DocumentationCoordinate',
    'PublicEmissionGate',
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'public theorem emission gate dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'public theorem emission gate input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Policy, PUBLIC_EMISSION_GATE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'public theorem emission gate policy must match the fail-closed policy',
      { expected: PUBLIC_EMISSION_GATE_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
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
    'DocumentationCoordinate',
    'PublicEmissionGate',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'public theorem emission gate rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'PublicTheoremEmissionGateInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    globalFinalDerivationsReady: true,
    globalSemanticNodeDerivationsReady: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['FinalComplexityPredecessor', 'NF', field],
        'final-complexity predecessor public-emission boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.activeFinalNodeIds, [])
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || nf.semanticOverlay?.globalSemanticNodeDerivationsReady !== true
      || nf.semanticOverlay?.publicTheoremEmissionReady !== false) {
    return validationReject0(
      ['FinalComplexityPredecessor', 'NF', 'semanticOverlay'],
      'final-complexity predecessor must keep public emission blocked with all final nodes quarantined',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
        semanticOverlay: nf.semanticOverlay,
      },
    );
  }
  return validationAccept0({
    kind: 'PublicEmissionFinalComplexityPredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
  });
}

function validateDocumentationCoordinate0(coordinate) {
  if (!sameCanonical0(coordinate, PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0)) {
    return validationReject0(
      ['DocumentationCoordinate'],
      'public theorem emission gate requires the exact immutable documentation coordinate',
      { expected: PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0, actual: coordinate },
    );
  }
  return validationAccept0({
    kind: 'PublicEmissionDocumentationCoordinate0NF',
    coordinateId: coordinate.coordinateId,
    sealedReleaseNotOverwritten: true,
    sourceAndArtifactAccessPublicWithoutRequest: true,
    documentationOnlyRevision: true,
  });
}

function validateGateSuite0(suite, documentationCoordinate) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['PublicEmissionGate'],
      'public theorem emission gate suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makePublicTheoremEmissionGateSuite0({
    DocumentationCoordinate: documentationCoordinate,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['PublicEmissionGate'],
      'public theorem emission gate suite must exactly match the computed documentation and policy binding',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'PublicTheoremEmissionGateSuite0NF',
    suiteId: suite.suiteId,
    bindingDigest: suite.binding.bindingDigest,
  });
}

function publicEmissionBlockerReason0(coordinate) {
  if (coordinate === 'Release.UnrestrictedFinalSoundness') {
    return 'bounded semantic DAG coverage is complete, but unrestricted final soundness has not been independently released';
  }
  if (coordinate === 'Documentation.ImmutablePublicRevision') {
    return 'sealed 7072f8d report must not be overwritten; public emission requires a new immutable documentation/publication coordinate';
  }
  return 'external review acceptance is not represented by this executable gate';
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
