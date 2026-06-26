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

import {
  CheckPublicTheoremEmissionGate0,
  PUBLIC_EMISSION_BLOCKERS0,
  PUBLIC_EMISSION_DOCUMENTATION_COORDINATE0,
  PUBLIC_EMISSION_GATE_POLICY0,
  PUBLIC_THEOREM_EMISSION_COORDINATE0,
  makePublicTheoremEmissionGateInput0,
  makePublicTheoremEmissionGateSuite0,
} from './pcc-public-emission-gate0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_PUBLIC_EMISSION_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_PUBLIC_EMISSION_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGPublicEmissionSuccessorPolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  finalComplexityPredecessorMustAccept: true,
  completeBoundedSemanticDAGCoverageRequired: true,
  publicEmissionGateMustAcceptAsBlocked: true,
  activeFinalNodeSetMustRemainEmpty: true,
  sealedReleaseMustNotBeOverwritten: true,
  documentationCoordinateMustBeImmutable: true,
  finalTheoremRequiresPublicEmissionGate: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_PUBLIC_EMISSION_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGPublicEmissionCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGFinalComplexitySuccessor0',
  publicEmissionGateChecker: 'CheckPublicTheoremEmissionGate0',
});

export function makeGlobalProofDAGPublicEmissionSuccessor0({
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
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_PUBLIC_EMISSION_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGPublicEmissionSuccessor0 Purpose must be one of ${GLOBAL_PUBLIC_EMISSION_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGPublicEmissionSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
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
    Binding: { ...GLOBAL_PUBLIC_EMISSION_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_PUBLIC_EMISSION_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGPublicEmissionSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGPublicEmissionSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGPublicEmissionFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGPublicEmissionFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkGlobalInternal0(input, { checker, requiredPurpose }) {
  const ledger = [];
  const shape = validateShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    const witness = {
      reason: 'public-emission final readiness requires a final-theorem purpose record',
      requiredPurpose,
      actualPurpose: input.Purpose,
    };
    ledger.push(makeLedgerEntry0('purpose', false, witness));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.purpose`,
      path: ['Purpose'],
      witness,
      ledger,
    });
  }
  const purpose = requiredPurpose ?? input.Purpose;
  ledger.push(makeLedgerEntry0('purpose', true, {
    kind: 'GlobalProofDAGPublicEmissionPurpose0NF',
    purpose,
  }));

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
      coord: `${checker}.predecessorGlobal.exception`,
      path: ['PredecessorGlobal'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal`,
      path: ['PredecessorGlobal'],
      witness: {
        reason: 'final-complexity predecessor rejected before public-emission gate',
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

  const gateCall = await callChecker0(
    'CheckPublicTheoremEmissionGate0',
    () => CheckPublicTheoremEmissionGate0(
      makePublicTheoremEmissionGateInput0({
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
        DocumentationCoordinate: input.DocumentationCoordinate,
        PublicEmissionGate: input.PublicEmissionGate,
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckPublicTheoremEmissionGate0',
    gateCall.ok && gateCall.record.tag === 'accept',
    gateCall.ok ? gateCall.record : gateCall.witness,
  ));
  if (!gateCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.publicEmissionGate.exception`,
      path: ['PublicEmissionGate'],
      witness: gateCall.witness,
      ledger,
    });
  }
  if (gateCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.publicEmissionGate`,
      path: ['PublicEmissionGate'],
      witness: {
        reason: 'public theorem emission gate rejected',
        inner: compactRecord0(gateCall.record),
      },
      ledger,
    });
  }
  const gateNF = gateCall.record.NF ?? gateCall.record.nf ?? {};
  const gateBoundary = validateGateBoundary0(gateNF);
  ledger.push(makeLedgerEntry0(
    'publicEmissionGateBoundary',
    gateBoundary.ok,
    gateBoundary.nf ?? gateBoundary.witness,
  ));
  if (!gateBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.publicEmissionGateBoundary`,
      gateBoundary,
      ledger,
    );
  }

  const computedGate = makeComputedPublicEmissionGate0({
    predecessorRecord: predecessorCall.record,
    predecessorNF,
    gateRecord: gateCall.record,
    gateNF,
  });
  ledger.push(makeLedgerEntry0(
    'computedPublicEmissionGate',
    computedGate.finalTheoremReady,
    computedGate,
  ));

  if (purpose === 'final-theorem' && !computedGate.finalTheoremReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['ComputedPublicEmissionGate'],
      witness: {
        reason: 'public theorem emission successor is not ready for final-theorem use',
        blockers: computedGate.blockers,
        activeFinalNodeIds: computedGate.activeFinalNodeIds,
        quarantinedFinalNodeIds: computedGate.quarantinedFinalNodeIds,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGPublicEmissionSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: 'development-only',

      predecessorGlobalAccepted: true,
      predecessorGlobalChecker: predecessorCall.record.checker,
      predecessorGlobalDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      predecessorGlobalSemanticNodeDerivationsReady: true,
      predecessorGlobalFinalDerivationsReady: true,

      publicEmissionGateChecker: gateCall.record.checker,
      publicEmissionGateDigest: gateCall.record.Digest ?? gateCall.record.digest,
      publicEmissionGateRepresentedReady: true,
      publicEmissionCoordinate: PUBLIC_THEOREM_EMISSION_COORDINATE0,
      documentationCoordinate: input.DocumentationCoordinate,
      documentationCoordinateDigest:
        digestCanonical0(input.DocumentationCoordinate),
      documentationOnlyRevision: true,
      sealedReleaseNotOverwritten: true,
      sourceAndArtifactAccessPublicWithoutRequest: true,

      globalSemanticNodeDerivationsReady: true,
      globalFinalDerivationsReady: true,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionAllowed: false,
      releasePublicTheoremEmissionBlocked: true,
      releasePublicTheoremEmissionBlockers: [...PUBLIC_EMISSION_BLOCKERS0],
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
      finalTheoremReady: false,
      developmentOnly: true,

      semanticOverlay: predecessorNF.semanticOverlay,
      semanticOverlayDigest: digestCanonical0(predecessorNF.semanticOverlay ?? null),
      computedPublicEmissionGate: computedGate,
      computedPublicEmissionGateDigest: digestCanonical0(computedGate),
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'public-emission successor input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalProofDAGPublicEmissionSuccessor0') {
    return validationReject0(
      ['kind'],
      'public-emission successor kind must be GlobalProofDAGPublicEmissionSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `public-emission successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_PUBLIC_EMISSION_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'public-emission successor Purpose is unsupported',
      { actual: input.Purpose },
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
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'public-emission successor is missing a required field',
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
        'public-emission successor dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'public-emission successor input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Binding, GLOBAL_PUBLIC_EMISSION_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'public-emission successor checker binding mismatch',
      { expected: GLOBAL_PUBLIC_EMISSION_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_PUBLIC_EMISSION_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'public-emission successor policy mismatch',
      { expected: GLOBAL_PUBLIC_EMISSION_SUCCESSOR_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'Purpose',
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
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'public-emission successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'GlobalProofDAGPublicEmissionSuccessorShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    globalSemanticNodeDerivationsReady: true,
    globalFinalDerivationsReady: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['FinalComplexityPredecessor', 'NF', field],
        'public-emission successor predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.activeFinalNodeIds, [])
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)) {
    return validationReject0(
      ['FinalComplexityPredecessor', 'NF', 'activeFinalNodeIds'],
      'public-emission predecessor must expose no active final node and must quarantine all finals',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
      },
    );
  }
  return validationAccept0({ kind: 'PublicEmissionPredecessorBoundary0NF', ...expected });
}

function validateGateBoundary0(nf) {
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
        ['PublicEmissionGate', 'NF', field],
        'public theorem emission gate boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.activeFinalNodeIds, [])
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)) {
    return validationReject0(
      ['PublicEmissionGate', 'NF', 'quarantinedFinalNodeIds'],
      'public theorem emission gate must keep all final nodes quarantined',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
      },
    );
  }
  return validationAccept0({ kind: 'PublicEmissionGateBoundary0NF', ...expected });
}

function makeComputedPublicEmissionGate0({ predecessorRecord, gateRecord, gateNF }) {
  const blockers = gateNF.blockers ?? [];
  const nodes = [
    makeGateNode0(
      'Gate.GlobalDAG.SemanticNodeDerivations',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.Release.PublicTheoremEmission',
      ['Gate.GlobalDAG.SemanticNodeDerivations'],
      false,
      gateRecord.Digest ?? gateRecord.digest,
    ),
    makeGateNode0(
      'Gate.FinalTheorem.Readiness',
      ['Gate.Release.PublicTheoremEmission'],
      false,
      digestCanonical0({ publicTheoremEmissionAllowed: false }),
    ),
  ];
  return Object.freeze({
    kind: 'GlobalProofDAGComputedPublicEmissionGate0',
    version: CHECKER_VERSION,
    globalSemanticNodeDerivationsReady: true,
    globalFinalDerivationsReady: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.map((entry) => entry.coordinate),
    ),
    activeFinalNodeIds: Object.freeze([]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    documentationCoordinateDigest: gateNF.documentationCoordinateDigest,
    releasePublicTheoremEmissionBlocked: true,
  });
}

function makeGateNode0(id, premises, ready, digest) {
  return Object.freeze({
    id,
    premises: Object.freeze([...premises]),
    ready,
    digest,
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
  return makeRejectRecord0({ checker, coord, path: result.path, witness: result.witness, ledger });
}

function makeRejectRecord0({ checker, coord, path, witness, ledger }) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness, ledger };
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
  return { ok: false, path, witness: { reason, ...(details ?? {}) } };
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
