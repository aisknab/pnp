import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGPackageSuccessor0,
  makeGlobalProofDAGPackageSuccessor0,
} from './pcc-global-proof-dag-package-successor0.mjs';

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
  CheckGlobalFinalPrefixSemantic0,
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
  GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0,
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticInput0,
  makeGlobalFinalPrefixSemanticSuite0,
} from './pcc-global-final-prefix-semantic0.mjs';

import {
  buildFinalPrefixOverlay0,
  makeFinalPrefixComputedGate0,
} from './pcc-global-final-prefix-overlay0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalPrefixReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorPackageGateMustRemainDevelopmentOnly: true,
  predecessorPackageGateCannotImplyFinalReadiness: true,
  semanticPackageDerivationsMustRemainReady: true,
  finalPrefixRefinementsMustBeComputed: true,
  finalPrefixNodesBindSemanticRefinementDigests: true,
  boundedExecutableFinalPrefixRefinementsOnly: true,
  unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
  semanticallyRefinedFinalNodesRemainPubliclyQuarantined: true,
  satReductionAndComplexityImplicationsRemainBlocked: true,
  finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalPrefixCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGPackageSuccessor0',
  semanticFinalPrefixChecker: 'CheckGlobalFinalPrefixSemantic0',
});

export function makeGlobalProofDAGFinalPrefixSuccessor0({
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
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGFinalPrefixSuccessor0 Purpose must be one of ${GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticFinalPrefixSuccessor0',
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
    Binding: { ...GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGFinalPrefixSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalPrefixSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGFinalPrefixFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalPrefixFinalTheoremReadiness0',
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
      reason: 'semantic final-prefix global readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGFinalPrefixPurpose0NF',
    purpose,
  }));

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGPackageSuccessor0',
    () => CheckGlobalProofDAGPackageSuccessor0(
      makeGlobalProofDAGPackageSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        LocalPackages: input.LocalPackages,
        PackageSemanticDerivations: input.PackageSemanticDerivations,
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGPackageSuccessor0',
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
  const predecessorRecord = predecessorCall.record;
  if (predecessorRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal`,
      path: ['PredecessorGlobal'],
      witness: {
        reason: 'semantic package predecessor global gate rejected before final-prefix upgrade',
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorPackageBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorPackageBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const prefixCall = await callChecker0(
    'CheckGlobalFinalPrefixSemantic0',
    () => CheckGlobalFinalPrefixSemantic0(
      makeGlobalFinalPrefixSemanticInput0({
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
        SemanticFinalPrefix: input.FinalPrefixSemanticDerivations,
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalFinalPrefixSemantic0',
    prefixCall.ok && prefixCall.record.tag === 'accept',
    prefixCall.ok ? prefixCall.record : prefixCall.witness,
  ));
  if (!prefixCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticFinalPrefix.exception`,
      path: ['FinalPrefixSemanticDerivations'],
      witness: prefixCall.witness,
      ledger,
    });
  }
  const prefixRecord = prefixCall.record;
  if (prefixRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticFinalPrefix`,
      path: ['FinalPrefixSemanticDerivations'],
      witness: {
        reason: 'bounded semantic final-prefix refinement checker rejected',
        inner: compactRecord0(prefixRecord),
      },
      ledger,
    });
  }
  const prefixNF = prefixRecord.NF ?? prefixRecord.nf ?? {};
  const prefixBoundary = validatePrefixBoundary0(prefixNF);
  ledger.push(makeLedgerEntry0(
    'semanticFinalPrefixBoundary',
    prefixBoundary.ok,
    prefixBoundary.nf ?? prefixBoundary.witness,
  ));
  if (!prefixBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticFinalPrefixBoundary`,
      prefixBoundary,
      ledger,
    );
  }

  const overlay = buildFinalPrefixOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    prefixNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticFinalPrefixOverlay',
    overlay.ok,
    overlay.nf ?? overlay.witness,
  ));
  if (!overlay.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticOverlay`,
      overlay,
      ledger,
    );
  }

  const gate = makeFinalPrefixComputedGate0({
    predecessorRecord,
    predecessorNF,
    prefixRecord,
    overlay: overlay.nf,
  });
  ledger.push(makeLedgerEntry0(
    'computedGlobalSemanticGate',
    gate.finalTheoremReady,
    gate,
  ));

  if (purpose === 'final-theorem' && !gate.finalTheoremReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['ComputedGlobalGate'],
      witness: {
        reason: 'semantic final-prefix global successor is not ready for final-theorem use',
        blockers: gate.blockers,
        semanticallyRefinedFinalNodeIds:
          gate.semanticallyRefinedFinalNodeIds,
        remainingBlockedFinalNodeIds:
          gate.remainingBlockedFinalNodeIds,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        boundedExecutableFinalPrefixRefinementsOnly: true,
        unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticFinalPrefixSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      predecessorGlobalAccepted: true,
      predecessorGlobalChecker: predecessorRecord.checker,
      predecessorGlobalDigest:
        predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorGlobalDevelopmentOnly: true,
      predecessorGlobalPublicTheoremEmissionAllowed: false,
      predecessorGlobalFinalNodesQuarantined: true,
      predecessorGlobalPackageReady: true,
      predecessorGlobalFinalPrefixReady: false,

      semanticKBundleFinalReady:
        predecessorNF.semanticKBundleFinalReady === true,
      semanticK0ConformanceReady:
        predecessorNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: predecessorNF.semanticSigmaReady === true,
      semanticReflectionReady: predecessorNF.semanticReflectionReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,
      globalRowDerivationsReady:
        predecessorNF.globalRowDerivationsReady === true,
      globalPackageDerivationsReady:
        predecessorNF.globalPackageDerivationsReady === true,

      globalFinalPrefixSemanticChecker: prefixRecord.checker,
      globalFinalPrefixSemanticDigest:
        prefixRecord.Digest ?? prefixRecord.digest,
      globalFinalPrefixSemanticReady: true,
      globalFinalPrefixRefinementsReady: true,
      globalFinalPrefixNodeIds: prefixNF.globalFinalPrefixNodeIds ?? [],
      globalFinalRemainingNodeIds:
        prefixNF.globalFinalRemainingNodeIds ?? [],
      globalFinalPrefixRefinementCount:
        prefixNF.globalFinalPrefixRefinementCount ?? null,
      globalFinalPrefixRefinementDigests:
        prefixNF.finalPrefixRefinementDigests ?? [],
      packSufficiencyDigest: prefixNF.packSufficiencyDigest ?? null,
      boundedExecutableFinalPrefixRefinementsOnly: true,
      unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
      packAcceptanceDoesNotActivatePublicConclusion: true,

      globalFinalSATReductionDerivationReady: false,
      globalFinalComplexityImplicationReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      satReductionSoundnessNotClaimed: true,
      complexityClassImplicationNotClaimed: true,
      Scope: { ...GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0 },

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'final-prefix-semantic-refinement',

      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),

      semanticallyRefinedFinalNodeIds:
        [...GLOBAL_FINAL_PREFIX_NODE_IDS0],
      remainingBlockedFinalNodeIds:
        [...GLOBAL_FINAL_REMAINING_NODE_IDS0],
      legacyFinalNodesStructurallyAccepted: true,
      legacyFinalNodesQuarantined: true,
      semanticallyRefinedFinalNodesRemainPubliclyQuarantined: true,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

      developmentOnly: true,
      finalTheoremReady: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'semantic final-prefix global successor input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticFinalPrefixSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic final-prefix global successor kind must be GlobalProofDAGSemanticFinalPrefixSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic final-prefix global successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic final-prefix global successor Purpose is unsupported',
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
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic final-prefix global successor is missing a required field',
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
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'semantic final-prefix global dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic final-prefix global input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(
    input.Binding,
    GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_BINDING0,
  )) {
    return validationReject0(
      ['Binding'],
      'semantic final-prefix global checker binding mismatch',
      {
        expected: GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }
  if (!sameCanonical0(
    input.Policy,
    GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_POLICY0,
  )) {
    return validationReject0(
      ['Policy'],
      'semantic final-prefix global release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_FINAL_PREFIX_SUCCESSOR_POLICY0,
        actual: input.Policy,
      },
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
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic final-prefix global successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalPrefixSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    globalPackageSemanticReady: true,
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic package predecessor global boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0
      || !sameCanonical0(
        nf.semanticOverlay?.blockedFinalNodeIds,
        GLOBAL_DAG_REQUIRED_FINALS0,
      )
      || nf.semanticOverlay?.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic package predecessor must keep every final node blocked and expose no active final node',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        blockedFinalNodeIds: nf.semanticOverlay?.blockedFinalNodeIds,
        globalFinalDerivationsReady:
          nf.semanticOverlay?.globalFinalDerivationsReady,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGFinalPrefixPredecessorBoundary0NF',
    ...expected,
    blockedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    activeFinalNodeIds: [],
  });
}

function validatePrefixBoundary0(nf) {
  const expected = {
    globalFinalPrefixSemanticReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalPackageSoundnessNodeRefinementReady: true,
    globalGeneratedPackageSufficiencyNodeRefinementReady: true,
    globalPackageDerivationsReady: true,
    boundedExecutableFinalPrefixRefinementsOnly: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
    packAcceptanceDoesNotActivatePublicConclusion: true,
    publicTheoremEmissionAllowed: false,
    globalFinalSATReductionDerivationReady: false,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['FinalPrefixSemanticDerivations', 'NF', field],
        'bounded final-prefix semantic readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.globalFinalPrefixNodeIds, GLOBAL_FINAL_PREFIX_NODE_IDS0)
      || !sameCanonical0(
        nf.globalFinalRemainingNodeIds,
        GLOBAL_FINAL_REMAINING_NODE_IDS0,
      )
      || nf.globalFinalPrefixRefinementCount
        !== GLOBAL_FINAL_PREFIX_NODE_IDS0.length) {
    return validationReject0(
      ['FinalPrefixSemanticDerivations', 'NF'],
      'bounded final-prefix semantic node coverage mismatch',
      {
        expectedPrefix: [...GLOBAL_FINAL_PREFIX_NODE_IDS0],
        actualPrefix: nf.globalFinalPrefixNodeIds,
        expectedRemaining: [...GLOBAL_FINAL_REMAINING_NODE_IDS0],
        actualRemaining: nf.globalFinalRemainingNodeIds,
        actualCount: nf.globalFinalPrefixRefinementCount,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGFinalPrefixSemanticBoundary0NF',
    ...expected,
    globalFinalPrefixNodeIds: [...GLOBAL_FINAL_PREFIX_NODE_IDS0],
    globalFinalRemainingNodeIds: [...GLOBAL_FINAL_REMAINING_NODE_IDS0],
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
