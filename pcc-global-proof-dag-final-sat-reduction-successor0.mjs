import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGFinalPrefixSuccessor0,
  makeGlobalProofDAGFinalPrefixSuccessor0,
} from './pcc-global-proof-dag-final-prefix-successor0.mjs';

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
  CheckGlobalFinalSATReductionSemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  GLOBAL_FINAL_SAT_REDUCTION_SCOPE0,
  makeGlobalFinalSATReductionSemanticInput0,
  makeGlobalFinalSATReductionSemanticSuite0,
} from './pcc-global-final-sat-reduction-semantic0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalSATReductionReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorFinalPrefixGateMustRemainDevelopmentOnly: true,
  predecessorFinalPrefixGateCannotImplySATReductionReadiness: true,
  finalPrefixRefinementsMustRemainReady: true,
  finalSATReductionMustBeComputed: true,
  satReductionNodeBindsSemanticDerivationDigest: true,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  satInPConclusionRemainsPubliclyQuarantined: true,
  pEqualsNPImplicationRemainsBlocked: true,
  finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalSATReductionCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGFinalPrefixSuccessor0',
  semanticFinalSATReductionChecker: 'CheckGlobalFinalSATReductionSemantic0',
});

export function makeGlobalProofDAGFinalSATReductionSuccessor0({
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
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGFinalSATReductionSuccessor0 Purpose must be one of ${GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticFinalSATReductionSuccessor0',
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
    Binding: { ...GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGFinalSATReductionSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalSATReductionSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGFinalSATReductionFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalSATReductionFinalTheoremReadiness0',
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
      reason: 'semantic final SAT-reduction global readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGFinalSATReductionPurpose0NF',
    purpose,
  }));

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGFinalPrefixSuccessor0',
    () => CheckGlobalProofDAGFinalPrefixSuccessor0(
      makeGlobalProofDAGFinalPrefixSuccessor0({
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
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGFinalPrefixSuccessor0',
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
        reason: 'semantic final-prefix predecessor global gate rejected before SAT-reduction upgrade',
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorFinalPrefixBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorFinalPrefixBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const satCall = await callChecker0(
    'CheckGlobalFinalSATReductionSemantic0',
    () => CheckGlobalFinalSATReductionSemantic0(
      makeGlobalFinalSATReductionSemanticInput0({
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
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalFinalSATReductionSemantic0',
    satCall.ok && satCall.record.tag === 'accept',
    satCall.ok ? satCall.record : satCall.witness,
  ));
  if (!satCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticSATReduction.exception`,
      path: ['SATReductionSemanticDerivations'],
      witness: satCall.witness,
      ledger,
    });
  }
  const satRecord = satCall.record;
  if (satRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticSATReduction`,
      path: ['SATReductionSemanticDerivations'],
      witness: {
        reason: 'bounded semantic final SAT-reduction checker rejected',
        inner: compactRecord0(satRecord),
      },
      ledger,
    });
  }
  const satNF = satRecord.NF ?? satRecord.nf ?? {};
  const satBoundary = validateSATBoundary0(satNF);
  ledger.push(makeLedgerEntry0(
    'semanticSATReductionBoundary',
    satBoundary.ok,
    satBoundary.nf ?? satBoundary.witness,
  ));
  if (!satBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticSATReductionBoundary`,
      satBoundary,
      ledger,
    );
  }

  const overlay = buildFinalSATReductionOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    satNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticFinalSATReductionOverlay',
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

  const gate = makeFinalSATReductionComputedGate0({
    predecessorRecord,
    predecessorNF,
    satRecord,
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
        reason: 'semantic final SAT-reduction global successor is not ready for final-theorem use',
        blockers: gate.blockers,
        semanticallyRefinedFinalNodeIds:
          gate.semanticallyRefinedFinalNodeIds,
        remainingBlockedFinalNodeIds:
          gate.remainingBlockedFinalNodeIds,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        boundedExecutableSATReductionRefinementOnly: true,
        unrestrictedSATReductionSoundnessNotClaimed: true,
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticFinalSATReductionSuccessor0NF',
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
      predecessorGlobalFinalPrefixReady: true,
      predecessorGlobalSATReductionReady: false,

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
      globalFinalPrefixRefinementsReady:
        predecessorNF.globalFinalPrefixRefinementsReady === true,

      globalFinalSATReductionSemanticChecker: satRecord.checker,
      globalFinalSATReductionSemanticDigest:
        satRecord.Digest ?? satRecord.digest,
      globalFinalSATReductionSemanticReady: true,
      globalFinalSATReductionDerivationReady: true,
      globalFinalSATReductionNodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
      globalFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      globalFinalSATReductionDerivationDigest:
        satNF.satReductionDerivationDigest ?? null,
      satReductionDerivation: satNF.satReductionDerivation,
      finalIntegrationDigest: satNF.finalIntegrationDigest ?? null,
      boundedExecutableSATReductionRefinementOnly: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
      satInPConclusionRemainsPubliclyQuarantined: true,

      globalFinalComplexityImplicationReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      complexityClassImplicationNotClaimed: true,
      Scope: { ...GLOBAL_FINAL_SAT_REDUCTION_SCOPE0 },

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'final-sat-reduction-semantic-refinement',

      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),

      semanticallyRefinedFinalNodeIds:
        [
          ...(predecessorNF.semanticallyRefinedFinalNodeIds ?? []),
          GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
        ],
      remainingBlockedFinalNodeIds: [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
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

function buildFinalSATReductionOverlay0({ dag, predecessorNF, satNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for SAT-reduction overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)
      || predecessorOverlay.globalFinalPrefixRefinementsReady !== true
      || predecessorOverlay.globalFinalSATReductionDerivationReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'SAT-reduction successor requires the final-prefix semantic predecessor overlay',
      { actual: predecessorOverlay },
    );
  }
  if (!predecessorOverlay.blockedFinalNodeIds?.includes(
    GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedFinalNodeIds'],
      'SAT-reduction predecessor must keep the SAT-in-P final node blocked',
      { actual: predecessorOverlay.blockedFinalNodeIds },
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const node = nodeById.get(GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0);
  if (!isPlainObject0(node) || node.nodeKind !== 'final') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0],
      'SAT-reduction overlay requires the SAT-in-P coordinate as a final node',
      { actual: node },
    );
  }
  const derivation = satNF.satReductionDerivation;
  if (!isPlainObject0(derivation) || derivation.ready !== true) {
    return validationReject0(
      ['SATReductionSemanticDerivations', 'NF', 'satReductionDerivation'],
      'SAT-reduction overlay is missing a ready bounded derivation',
      { actual: derivation },
    );
  }
  const nodeDigest = digestCanonical0(stripDigestFields0(node));
  if (!sameCanonical0(nodeDigest, derivation.globalNodeDigest)) {
    return validationReject0(
      ['SATReductionSemanticDerivations', 'NF', 'satReductionDerivation', 'globalNodeDigest'],
      'SAT-reduction derivation global-node digest mismatch',
      { expected: nodeDigest, actual: derivation.globalNodeDigest },
    );
  }

  const semanticFinalSATReductionBinding = Object.freeze({
    nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    nodeKind: node.nodeKind,
    globalNodeDigest: nodeDigest,
    derivationDigest: derivation.derivationDigest,
    dependencyNodeDigests: derivation.dependencyNodeDigests,
    finalIntegrationDigest: derivation.finalIntegrationDigest,
    satDecisionDigest: derivation.satDecisionDigest,
    satBoundsDigest: derivation.satBoundsDigest,
    positiveRecordDigest: derivation.positiveRecordDigest,
    decisionNegativeProbeDigest: derivation.decisionNegativeProbeDigest,
    minimizerNegativeProbeDigest: derivation.minimizerNegativeProbeDigest,
    checkerContractDigest: derivation.checkerContractDigest,
    conclusionDigest: derivation.conclusionDigest,
    scope: GLOBAL_FINAL_SAT_REDUCTION_SCOPE0.scope,
    boundedExecutableSATReductionRefinement: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    publiclyActive: false,
  });

  const semanticFinalSATReductionNodeIds = [GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0];
  const semanticNodeIds = [
    ...(predecessorOverlay.semanticNodeIds ?? []),
    ...semanticFinalSATReductionNodeIds,
  ];
  const structuralOnlyNodeIds = nodes
    .filter((entry) => !semanticNodeIds.includes(entry.id))
    .map((entry) => entry.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalSATReductionOverlay0NF',
    ...copyPredecessorOverlay0(predecessorOverlay),
    semanticFinalSATReductionNodeIds,
    semanticFinalSATReductionBinding,
    blockedFinalNodeIds: [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
    blockedFinalImplicationNodeIds: [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticFinalSATReductionNodeCount: 1,
    blockedFinalNodeCount: 1,
    quarantinedFinalNodeCount: GLOBAL_DAG_REQUIRED_FINALS0.length,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,

    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutableSATReductionRefinementOnly: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    satInPConclusionRemainsPubliclyQuarantined: true,
  });
}

function makeFinalSATReductionComputedGate0({
  predecessorRecord,
  predecessorNF,
  satRecord,
  overlay,
}) {
  const nodes = [
    makeGateNode0(
      'Gate.PredecessorFinalPrefix.DevelopmentAcceptance',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.PredecessorFinalPrefix.DevelopmentAcceptance'],
      true,
      predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.InfrastructureDerivations',
      ['Gate.PredecessorFinalPrefix.DevelopmentAcceptance'],
      true,
      predecessorNF.globalInfrastructureSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.RowDerivations',
      ['Gate.GlobalDAG.InfrastructureDerivations'],
      true,
      predecessorNF.globalRowSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.PackageDerivations',
      ['Gate.GlobalDAG.RowDerivations'],
      true,
      predecessorNF.globalPackageSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalPrefixRefinements',
      ['Gate.GlobalDAG.PackageDerivations'],
      true,
      predecessorNF.globalFinalPrefixSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalSATReductionDerivation',
      ['Gate.GlobalDAG.FinalPrefixRefinements'],
      true,
      satRecord.Digest ?? satRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalComplexityImplication',
      ['Gate.GlobalDAG.FinalSATReductionDerivation'],
      false,
      digestCanonical0(GLOBAL_FINAL_COMPLEXITY_NODE_ID0),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalDerivations',
      [
        'Gate.GlobalDAG.FinalPrefixRefinements',
        'Gate.GlobalDAG.FinalSATReductionDerivation',
        'Gate.GlobalDAG.FinalComplexityImplication',
      ],
      false,
      digestCanonical0({
        finalPrefixReady: true,
        satReductionReady: true,
        complexityImplicationReady: false,
      }),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.SemanticNodeDerivations',
      [
        'Gate.GlobalDAG.InfrastructureDerivations',
        'Gate.GlobalDAG.RowDerivations',
        'Gate.GlobalDAG.PackageDerivations',
        'Gate.GlobalDAG.FinalDerivations',
      ],
      false,
      digestCanonical0({
        infrastructureReady: true,
        rowReady: true,
        packageReady: true,
        finalReady: false,
      }),
    ),
    makeGateNode0(
      'Gate.FinalTheorem.Readiness',
      [
        'Gate.KBundle.ReflectionFinalReadiness',
        'Gate.GlobalDAG.SemanticNodeDerivations',
      ],
      false,
      digestCanonical0({
        kBundleFinalReady: true,
        globalSemanticNodeDerivationsReady: false,
      }),
    ),
  ];

  const blockers = [
    Object.freeze({
      coordinate: 'KBundle.ReflectionFinalReadiness',
      ready: true,
      reason: null,
      digest: predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.InfrastructureDerivations',
      ready: true,
      reason: null,
      digest: predecessorNF.globalInfrastructureSemanticDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.RowDerivations',
      ready: true,
      reason: null,
      digest: predecessorNF.globalRowSemanticDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.PackageDerivations',
      ready: true,
      reason: null,
      digest: predecessorNF.globalPackageSemanticDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalPrefixRefinements',
      ready: true,
      reason: null,
      digest: predecessorNF.globalFinalPrefixSemanticDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalSATReductionDerivation',
      ready: true,
      reason: null,
      digest: satRecord.Digest ?? satRecord.digest,
      boundedExecutableSATReductionRefinementOnly: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalComplexityImplication',
      ready: false,
      reason: 'the SAT-in-P-to-P-equals-NP complexity-class implication remains quarantined until independently represented',
      digest: digestCanonical0(overlay.blockedFinalImplicationNodeIds[0]),
    }),
  ];

  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticFinalSATReductionGate0',
    version: CHECKER_VERSION,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutableSATReductionRefinementOnly: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    semanticallyRefinedFinalNodeIds: Object.freeze([
      ...(predecessorNF.semanticallyRefinedFinalNodeIds ?? []),
      GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    ]),
    remainingBlockedFinalNodeIds: Object.freeze([GLOBAL_FINAL_COMPLEXITY_NODE_ID0]),
    requiredFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    semanticSATReductionNodePubliclyActive: false,
    legacyFinalNodesStructurallyAccepted: true,
    legacyFinalNodesSemanticallyActive: false,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
  });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    globalFinalPrefixSemanticReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    globalFinalSATReductionDerivationReady: false,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic final-prefix predecessor global boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || !nf.semanticOverlay?.blockedFinalNodeIds?.includes(
        GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic final-prefix predecessor must keep SAT reduction blocked and expose no active final node',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        blockedFinalNodeIds: nf.semanticOverlay?.blockedFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGFinalSATReductionPredecessorBoundary0NF',
    ...expected,
  });
}

function validateSATBoundary0(nf) {
  const expected = {
    globalFinalSATReductionSemanticReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalPackageDerivationsReady: true,
    boundedExecutableSATReductionRefinementOnly: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    satInPPublicConclusionNotActivated: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['SATReductionSemanticDerivations', 'NF', field],
        'bounded final SAT-reduction semantic readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (nf.globalFinalSATReductionNodeId !== GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0
      || nf.globalFinalComplexityNodeId !== GLOBAL_FINAL_COMPLEXITY_NODE_ID0) {
    return validationReject0(
      ['SATReductionSemanticDerivations', 'NF'],
      'bounded final SAT-reduction node coverage mismatch',
      {
        expectedSAT: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
        actualSAT: nf.globalFinalSATReductionNodeId,
        expectedComplexity: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
        actualComplexity: nf.globalFinalComplexityNodeId,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGFinalSATReductionSemanticBoundary0NF',
    ...expected,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'semantic final SAT-reduction global successor input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticFinalSATReductionSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic final SAT-reduction global successor kind must be GlobalProofDAGSemanticFinalSATReductionSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic final SAT-reduction global successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic final SAT-reduction global successor Purpose is unsupported',
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
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic final SAT-reduction global successor is missing a required field',
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
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'semantic final SAT-reduction global dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic final SAT-reduction global input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(
    input.Binding,
    GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_BINDING0,
  )) {
    return validationReject0(
      ['Binding'],
      'semantic final SAT-reduction global checker binding mismatch',
      {
        expected: GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }
  if (!sameCanonical0(
    input.Policy,
    GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_POLICY0,
  )) {
    return validationReject0(
      ['Policy'],
      'semantic final SAT-reduction global release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_FINAL_SAT_REDUCTION_SUCCESSOR_POLICY0,
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
    'SATReductionSemanticDerivations',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic final SAT-reduction global successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalSATReductionSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function copyPredecessorOverlay0(predecessorOverlay) {
  return {
    semanticKBundleDigest: predecessorOverlay.semanticKBundleDigest ?? null,
    semanticKernelNodeIds:
      [...(predecessorOverlay.semanticKernelNodeIds ?? [])],
    blockedKernelNodeIds: [],
    semanticSigmaNodeIds:
      [...(predecessorOverlay.semanticSigmaNodeIds ?? [])],
    blockedSigmaNodeIds: [],
    semanticSigmaBindings:
      predecessorOverlay.semanticSigmaBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticReflectionNodeIds:
      [...(predecessorOverlay.semanticReflectionNodeIds ?? [])],
    blockedReflectionNodeIds: [],
    semanticReflectionBindings:
      predecessorOverlay.semanticReflectionBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticInfrastructureNodeIds:
      [...(predecessorOverlay.semanticInfrastructureNodeIds ?? [])],
    blockedInfrastructureNodeIds: [],
    semanticInfrastructureBindings:
      predecessorOverlay.semanticInfrastructureBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticRowNodeIds:
      [...(predecessorOverlay.semanticRowNodeIds ?? [])],
    blockedRowNodeIds: [],
    semanticRowBindings:
      predecessorOverlay.semanticRowBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticPackageNodeIds:
      [...(predecessorOverlay.semanticPackageNodeIds ?? [])],
    blockedPackageNodeIds: [],
    semanticPackageBindings:
      predecessorOverlay.semanticPackageBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticFinalPrefixNodeIds:
      [...(predecessorOverlay.semanticFinalPrefixNodeIds ?? [])],
    semanticFinalPrefixBindings:
      predecessorOverlay.semanticFinalPrefixBindings?.map((entry) => ({ ...entry })) ?? [],
  };
}

function stripDigestFields0(value) {
  if (!isPlainObject0(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
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

function makeGateNode0(id, premises, ready, digest) {
  return Object.freeze({
    id,
    premises: Object.freeze([...premises]),
    ready,
    digest,
  });
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
