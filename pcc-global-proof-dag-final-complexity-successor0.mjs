import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGFinalSATReductionSuccessor0,
  makeGlobalProofDAGFinalSATReductionSuccessor0,
} from './pcc-global-proof-dag-final-sat-reduction-successor0.mjs';

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
  GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  makeGlobalFinalSATReductionSemanticSuite0,
} from './pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckGlobalFinalComplexitySemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_COMPLEXITY_SCOPE0,
  makeGlobalFinalComplexitySemanticInput0,
  makeGlobalFinalComplexitySemanticSuite0,
} from './pcc-global-final-complexity-semantic0.mjs';

import {
  STANDARD_COMPLEXITY_BASIS0,
} from './pcc-complexity-bridge0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalComplexityReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorSATReductionGateMustRemainDevelopmentOnly: true,
  predecessorSATReductionGateCannotImplyComplexityReadiness: true,
  finalSATReductionDerivationMustRemainReady: true,
  finalComplexityRefinementMustBeComputed: true,
  complexityNodeBindsSemanticDerivationDigest: true,
  allFinalCoordinatesMayBeBoundedRefinedWithoutPublication: true,
  guardedComplexityRefinementOnly: true,
  cookLevinFormalizationIncluded: false,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
  unrestrictedFinalSoundnessRequiredForPublication: true,
  allFinalNodesRemainPubliclyQuarantined: true,
  publicTheoremEmissionRequiresUnrestrictedFinalSoundness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalComplexityCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker:
    'CheckGlobalProofDAGFinalSATReductionSuccessor0',
  semanticFinalComplexityChecker: 'CheckGlobalFinalComplexitySemantic0',
});

export function makeGlobalProofDAGFinalComplexitySuccessor0({
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
  ComplexityBasis = STANDARD_COMPLEXITY_BASIS0,
  ComplexitySemanticDerivations = makeGlobalFinalComplexitySemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
    SATReductionSemanticDerivations,
    ComplexityBasis,
  }),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGFinalComplexitySuccessor0 Purpose must be one of ${GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticFinalComplexitySuccessor0',
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
    ComplexityBasis,
    ComplexitySemanticDerivations,
    Binding: { ...GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGFinalComplexitySuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalComplexitySuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0',
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
      reason: 'semantic final complexity global readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGFinalComplexityPurpose0NF',
    purpose,
  }));

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGFinalSATReductionSuccessor0',
    () => CheckGlobalProofDAGFinalSATReductionSuccessor0(
      makeGlobalProofDAGFinalSATReductionSuccessor0({
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
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGFinalSATReductionSuccessor0',
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
        reason: 'semantic final SAT-reduction predecessor global gate rejected before complexity upgrade',
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorSATReductionBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorSATReductionBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const complexityCall = await callChecker0(
    'CheckGlobalFinalComplexitySemantic0',
    () => CheckGlobalFinalComplexitySemantic0(
      makeGlobalFinalComplexitySemanticInput0({
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
        ComplexityBasis: input.ComplexityBasis,
        ComplexitySemanticDerivations:
          input.ComplexitySemanticDerivations,
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalFinalComplexitySemantic0',
    complexityCall.ok && complexityCall.record.tag === 'accept',
    complexityCall.ok ? complexityCall.record : complexityCall.witness,
  ));
  if (!complexityCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticFinalComplexity.exception`,
      path: ['ComplexitySemanticDerivations'],
      witness: complexityCall.witness,
      ledger,
    });
  }
  const complexityRecord = complexityCall.record;
  if (complexityRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticFinalComplexity`,
      path: ['ComplexitySemanticDerivations'],
      witness: {
        reason: 'guarded semantic final complexity checker rejected',
        inner: compactRecord0(complexityRecord),
      },
      ledger,
    });
  }
  const complexityNF = complexityRecord.NF ?? complexityRecord.nf ?? {};
  const complexityBoundary = validateComplexityBoundary0(complexityNF);
  ledger.push(makeLedgerEntry0(
    'semanticFinalComplexityBoundary',
    complexityBoundary.ok,
    complexityBoundary.nf ?? complexityBoundary.witness,
  ));
  if (!complexityBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticFinalComplexityBoundary`,
      complexityBoundary,
      ledger,
    );
  }

  const overlay = buildFinalComplexityOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    complexityNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticFinalComplexityOverlay',
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

  const gate = makeFinalComplexityComputedGate0({
    predecessorRecord,
    predecessorNF,
    complexityRecord,
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
        reason: 'guarded final complexity successor is not ready for public final-theorem use',
        blockers: gate.blockers,
        boundedSemanticFinalNodeIds: gate.boundedSemanticFinalNodeIds,
        remainingBlockedFinalNodeIds: gate.remainingBlockedFinalNodeIds,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        guardedComplexityRefinementOnly: true,
        unrestrictedFinalSoundnessReady: false,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticFinalComplexitySuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: 'development-only',

      predecessorGlobalAccepted: true,
      predecessorGlobalChecker: predecessorRecord.checker,
      predecessorGlobalDigest:
        predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorGlobalDevelopmentOnly: true,
      predecessorGlobalPublicTheoremEmissionAllowed: false,
      predecessorGlobalSATReductionReady: true,
      predecessorGlobalComplexityReady: false,

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
      globalFinalSATReductionDerivationReady: true,

      globalFinalComplexitySemanticChecker: complexityRecord.checker,
      globalFinalComplexitySemanticDigest:
        complexityRecord.Digest ?? complexityRecord.digest,
      globalFinalComplexitySemanticReady: true,
      globalFinalComplexityImplicationRefinementReady: true,
      globalFinalComplexityImplicationReady: true,
      globalFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      globalFinalComplexityDerivationDigest:
        complexityNF.complexityDerivationDigest ?? null,
      complexityDerivation: complexityNF.complexityDerivation,
      complexityBridgeDigest: complexityNF.complexityBridgeDigest ?? null,
      complexityBasisDigest: complexityNF.complexityBasisDigest ?? null,
      allGlobalFinalCoordinatesBoundedRefined: true,
      guardedComplexityRefinementOnly: true,
      cookLevinFormalizationIncluded: false,
      standardTheoremDependencyTrustRequired: true,
      unrestrictedComplexityImplicationSoundnessNotClaimed: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'final-complexity-bounded-refinement',

      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),

      boundedSemanticFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
      remainingBlockedFinalNodeIds: [],
      legacyFinalNodesStructurallyAccepted: true,
      legacyFinalNodesQuarantined: true,
      allBoundedRefinedFinalNodesRemainPubliclyQuarantined: true,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      unrestrictedFinalSoundnessReady: false,
      developmentOnly: true,
      finalTheoremReady: false,
      publicTheoremEmissionAllowed: false,
      finalPublicationReadinessRequiresUnrestrictedSoundness: true,
      Scope: { ...GLOBAL_FINAL_COMPLEXITY_SCOPE0 },
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function buildFinalComplexityOverlay0({ dag, predecessorNF, complexityNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for final complexity overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)
      || predecessorOverlay.globalFinalSATReductionDerivationReady !== true
      || predecessorOverlay.globalFinalComplexityImplicationReady !== false
      || !sameCanonical0(
        predecessorOverlay.blockedFinalNodeIds,
        [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'final complexity successor requires the exact SAT-reduction predecessor overlay',
      { actual: predecessorOverlay },
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const node = nodeById.get(GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  const derivation = complexityNF.complexityDerivation;
  if (!isPlainObject0(node) || node.nodeKind !== 'final') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
      'final complexity overlay requires the complexity coordinate as a final node',
      { actual: node },
    );
  }
  if (!isPlainObject0(derivation) || derivation.ready !== true) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'NF', 'complexityDerivation'],
      'final complexity overlay is missing a ready guarded derivation',
      { actual: derivation },
    );
  }
  const nodeDigest = digestCanonical0(stripDigestFields0(node));
  if (!sameCanonical0(nodeDigest, derivation.globalNodeDigest)) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'NF', 'complexityDerivation', 'globalNodeDigest'],
      'final complexity derivation global-node digest mismatch',
      { expected: nodeDigest, actual: derivation.globalNodeDigest },
    );
  }

  const semanticFinalComplexityBinding = Object.freeze({
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    nodeKind: node.nodeKind,
    globalNodeDigest: nodeDigest,
    derivationDigest: derivation.derivationDigest,
    dependencyNodeId: derivation.dependencyNodeId,
    dependencyNodeDigest: derivation.dependencyNodeDigest,
    dependencyDerivationDigest: derivation.dependencyDerivationDigest,
    complexityBasisDigest: derivation.complexityBasisDigest,
    sourceImplicationDigest: derivation.sourceImplicationDigest,
    finalPublicTheoremDigest: derivation.finalPublicTheoremDigest,
    finalTheoremRecordDigest: derivation.finalTheoremRecordDigest,
    complexityBridgeRecordDigest: derivation.complexityBridgeRecordDigest,
    premiseRemovalNegativeProbeDigest:
      derivation.premiseRemovalNegativeProbeDigest,
    unconditionalClaimNegativeProbeDigest:
      derivation.unconditionalClaimNegativeProbeDigest,
    checkerContractDigest: derivation.checkerContractDigest,
    conclusionDigest: derivation.conclusionDigest,
    scope: GLOBAL_FINAL_COMPLEXITY_SCOPE0.scope,
    guardedComplexityRefinement: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    publiclyActive: false,
  });

  const semanticFinalComplexityNodeIds = [GLOBAL_FINAL_COMPLEXITY_NODE_ID0];
  const semanticNodeIds = [
    ...(predecessorOverlay.semanticNodeIds ?? []),
    ...semanticFinalComplexityNodeIds,
  ];
  const structuralOnlyNodeIds = nodes
    .filter((entry) => !semanticNodeIds.includes(entry.id))
    .map((entry) => entry.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalComplexityOverlay0NF',
    ...copyPredecessorOverlay0(predecessorOverlay),
    semanticFinalComplexityNodeIds,
    semanticFinalComplexityBinding,
    blockedFinalNodeIds: [],
    blockedFinalImplicationNodeIds: [],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticFinalComplexityNodeCount: 1,
    blockedFinalNodeCount: 0,
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
    globalFinalComplexityImplicationReady: true,
    allGlobalFinalCoordinatesBoundedRefined: true,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    unrestrictedFinalSoundnessReady: false,
    guardedComplexityRefinementOnly: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    allBoundedRefinedFinalNodesRemainPubliclyQuarantined: true,
  });
}

function makeFinalComplexityComputedGate0({
  predecessorRecord,
  predecessorNF,
  complexityRecord,
  overlay,
}) {
  const nodes = [
    makeGateNode0(
      'Gate.PredecessorSATReduction.DevelopmentAcceptance',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.PredecessorSATReduction.DevelopmentAcceptance'],
      true,
      predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.InfrastructureDerivations',
      ['Gate.PredecessorSATReduction.DevelopmentAcceptance'],
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
      predecessorNF.globalFinalSATReductionSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalComplexityImplication',
      ['Gate.GlobalDAG.FinalSATReductionDerivation'],
      true,
      complexityRecord.Digest ?? complexityRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.BoundedFinalSemanticCoverage',
      [
        'Gate.GlobalDAG.FinalPrefixRefinements',
        'Gate.GlobalDAG.FinalSATReductionDerivation',
        'Gate.GlobalDAG.FinalComplexityImplication',
      ],
      true,
      digestCanonical0([...GLOBAL_DAG_REQUIRED_FINALS0]),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.UnrestrictedFinalSoundness',
      ['Gate.GlobalDAG.BoundedFinalSemanticCoverage'],
      false,
      digestCanonical0({
        unrestrictedSATReductionSoundnessReady: false,
        unrestrictedComplexityImplicationSoundnessReady: false,
        cookLevinFormalizationIncluded: false,
      }),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalDerivations',
      [
        'Gate.GlobalDAG.BoundedFinalSemanticCoverage',
        'Gate.GlobalDAG.UnrestrictedFinalSoundness',
      ],
      false,
      digestCanonical0({
        boundedCoverageReady: true,
        unrestrictedSoundnessReady: false,
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
      digest: predecessorNF.globalFinalSATReductionSemanticDigest ?? null,
      boundedExecutableSATReductionRefinementOnly: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalComplexityImplication',
      ready: true,
      reason: null,
      digest: complexityRecord.Digest ?? complexityRecord.digest,
      guardedComplexityRefinementOnly: true,
      unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.UnrestrictedFinalSoundness',
      ready: false,
      reason: 'bounded executable refinements do not establish unrestricted SAT-reduction soundness or provide a formal Cook-Levin dependency inside this checker stack',
      digest: digestCanonical0({
        unrestrictedSATReductionSoundnessReady: false,
        cookLevinFormalizationIncluded: false,
      }),
    }),
  ];

  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticFinalComplexityGate0',
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
    globalFinalComplexityImplicationReady: true,
    allGlobalFinalCoordinatesBoundedRefined: true,
    unrestrictedFinalSoundnessReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    guardedComplexityRefinementOnly: true,
    cookLevinFormalizationIncluded: false,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    boundedSemanticFinalNodeIds:
      Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    remainingBlockedFinalNodeIds: Object.freeze([]),
    requiredFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    boundedFinalNodesPubliclyActive: false,
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
    globalFinalSATReductionSemanticReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalFinalPrefixRefinementsReady: true,
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic final SAT-reduction predecessor global boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || !sameCanonical0(
        nf.semanticOverlay?.blockedFinalNodeIds,
        [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic final SAT-reduction predecessor must keep exactly the complexity node blocked and expose no active final node',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        blockedFinalNodeIds: nf.semanticOverlay?.blockedFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGFinalComplexityPredecessorBoundary0NF',
    ...expected,
  });
}

function validateComplexityBoundary0(nf) {
  const expected = {
    globalFinalComplexitySemanticReady: true,
    globalFinalComplexityImplicationRefinementReady: true,
    globalFinalComplexityImplicationReady: true,
    allGlobalFinalCoordinatesBoundedRefined: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalPackageDerivationsReady: true,
    guardedComplexityRefinementOnly: true,
    cookLevinFormalizationIncluded: false,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    publicConclusionNotActivated: true,
    publicTheoremEmissionAllowed: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    unrestrictedFinalSoundnessReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['ComplexitySemanticDerivations', 'NF', field],
        'guarded final complexity semantic readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (nf.globalFinalComplexityNodeId !== GLOBAL_FINAL_COMPLEXITY_NODE_ID0
      || nf.globalFinalSATReductionNodeId !== GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'NF'],
      'guarded final complexity node coverage mismatch',
      {
        expectedComplexity: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
        actualComplexity: nf.globalFinalComplexityNodeId,
        expectedSAT: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
        actualSAT: nf.globalFinalSATReductionNodeId,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGFinalComplexitySemanticBoundary0NF',
    ...expected,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'semantic final complexity global successor input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticFinalComplexitySuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic final complexity global successor kind must be GlobalProofDAGSemanticFinalComplexitySuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic final complexity global successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic final complexity global successor Purpose is unsupported',
      { actual: input.Purpose },
    );
  }
  const objectFields = [
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
    'ComplexityBasis',
    'ComplexitySemanticDerivations',
    'Binding',
    'Policy',
  ];
  for (const field of objectFields) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic final complexity global successor is missing a required field',
        { field },
      );
    }
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'semantic final complexity global dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic final complexity global input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(
    input.Binding,
    GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_BINDING0,
  )) {
    return validationReject0(
      ['Binding'],
      'semantic final complexity global checker binding mismatch',
      {
        expected: GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }
  if (!sameCanonical0(
    input.Policy,
    GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_POLICY0,
  )) {
    return validationReject0(
      ['Policy'],
      'semantic final complexity global release policy must match the guarded fail-closed policy',
      {
        expected: GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_POLICY0,
        actual: input.Policy,
      },
    );
  }
  const allowed = new Set(['kind', 'version', 'Purpose', ...objectFields]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic final complexity global successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalComplexitySuccessorShape0NF',
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
    semanticFinalSATReductionNodeIds:
      [...(predecessorOverlay.semanticFinalSATReductionNodeIds ?? [])],
    semanticFinalSATReductionBinding:
      predecessorOverlay.semanticFinalSATReductionBinding
        ? { ...predecessorOverlay.semanticFinalSATReductionBinding }
        : null,
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
