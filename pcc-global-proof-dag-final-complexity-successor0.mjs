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
  makeGlobalFinalSATReductionSemanticSuite0,
} from './pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckGlobalFinalComplexitySemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_COMPLEXITY_SCOPE0,
  makeGlobalFinalComplexitySemanticInput0,
  makeGlobalFinalComplexitySemanticSuite0,
} from './pcc-global-final-complexity-semantic0.mjs';

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
  predecessorSATReductionGateCannotImplyPublicReadiness: true,
  finalSATReductionMustRemainReady: true,
  finalComplexityImplicationMustBeComputed: true,
  complexityNodeBindsSemanticDerivationDigest: true,
  boundedExecutableComplexityImplicationOnly: true,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
  publicTheoremEmissionRemainsSeparate: true,
  finalNodesRemainPubliclyQuarantined: true,
  finalTheoremRequiresPublicEmissionGate: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalComplexityCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGFinalSATReductionSuccessor0',
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
  ComplexitySemanticDerivations = makeGlobalFinalComplexitySemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
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
      coord: `${checker}.semanticComplexity.exception`,
      path: ['ComplexitySemanticDerivations'],
      witness: complexityCall.witness,
      ledger,
    });
  }
  const complexityRecord = complexityCall.record;
  if (complexityRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticComplexity`,
      path: ['ComplexitySemanticDerivations'],
      witness: {
        reason: 'bounded semantic final complexity checker rejected',
        inner: compactRecord0(complexityRecord),
      },
      ledger,
    });
  }
  const complexityNF = complexityRecord.NF ?? complexityRecord.nf ?? {};
  const complexityBoundary = validateComplexityBoundary0(complexityNF);
  ledger.push(makeLedgerEntry0(
    'semanticComplexityBoundary',
    complexityBoundary.ok,
    complexityBoundary.nf ?? complexityBoundary.witness,
  ));
  if (!complexityBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticComplexityBoundary`,
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
        reason: 'semantic final complexity global successor is not ready for public-theorem emission',
        blockers: gate.blockers,
        semanticallyRefinedFinalNodeIds:
          gate.semanticallyRefinedFinalNodeIds,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        boundedExecutableComplexityImplicationOnly: true,
        unrestrictedComplexityImplicationSoundnessNotClaimed: true,
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
      globalFinalSATReductionDerivationReady:
        predecessorNF.globalFinalSATReductionDerivationReady === true,

      globalFinalComplexitySemanticChecker: complexityRecord.checker,
      globalFinalComplexitySemanticDigest:
        complexityRecord.Digest ?? complexityRecord.digest,
      globalFinalComplexitySemanticReady: true,
      globalFinalComplexityImplicationReady: true,
      globalFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      complexityImplicationDerivation:
        complexityNF.complexityImplicationDerivation,
      complexityImplicationDerivationDigest:
        complexityNF.complexityImplicationDerivationDigest ?? null,
      boundedExecutableComplexityImplicationOnly: true,
      unrestrictedComplexityImplicationSoundnessNotClaimed: true,
      pEqualsNPPublicConclusionNotActivated: true,

      globalFinalDerivationsReady: true,
      globalSemanticNodeDerivationsReady: true,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionAllowed: false,
      publicTheoremEmissionRemainsSeparate: true,
      Scope: { ...GLOBAL_FINAL_COMPLEXITY_SCOPE0 },

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'final-complexity-semantic-refinement',

      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),

      semanticallyRefinedFinalNodeIds:
        [...GLOBAL_DAG_REQUIRED_FINALS0],
      remainingBlockedFinalNodeIds: [],
      legacyFinalNodesStructurallyAccepted: true,
      legacyFinalNodesQuarantined: true,
      semanticallyRefinedFinalNodesRemainPubliclyQuarantined: true,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

      developmentOnly: true,
      finalTheoremReady: false,
      finalTheoremRequiresPublicEmissionGate: true,
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
      'legacy global DAG must expose Nodes for complexity overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)
      || predecessorOverlay.globalFinalSATReductionDerivationReady !== true
      || predecessorOverlay.globalFinalComplexityImplicationReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'complexity successor requires the SAT-reduction semantic predecessor overlay',
      { actual: predecessorOverlay },
    );
  }
  if (!predecessorOverlay.blockedFinalNodeIds?.includes(
    GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedFinalNodeIds'],
      'complexity predecessor must keep the P-equals-NP final node blocked',
      { actual: predecessorOverlay.blockedFinalNodeIds },
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const node = nodeById.get(GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  if (!isPlainObject0(node) || node.nodeKind !== 'final') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
      'complexity overlay requires the P-equals-NP coordinate as a final node',
      { actual: node },
    );
  }
  const derivation = complexityNF.complexityImplicationDerivation;
  if (!isPlainObject0(derivation) || derivation.ready !== true) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'NF', 'complexityImplicationDerivation'],
      'complexity overlay is missing a ready bounded derivation',
      { actual: derivation },
    );
  }
  const nodeDigest = digestCanonical0(stripDigestFields0(node));
  if (!sameCanonical0(nodeDigest, derivation.globalNodeDigest)) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'NF', 'complexityImplicationDerivation', 'globalNodeDigest'],
      'complexity derivation global-node digest mismatch',
      { expected: nodeDigest, actual: derivation.globalNodeDigest },
    );
  }

  const semanticFinalComplexityBinding = Object.freeze({
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    nodeKind: node.nodeKind,
    globalNodeDigest: nodeDigest,
    derivationDigest: derivation.derivationDigest,
    dependencyNodeDigest: derivation.dependencyNodeDigest,
    dependencyRefinementDigest: derivation.dependencyRefinementDigest,
    finalTheoremDigest: derivation.finalTheoremDigest,
    complexityImplicationDigest: derivation.complexityImplicationDigest,
    positiveRecordDigest: derivation.positiveRecordDigest,
    premiseNegativeProbeDigest: derivation.premiseNegativeProbeDigest,
    unconditionalNegativeProbeDigest: derivation.unconditionalNegativeProbeDigest,
    checkerContractDigest: derivation.checkerContractDigest,
    conclusionDigest: derivation.conclusionDigest,
    scope: GLOBAL_FINAL_COMPLEXITY_SCOPE0.scope,
    boundedExecutableComplexityImplication: true,
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
    globalFinalDerivationsReady: true,
    globalSemanticNodeDerivationsReady: true,
    publicTheoremEmissionReady: false,
    boundedExecutableComplexityImplicationOnly: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    publicTheoremEmissionRemainsSeparate: true,
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
      'Gate.GlobalDAG.FinalDerivations',
      [
        'Gate.GlobalDAG.FinalPrefixRefinements',
        'Gate.GlobalDAG.FinalSATReductionDerivation',
        'Gate.GlobalDAG.FinalComplexityImplication',
      ],
      true,
      digestCanonical0({
        finalPrefixReady: true,
        satReductionReady: true,
        complexityImplicationReady: true,
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
      true,
      digestCanonical0({
        infrastructureReady: true,
        rowReady: true,
        packageReady: true,
        finalReady: true,
      }),
    ),
    makeGateNode0(
      'Gate.Release.PublicTheoremEmission',
      [
        'Gate.KBundle.ReflectionFinalReadiness',
        'Gate.GlobalDAG.SemanticNodeDerivations',
      ],
      false,
      digestCanonical0({
        semanticNodeDerivationsReady: true,
        publicEmissionSeparatelyGated: true,
      }),
    ),
    makeGateNode0(
      'Gate.FinalTheorem.Readiness',
      ['Gate.Release.PublicTheoremEmission'],
      false,
      digestCanonical0({
        publicTheoremEmissionReady: false,
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
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalComplexityImplication',
      ready: true,
      reason: null,
      digest: complexityRecord.Digest ?? complexityRecord.digest,
      boundedExecutableComplexityImplicationOnly: true,
      unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'Release.PublicTheoremEmission',
      ready: false,
      reason: 'public theorem emission remains a separate release-gate step after semantic final-node coverage',
      digest: digestCanonical0(overlay.quarantinedFinalNodeIds),
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
    globalFinalDerivationsReady: true,
    globalSemanticNodeDerivationsReady: true,
    publicTheoremEmissionReady: false,
    boundedExecutableComplexityImplicationOnly: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    semanticallyRefinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    remainingBlockedFinalNodeIds: Object.freeze([]),
    requiredFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    semanticFinalNodesPubliclyActive: false,
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
      || !nf.semanticOverlay?.blockedFinalNodeIds?.includes(
        GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic final SAT-reduction predecessor must keep complexity implication blocked and expose no active final node',
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
    globalFinalComplexityImplicationReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalPackageDerivationsReady: true,
    boundedExecutableComplexityImplicationOnly: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    pEqualsNPPublicConclusionNotActivated: true,
    publicTheoremEmissionAllowed: false,
    globalFinalDerivationsReady: true,
    globalSemanticNodeDerivationsReady: true,
    publicTheoremEmissionReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['ComplexitySemanticDerivations', 'NF', field],
        'bounded final complexity semantic readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (nf.globalFinalComplexityNodeId !== GLOBAL_FINAL_COMPLEXITY_NODE_ID0) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'NF', 'globalFinalComplexityNodeId'],
      'bounded final complexity node coverage mismatch',
      { expected: GLOBAL_FINAL_COMPLEXITY_NODE_ID0, actual: nf.globalFinalComplexityNodeId },
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
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic final complexity global successor is missing a required field',
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
  ]) {
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
      'semantic final complexity global release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_FINAL_COMPLEXITY_SUCCESSOR_POLICY0,
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
    'ComplexitySemanticDerivations',
    'Binding',
    'Policy',
  ]);
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
