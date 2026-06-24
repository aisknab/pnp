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
  CheckFinalIntegration0,
} from './pcc-final-framework0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0 =
  'Final.AcceptedPackageImpliesSATinP';

export const GLOBAL_FINAL_COMPLEXITY_NODE_ID0 =
  'Final.AcceptedPackageImpliesPEqualsNP';

export const GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0 = Object.freeze([
  'Package.G.LockedNANDThreshold',
  'Package.O.ZeroSlackOracle',
  'Final.GeneratedPackageSufficiency',
]);

export const GLOBAL_FINAL_SAT_REDUCTION_SCOPE0 = Object.freeze({
  kind: 'GlobalFinalSATReductionSemanticScope0',
  version: CHECKER_VERSION,
  scope: 'bounded-executable-sat-reduction-refinement',
  finalPrefixPredecessorChecked: true,
  finalIntegrationReplayed: true,
  finalFrameworkMatchReplayed: true,
  satDecisionRecordReplayed: true,
  satBoundsRecordReplayed: true,
  exactMinimizerBridgeMetadataChecked: true,
  lockedNANDThresholdDependencyChecked: true,
  zeroSlackOracleDependencyChecked: true,
  generatedPackageSufficiencyDependencyChecked: true,
  decisionComparatorNegativeProbeChecked: true,
  exactMinimizerNegativeProbeChecked: true,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  complexityClassImplicationNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const GLOBAL_FINAL_SAT_REDUCTION_POLICY0 = Object.freeze({
  kind: 'GlobalFinalSATReductionSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresFinalPrefixSuccessorAcceptance: true,
  requiresFinalIntegrationAcceptance: true,
  requiresExactPCCPackSurfaceAlignment: true,
  requiresExactFinalSATNodeContract: true,
  requiresExactPCCMinBridgeRecord: true,
  requiresSATDecisionComparatorMinGreaterThanBaseline: true,
  requiresResidualSlackBoundFour: true,
  requiresPolynomialBoundExtraction: true,
  requiresDecisionComparatorNegativeProbe: true,
  requiresExactMinimizerNegativeProbe: true,
  bindsGlobalNodeDigest: true,
  bindsDependencyNodeDigests: true,
  bindsFinalIntegrationDigest: true,
  bindsSATDecisionAndBoundsDigests: true,
  bindsPositiveAndNegativeRecordDigests: true,
  callerReadinessAssertionsForbidden: true,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  pEqualsNPImplicationRemainsSeparate: true,
});

export const GLOBAL_FINAL_SAT_REDUCTION_CONTRACT0 = Object.freeze({
  kind: 'GlobalFinalSATReductionCheckerContract0',
  version: CHECKER_VERSION,
  nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  nodeKind: 'final',
  label: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  premises: GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0,
  conclusionTag: 'FinalTheoremAccepted0',
  theorem: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  sourceImplicationId: 'PackageAcceptanceImpliesSATinP',
  sourceConclusion: 'SAT in P',
  finalIntegrationChecker: 'CheckFinalIntegration0',
  finalFrameworkChecker: 'CheckFinalFrameworkMatch0',
  satDecisionChecker: 'CheckSATDecision0',
  satBoundsChecker: 'CheckSATBounds0',
  exactMinimizer: 'PCCMin',
  residualBandBound: 4,
  decisionComparator: 'minSize>baseline',
  finalPolynomialExponent: 42,
  decisionComparatorNegativeMutation: 'minSize>=baseline',
  exactMinimizerNegativeField: 'SATBounds.Minimizer.exact',
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
});

export function makeGlobalFinalSATReductionSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  PCCPack = makeGlobalFinalPrefixPCCPack0({ LegacyGlobalProofDAG }),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  return Object.freeze({
    kind: 'GlobalFinalSATReductionSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.final-sat-reduction.semantic.phase38',
    reductionBinding: makeSATReductionBinding0({
      node: nodeById.get(GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0) ?? null,
      dependencyNodes: GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0
        .map((nodeId) => nodeById.get(nodeId) ?? null),
      PCCPack,
    }),
    Scope: { ...GLOBAL_FINAL_SAT_REDUCTION_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_SAT_REDUCTION_POLICY0 },
  });
}

export function makeGlobalFinalSATReductionSemanticInput0({
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
} = {}) {
  return Object.freeze({
    kind: 'GlobalFinalSATReductionSemanticInput0',
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
    Scope: { ...GLOBAL_FINAL_SAT_REDUCTION_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_SAT_REDUCTION_POLICY0 },
  });
}

export async function CheckGlobalFinalSATReductionSemantic0(input) {
  const checker = 'CheckGlobalFinalSATReductionSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

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
      coord: `${checker}.finalPrefixPredecessor.exception`,
      path: ['FinalPrefixSemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalPrefixPredecessor`,
      path: ['FinalPrefixSemanticDerivations'],
      witness: {
        reason: 'SAT-reduction refinement requires an accepted final-prefix predecessor',
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
    'finalPrefixPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalPrefixPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const integrationCall = await callChecker0(
    'CheckFinalIntegration0',
    () => CheckFinalIntegration0(input.PCCPack.FinalIntegration),
  );
  ledger.push(makeLedgerEntry0(
    'CheckFinalIntegration0',
    integrationCall.ok && isFinalIntegrationAccept0(integrationCall.record),
    integrationCall.ok ? integrationCall.record : integrationCall.witness,
  ));
  if (!integrationCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalIntegration.exception`,
      path: ['PCCPack', 'FinalIntegration'],
      witness: integrationCall.witness,
      ledger,
    });
  }
  if (!isFinalIntegrationAccept0(integrationCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalIntegration`,
      path: ['PCCPack', 'FinalIntegration'],
      witness: {
        reason: 'SAT-reduction refinement requires accepted final integration',
        inner: compactRecord0(integrationCall.record),
      },
      ledger,
    });
  }

  const alignment = validatePackAlignment0(input);
  ledger.push(makeLedgerEntry0(
    'packSurfaceAlignment',
    alignment.ok,
    alignment.nf ?? alignment.witness,
  ));
  if (!alignment.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.packSurfaceAlignment`,
      alignment,
      ledger,
    );
  }

  const suite = validateSemanticSuite0(
    input.SATReductionSemanticDerivations,
    input.LegacyGlobalProofDAG,
    input.PCCPack,
  );
  ledger.push(makeLedgerEntry0(
    'semanticSATReductionSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticSATReductionSuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const reduction = await deriveSATReduction0({
    node: nodeById.get(GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0),
    dependencyNodes: GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0
      .map((nodeId) => nodeById.get(nodeId)),
    binding: input.SATReductionSemanticDerivations.reductionBinding,
    pack: input.PCCPack,
    positiveRecord: integrationCall.record,
    predecessorNF,
    globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
  });
  ledger.push(makeLedgerEntry0(
    'finalSATReduction.Final.AcceptedPackageImpliesSATinP',
    reduction.ok,
    reduction.nf ?? reduction.witness,
  ));
  if (!reduction.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalSATReduction.Final.AcceptedPackageImpliesSATinP`,
      reduction,
      ledger,
    );
  }

  const integrationNF = integrationCall.record.NF ?? integrationCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalFinalSATReductionSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalFinalSATReductionSemanticReady: true,
      globalFinalSATReductionDerivationReady: true,

      finalPrefixPredecessorAccepted: true,
      finalPrefixPredecessorChecker: predecessorCall.record.checker,
      finalPrefixPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalFinalPrefixRefinementsReady:
        predecessorNF.globalFinalPrefixRefinementsReady === true,
      globalPackageDerivationsReady:
        predecessorNF.globalPackageDerivationsReady === true,
      globalRowDerivationsReady:
        predecessorNF.globalRowDerivationsReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,
      semanticKBundleFinalReady:
        predecessorNF.semanticKBundleFinalReady === true,

      finalIntegrationAccepted: true,
      finalIntegrationChecker: integrationCall.record.checker,
      finalIntegrationDigest:
        integrationCall.record.Digest ?? integrationCall.record.digest,
      finalIntegrationNFKind: integrationNF.kind,
      pccPackDigest: digestCanonical0(input.PCCPack),
      finalFrameworkMatchDigest:
        digestCanonical0(input.PCCPack.FinalIntegration.FinalMatch),
      satDecisionDigest:
        digestCanonical0(input.PCCPack.FinalIntegration.SATDecision),
      satBoundsDigest:
        digestCanonical0(input.PCCPack.FinalIntegration.SATBounds),
      pccMinBridgeDigest:
        digestCanonical0(input.PCCPack.FinalTheorem.PCCMinBridge),
      satImplicationSourceDigest:
        digestCanonical0(
          input.PCCPack.FinalTheorem.AcceptedPackageImpliesSATinP,
        ),

      globalFinalSATReductionNodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
      globalFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      satReductionDerivation: reduction.nf,
      satReductionDerivationDigest: reduction.nf.derivationDigest,
      satReductionBindingDigest: reduction.nf.bindingDigest,

      Scope: { ...GLOBAL_FINAL_SAT_REDUCTION_SCOPE0 },
      scopeDigest: digestCanonical0(input.Scope),
      boundedExecutableSATReductionRefinementOnly: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
      satInPPublicConclusionNotActivated: true,
      complexityClassImplicationNotClaimed: true,
      publicTheoremEmissionAllowed: false,

      globalFinalComplexityImplicationReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      pEqualsNPImplicationRemainsSeparate: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

async function deriveSATReduction0({
  node,
  dependencyNodes,
  binding,
  pack,
  positiveRecord,
  predecessorNF,
  globalBoundsExponent,
}) {
  const nodeValidation = validateSATReductionNode0({
    node,
    globalBoundsExponent,
  });
  if (!nodeValidation.ok) return nodeValidation;

  const deps = validateSATReductionDependencies0({
    dependencyNodes,
    predecessorNF,
  });
  if (!deps.ok) return deps;

  const source = validateSATReductionSourceRecords0(pack);
  if (!source.ok) return source;

  const expectedBinding = makeSATReductionBinding0({
    node,
    dependencyNodes,
    PCCPack: pack,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SATReductionSemanticDerivations', 'reductionBinding'],
      'SAT-reduction binding must exactly match the final node, dependencies, final integration surfaces, source records, and executable contract',
      { expected: expectedBinding, actual: binding },
    );
  }

  const decisionProbe = await runFinalIntegrationNegativeProbe0({
    integration: pack.FinalIntegration,
    probeName: 'SATDecisionComparator',
    mutate: (value) => ({
      ...value,
      SATDecision: {
        ...value.SATDecision,
        DecisionRule: {
          ...value.SATDecision.DecisionRule,
          comparator: GLOBAL_FINAL_SAT_REDUCTION_CONTRACT0
            .decisionComparatorNegativeMutation,
        },
      },
    }),
  });
  if (!decisionProbe.ok) return decisionProbe;

  const minimizerProbe = await runFinalIntegrationNegativeProbe0({
    integration: pack.FinalIntegration,
    probeName: 'SATBoundsMinimizerExactness',
    mutate: (value) => ({
      ...value,
      SATBounds: {
        ...value.SATBounds,
        Minimizer: {
          ...value.SATBounds.Minimizer,
          exact: false,
        },
      },
    }),
  });
  if (!minimizerProbe.ok) return minimizerProbe;

  const conclusion = Object.freeze({
    kind: 'GlobalFinalSATReductionConclusion0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    dependencies: [...GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0],
    finalIntegrationAccepted: true,
    exactMinimizerBridgeMetadataChecked: true,
    satDecisionComparatorChecked: true,
    polynomialBoundExtractionChecked: true,
    decisionComparatorNegativeProbeRejected: true,
    exactMinimizerNegativeProbeRejected: true,
    boundedExecutableSATReductionRefinement: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    publicSATinPConclusionNotActivated: true,
  });
  const nf = {
    kind: 'GlobalFinalSATReductionDerivation0NF',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    theorem: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    globalNodeDigest: expectedBinding.globalNodeDigest,
    dependencyNodeDigests: expectedBinding.dependencyNodeDigests,
    dependencyRefinementDigests: deps.nf.dependencyRefinementDigests,
    finalIntegrationDigest: expectedBinding.finalIntegrationDigest,
    finalFrameworkMatchDigest: expectedBinding.finalFrameworkMatchDigest,
    satDecisionDigest: expectedBinding.satDecisionDigest,
    satBoundsDigest: expectedBinding.satBoundsDigest,
    gpackDigest: expectedBinding.gpackDigest,
    pccMinBridgeDigest: expectedBinding.pccMinBridgeDigest,
    satImplicationSourceDigest: expectedBinding.satImplicationSourceDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    positiveRecordDigest: positiveRecord.Digest ?? positiveRecord.digest,
    decisionNegativeProbeDigest: decisionProbe.nf.recordDigest,
    minimizerNegativeProbeDigest: minimizerProbe.nf.recordDigest,
    baseline: source.nf.baseline,
    fullWordSize: source.nf.fullWordSize,
    residualSlackBound: source.nf.residualSlackBound,
    decisionComparator: source.nf.decisionComparator,
    finalPolynomialExponent: source.nf.finalPolynomialExponent,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    boundedExecutableSATReductionRefinement: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    publicSATinPConclusionNotActivated: true,
    ready: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function makeSATReductionBinding0({ node, dependencyNodes, PCCPack }) {
  const base = Object.freeze({
    kind: 'GlobalFinalSATReductionSemanticBinding0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    dependencyNodeIds: [...GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0],
    dependencyNodeDigests: dependencyNodes.map((dependencyNode) => ({
      nodeId: dependencyNode?.id ?? null,
      digest: digestCanonical0(stripDigestFields0(dependencyNode)),
    })),
    finalIntegrationDigest: digestCanonical0(PCCPack?.FinalIntegration ?? null),
    finalFrameworkMatchDigest:
      digestCanonical0(PCCPack?.FinalIntegration?.FinalMatch ?? null),
    satDecisionDigest:
      digestCanonical0(PCCPack?.FinalIntegration?.SATDecision ?? null),
    satBoundsDigest:
      digestCanonical0(PCCPack?.FinalIntegration?.SATBounds ?? null),
    gpackDigest: digestCanonical0(PCCPack?.FinalIntegration?.GPack ?? null),
    pccMinBridgeDigest:
      digestCanonical0(PCCPack?.FinalTheorem?.PCCMinBridge ?? null),
    satImplicationSourceDigest:
      digestCanonical0(
        PCCPack?.FinalTheorem?.AcceptedPackageImpliesSATinP ?? null,
      ),
    checkerContractDigest: digestCanonical0(GLOBAL_FINAL_SAT_REDUCTION_CONTRACT0),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function validateSATReductionNode0({ node, globalBoundsExponent }) {
  const contract = GLOBAL_FINAL_SAT_REDUCTION_CONTRACT0;
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'SAT-reduction final coordinate is missing its global node',
      { nodeId: contract.nodeId },
    );
  }
  if (node.id !== contract.nodeId
      || node.nodeKind !== contract.nodeKind
      || node.label !== contract.label) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'SAT-reduction global node identity, kind, or label mismatch',
      { contract, actual: node },
    );
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'],
      'SAT-reduction global node premise list must exactly match its contract',
      { expected: contract.premises, actual: node.premises },
    );
  }
  if (!sameCanonical0(node.imports, [])
      || String(node.mode ?? 'Full').trim().toLowerCase() !== 'full'
      || !sameCanonical0(node.payload, {})
      || node.route !== null
      || node.rank !== null) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'SAT-reduction global node must retain empty imports/payload, Full mode, and null route/rank',
      {
        imports: node.imports,
        mode: node.mode,
        payload: node.payload,
        route: node.route,
        rank: node.rank,
      },
    );
  }
  if (node.conclusion?.tag !== contract.conclusionTag
      || node.conclusion?.theorem !== contract.theorem
      || Object.keys(node.conclusion).length !== 2) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'conclusion'],
      'SAT-reduction global node conclusion must exactly match its theorem coordinate',
      { expected: contract.theorem, actual: node.conclusion },
    );
  }
  if (!isPlainObject0(node.bounds)
      || node.bounds.polynomial !== true
      || !Number.isInteger(node.bounds.exponent)
      || node.bounds.exponent <= 0
      || !Number.isInteger(globalBoundsExponent)
      || node.bounds.exponent > globalBoundsExponent) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'bounds'],
      'SAT-reduction global node must carry a positive polynomial bound inside the global envelope',
      { globalBoundsExponent, actual: node.bounds },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionNodeContract0NF',
    nodeId: contract.nodeId,
    exponent: node.bounds.exponent,
  });
}

function validateSATReductionDependencies0({ dependencyNodes, predecessorNF }) {
  const byId = new Map(dependencyNodes.map((node) => [node?.id, node]));
  for (const nodeId of GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0) {
    const node = byId.get(nodeId);
    if (!isPlainObject0(node)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', nodeId],
        'SAT-reduction dependency node is missing',
        { nodeId },
      );
    }
  }
  const packageBindings = new Map(
    (predecessorNF.semanticOverlay?.semanticPackageBindings ?? [])
      .map((entry) => [entry.nodeId, entry]),
  );
  const finalPrefixBindings = new Map(
    (predecessorNF.semanticOverlay?.semanticFinalPrefixBindings ?? [])
      .map((entry) => [entry.nodeId, entry]),
  );
  const needed = [
    ['Package.G.LockedNANDThreshold', packageBindings],
    ['Package.O.ZeroSlackOracle', packageBindings],
    ['Final.GeneratedPackageSufficiency', finalPrefixBindings],
  ];
  const dependencyRefinementDigests = [];
  for (const [nodeId, bindingMap] of needed) {
    const binding = bindingMap.get(nodeId);
    if (!isPlainObject0(binding)) {
      return validationReject0(
        ['FinalPrefixPredecessor', 'semanticOverlay', nodeId],
        'SAT-reduction dependency must have an accepted predecessor semantic binding',
        { nodeId },
      );
    }
    dependencyRefinementDigests.push({
      nodeId,
      digest: binding.refinementDigest
        ?? binding.derivationDigest
        ?? binding.digest
        ?? null,
    });
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionDependencies0NF',
    dependencyNodeIds: [...GLOBAL_FINAL_SAT_REDUCTION_DEPENDENCY_NODE_IDS0],
    dependencyRefinementDigests,
  });
}

function validateSATReductionSourceRecords0(pack) {
  const integration = pack.FinalIntegration;
  const bridge = pack.FinalTheorem?.PCCMinBridge;
  const implication = pack.FinalTheorem?.AcceptedPackageImpliesSATinP;
  const decision = integration?.SATDecision;
  const bounds = integration?.SATBounds;
  const match = integration?.FinalMatch;

  if (!isPlainObject0(integration)
      || !isPlainObject0(bridge)
      || !isPlainObject0(implication)
      || !isPlainObject0(decision)
      || !isPlainObject0(bounds)
      || !isPlainObject0(match)) {
    return validationReject0(
      ['PCCPack'],
      'SAT-reduction source surfaces must include final integration, bridge, implication, decision, bounds, and match records',
      {
        hasIntegration: isPlainObject0(integration),
        hasBridge: isPlainObject0(bridge),
        hasImplication: isPlainObject0(implication),
        hasDecision: isPlainObject0(decision),
        hasBounds: isPlainObject0(bounds),
        hasMatch: isPlainObject0(match),
      },
    );
  }

  const bridgeExpected = {
    exactMinimizer: 'PCCMin',
    residualBandBound: 4,
    residualBandPolynomial: true,
    lockedNANDReduction: true,
    satReduction: true,
    usesExactMinimum: true,
    rejectsApproximateMinimum: true,
    decisionComparator: 'minSize>baseline',
  };
  for (const [field, expected] of Object.entries(bridgeExpected)) {
    if (bridge[field] !== expected) {
      return validationReject0(
        ['PCCPack', 'FinalTheorem', 'PCCMinBridge', field],
        'SAT-reduction PCCMin bridge field mismatch',
        { field, expected, actual: bridge[field] },
      );
    }
  }

  const implicationExpected = {
    kind: 'FinalImplication0',
    id: 'PackageAcceptanceImpliesSATinP',
    conclusion: 'SAT in P',
    public: true,
    polynomial: true,
    usesPCCMinBridge: true,
    usesSATDecision: true,
    usesAcceptedGPack: true,
    usesAcceptedGlobalProofDAG: true,
    usesGlobalGThreshold: true,
    usesGThresholdProofRef: true,
    usesFinalIntegrationGlobalGLinkage: true,
  };
  for (const [field, expected] of Object.entries(implicationExpected)) {
    if (implication[field] !== expected) {
      return validationReject0(
        ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesSATinP', field],
        'SAT-reduction source implication field mismatch',
        { field, expected, actual: implication[field] },
      );
    }
  }
  for (const assumption of [
    'CheckPCCPackexp(P)=accept',
    'CheckGPack0(GPack)=accept',
    'CheckGlobalProofDAG0(GlobalProofDAG)=accept',
    'CheckFinalIntegration0(FinalIntPack)=accept',
    'Package.G.LockedNANDThreshold',
    'G.ThresholdCert.proof',
    'Lambda(WNAND_phi)<=4',
  ]) {
    if (!implication.assumptions?.includes(assumption)) {
      return validationReject0(
        ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesSATinP', 'assumptions'],
        'SAT-reduction source implication is missing a required assumption',
        { assumption, actual: implication.assumptions },
      );
    }
  }

  const baseline = decision.Baseline?.value;
  if (!Number.isInteger(baseline)
      || decision.LockedWord?.baseline !== baseline
      || decision.LockedWord?.fullWordSize !== baseline + 4
      || match.ChargeMap?.baseline !== baseline
      || match.ChargeMap?.fullWordSize !== baseline + 4
      || match.SlackMap?.lockedResidualSlackMax !== 4) {
    return validationReject0(
      ['PCCPack', 'FinalIntegration'],
      'SAT-reduction baseline, full-word size, or residual-slack bridge mismatch',
      {
        baseline,
        lockedWord: decision.LockedWord,
        chargeMap: match.ChargeMap,
        slackMap: match.SlackMap,
      },
    );
  }
  if (decision.NandConversion?.deterministic !== true
      || decision.NandConversion?.polynomial !== true
      || decision.NandConversion?.preservesSatisfiability !== true
      || decision.DecisionRule?.comparator !== 'minSize>baseline'
      || decision.DecisionRule?.usesExactMinimum !== true
      || decision.DecisionRule?.rejectsApproximateMinimum !== true) {
    return validationReject0(
      ['PCCPack', 'FinalIntegration', 'SATDecision'],
      'SAT decision record must bind deterministic conversion and the exact minSize>baseline comparator',
      { actual: decision },
    );
  }
  const satCase = decision.Cases?.find((entry) => entry.satisfiable === true);
  const unsatCase = decision.Cases?.find((entry) => entry.satisfiable === false);
  if (!isPlainObject0(satCase)
      || !isPlainObject0(unsatCase)
      || satCase.minSize <= baseline
      || satCase.decision !== 'SAT'
      || unsatCase.minSize !== baseline
      || unsatCase.decision !== 'UNSAT') {
    return validationReject0(
      ['PCCPack', 'FinalIntegration', 'SATDecision', 'Cases'],
      'SAT decision cases must witness the exact baseline comparison convention',
      { baseline, cases: decision.Cases },
    );
  }

  if (bounds.Converter?.polynomial !== true
      || bounds.LockedBuilder?.polynomial !== true
      || bounds.LockedBuilder?.residualSlackMax !== 4
      || bounds.Minimizer?.exact !== true
      || bounds.Minimizer?.polynomialWhenResidualSlackBounded !== true
      || bounds.Minimizer?.residualSlackBound !== 4
      || bounds.DecisionProcedure?.polynomial !== true
      || bounds.DecisionProcedure?.comparator !== 'minSize>baseline'
      || bounds.Bounds?.polynomial !== true
      || bounds.Bounds?.finite !== true
      || bounds.Bounds?.exponent !== 42) {
    return validationReject0(
      ['PCCPack', 'FinalIntegration', 'SATBounds'],
      'SAT bounds record must bind exact minimizer, residual slack four, and polynomial exponent 42',
      { actual: bounds },
    );
  }

  return validationAccept0({
    kind: 'GlobalFinalSATReductionSourceRecords0NF',
    baseline,
    fullWordSize: baseline + 4,
    residualSlackBound: 4,
    decisionComparator: 'minSize>baseline',
    minimizerExponent: bounds.Minimizer.exponent,
    finalPolynomialExponent: bounds.Bounds.exponent,
  });
}

async function runFinalIntegrationNegativeProbe0({ integration, probeName, mutate }) {
  const record = await CheckFinalIntegration0(mutate(integration));
  if (record.tag !== 'reject') {
    return validationReject0(
      ['PCCPack', 'FinalIntegration', 'negativeProbe', probeName],
      'SAT-reduction negative final-integration probe must reject',
      { actual: compactRecord0(record) },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionNegativeProbe0NF',
    probeName,
    coord: record.Coord ?? record.coord,
    path: record.Path ?? record.path,
    recordDigest: record.Digest ?? record.digest,
  });
}

function validatePackAlignment0(input) {
  const pack = input.PCCPack;
  const checks = [
    ['GlobalProofDAG', pack.GlobalProofDAG, input.LegacyGlobalProofDAG],
    ['RowPack', pack.RowPack, input.RowPack],
    ['LocalPackages', pack.LocalPackages, input.LocalPackages],
    ['RowFamG', pack.RowFamG, input.RowFamG],
    ['GPack', pack.GPack, input.RowFamG?.GPack],
    [
      'FinalIntegration.GlobalProofDAG',
      pack.FinalIntegration?.GlobalProofDAG,
      input.LegacyGlobalProofDAG,
    ],
    [
      'FinalIntegration.GPack',
      pack.FinalIntegration?.GPack,
      input.RowFamG?.GPack,
    ],
    [
      'FinalTheorem.FinalIntegration',
      pack.FinalTheorem?.FinalIntegration,
      pack.FinalIntegration,
    ],
    [
      'RowFamFinal.FinalTheorem',
      pack.RowFamFinal?.FinalTheorem,
      pack.FinalTheorem,
    ],
  ];
  for (const [name, actual, expected] of checks) {
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        ['PCCPack', ...name.split('.')],
        'SAT-reduction PCCPack surface must exactly align with the semantic predecessor inputs',
        {
          surface: name,
          expectedDigest: digestCanonical0(expected ?? null),
          actualDigest: digestCanonical0(actual ?? null),
        },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionPackAlignment0NF',
    alignedSurfaces: checks.map(([name]) => name),
  });
}

function validateSemanticSuite0(suite, dag, pack) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SATReductionSemanticDerivations'],
      'SAT-reduction semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'suiteId',
    'reductionBinding',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SATReductionSemanticDerivations', unexpected[0]],
      'SAT-reduction semantic suite rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalFinalSATReductionSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string') {
    return validationReject0(
      ['SATReductionSemanticDerivations'],
      'SAT-reduction semantic suite shape mismatch',
      { actual: suite },
    );
  }
  if (!sameCanonical0(suite.Scope, GLOBAL_FINAL_SAT_REDUCTION_SCOPE0)
      || !sameCanonical0(suite.Policy, GLOBAL_FINAL_SAT_REDUCTION_POLICY0)) {
    return validationReject0(
      ['SATReductionSemanticDerivations'],
      'SAT-reduction semantic suite scope or policy mismatch',
      { actualScope: suite.Scope, actualPolicy: suite.Policy },
    );
  }
  const expected = makeGlobalFinalSATReductionSemanticSuite0({
    LegacyGlobalProofDAG: dag,
    PCCPack: pack,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SATReductionSemanticDerivations'],
      'SAT-reduction semantic suite must exactly match the computed final-node, dependency, final-integration, and checker bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionSemanticSuite0NF',
    suiteId: suite.suiteId,
    nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    bindingDigest: suite.reductionBinding.bindingDigest,
    scopeDigest: digestCanonical0(suite.Scope),
    policyDigest: digestCanonical0(suite.Policy),
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
        ['FinalPrefixPredecessor', 'NF', field],
        'final-prefix predecessor boundary mismatch',
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
      ['FinalPrefixPredecessor', 'NF', 'semanticOverlay'],
      'final-prefix predecessor must keep the SAT reduction node blocked and expose no active final node',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        blockedFinalNodeIds: nf.semanticOverlay?.blockedFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionPredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'global SAT-reduction semantic input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalFinalSATReductionSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global SAT-reduction semantic input kind must be GlobalFinalSATReductionSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global SAT-reduction semantic input version must be ${CHECKER_VERSION}`,
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
    'Scope',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global SAT-reduction semantic input is missing a required field',
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
        'global SAT-reduction semantic dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global SAT-reduction semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'global SAT-reduction semantic input requires a global Nodes array',
    );
  }
  if (!sameCanonical0(input.Scope, GLOBAL_FINAL_SAT_REDUCTION_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'global SAT-reduction semantic scope must match the bounded fail-closed scope',
      { expected: GLOBAL_FINAL_SAT_REDUCTION_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_FINAL_SAT_REDUCTION_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global SAT-reduction semantic policy must match the fail-closed policy',
      { expected: GLOBAL_FINAL_SAT_REDUCTION_POLICY0, actual: input.Policy },
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
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global SAT-reduction semantic checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalSATReductionSemanticInputShape0NF',
  });
}

function isFinalIntegrationAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && record?.checker === 'CheckFinalIntegration0'
    && nf?.kind === 'FinalIntegration0NF';
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
