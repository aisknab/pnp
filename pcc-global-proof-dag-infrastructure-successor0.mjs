import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGReflectionSuccessor0,
  makeGlobalProofDAGReflectionSuccessor0,
} from './pcc-global-proof-dag-reflection-successor0.mjs';

import {
  CheckKBundleReflectionFinalTheoremReadiness0,
  CheckKBundleReflectionSuccessor0,
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  CheckGlobalInfrastructureSemantic0,
  GLOBAL_INFRASTRUCTURE_NODE_IDS0,
  makeGlobalInfrastructureSemanticInput0,
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  SEMANTIC_REFLECTION_REQUIRED_CHECKERS0,
} from './pcc-reflection-semantic0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

const CHECKER_VERSION = 0;

const COMPLETE_KERNEL_NODE_IDS0 = Object.freeze(
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.map((rule) => `K.${rule}`),
);

const SEMANTIC_SIGMA_NODE_IDS0 = Object.freeze([
  'Sigma.V53',
  'Sigma.V54',
]);

const SEMANTIC_REFLECTION_NODE_IDS0 = Object.freeze(
  SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.map(
    (checker) => `Reflection.${checker}`,
  ),
);

export const GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticInfrastructureReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorReflectionGateMustRemainDevelopmentOnly: true,
  predecessorReflectionGateCannotImplyInfrastructureReadiness: true,
  reflectionKBundleFinalReadinessMustRemainReady: true,
  infrastructureDerivationsMustBeComputed: true,
  infrastructureNodesBindSemanticDerivationDigests: true,
  rowPackageAndFinalNodesRemainQuarantined: true,
  globalFinalNodesQuarantinedUntilAllSemanticNodeFamiliesAccept: true,
  finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticInfrastructureCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGReflectionSuccessor0',
  semanticKBundleChecker: 'CheckKBundleReflectionSuccessor0',
  semanticKBundleFinalChecker:
    'CheckKBundleReflectionFinalTheoremReadiness0',
  semanticInfrastructureChecker: 'CheckGlobalInfrastructureSemantic0',
});

export function makeGlobalProofDAGInfrastructureSuccessor0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGInfrastructureSuccessor0 Purpose must be one of ${GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticInfrastructureSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    Binding: { ...GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGInfrastructureSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGInfrastructureSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGInfrastructureFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGInfrastructureFinalTheoremReadiness0',
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
      reason: 'semantic global infrastructure final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGInfrastructurePurpose0NF',
    purpose,
  }));

  const predecessorInput = makeGlobalProofDAGReflectionSuccessor0({
    KBundle: input.KBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    Purpose: 'development',
  });
  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGReflectionSuccessor0',
    () => CheckGlobalProofDAGReflectionSuccessor0(predecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGReflectionSuccessor0',
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
        reason: 'semantic reflection predecessor global gate rejected before infrastructure upgrade',
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorReflectionBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorReflectionBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const bundleDevelopmentCall = await callChecker0(
    'CheckKBundleReflectionSuccessor0',
    () => CheckKBundleReflectionSuccessor0({
      ...input.KBundle,
      Purpose: 'development',
    }),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleReflectionSuccessor0',
    bundleDevelopmentCall.ok
      && bundleDevelopmentCall.record.tag === 'accept',
    bundleDevelopmentCall.ok
      ? bundleDevelopmentCall.record
      : bundleDevelopmentCall.witness,
  ));
  if (!bundleDevelopmentCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle.exception`,
      path: ['KBundle'],
      witness: bundleDevelopmentCall.witness,
      ledger,
    });
  }
  if (bundleDevelopmentCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle`,
      path: ['KBundle'],
      witness: {
        reason: 'semantic reflection development KBundle rejected during infrastructure upgrade',
        inner: compactRecord0(bundleDevelopmentCall.record),
      },
      ledger,
    });
  }
  const bundleDevelopmentRecord = bundleDevelopmentCall.record;
  const bundleDevelopmentNF =
    bundleDevelopmentRecord.NF ?? bundleDevelopmentRecord.nf ?? {};
  const bundleBoundary = validateBundleDevelopmentBoundary0(
    bundleDevelopmentNF,
  );
  ledger.push(makeLedgerEntry0(
    'semanticKBundleDevelopmentBoundary',
    bundleBoundary.ok,
    bundleBoundary.nf ?? bundleBoundary.witness,
  ));
  if (!bundleBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticKBundleDevelopmentBoundary`,
      bundleBoundary,
      ledger,
    );
  }

  const bundleFinalCall = await callChecker0(
    'CheckKBundleReflectionFinalTheoremReadiness0',
    () => CheckKBundleReflectionFinalTheoremReadiness0({
      ...input.KBundle,
      Purpose: 'final-theorem',
    }),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleReflectionFinalTheoremReadiness0',
    bundleFinalCall.ok && isFinalReadyAccept0(bundleFinalCall.record),
    bundleFinalCall.ok ? bundleFinalCall.record : bundleFinalCall.witness,
  ));
  if (!bundleFinalCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundleFinal.exception`,
      path: ['KBundle'],
      witness: bundleFinalCall.witness,
      ledger,
    });
  }
  if (!isFinalReadyAccept0(bundleFinalCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundleFinal`,
      path: ['KBundle'],
      witness: {
        reason: 'reflection KBundle final-readiness probe must remain accepted',
        inner: compactRecord0(bundleFinalCall.record),
      },
      ledger,
    });
  }

  const infrastructureCall = await callChecker0(
    'CheckGlobalInfrastructureSemantic0',
    () => CheckGlobalInfrastructureSemantic0(
      makeGlobalInfrastructureSemanticInput0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        SemanticInfrastructure: input.InfrastructureSemanticDerivations,
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalInfrastructureSemantic0',
    infrastructureCall.ok && infrastructureCall.record.tag === 'accept',
    infrastructureCall.ok
      ? infrastructureCall.record
      : infrastructureCall.witness,
  ));
  if (!infrastructureCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticInfrastructure.exception`,
      path: ['InfrastructureSemanticDerivations'],
      witness: infrastructureCall.witness,
      ledger,
    });
  }
  const infrastructureRecord = infrastructureCall.record;
  if (infrastructureRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticInfrastructure`,
      path: ['InfrastructureSemanticDerivations'],
      witness: {
        reason: 'semantic global infrastructure checker rejected',
        inner: compactRecord0(infrastructureRecord),
      },
      ledger,
    });
  }
  const infrastructureNF =
    infrastructureRecord.NF ?? infrastructureRecord.nf ?? {};
  if (infrastructureNF.globalInfrastructureSemanticReady !== true
      || infrastructureNF.globalInfrastructureDerivationsReady !== true
      || !sameCanonical0(
        infrastructureNF.infrastructureCoordinates,
        GLOBAL_INFRASTRUCTURE_NODE_IDS0,
      )) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticInfrastructureBoundary`,
      path: ['InfrastructureSemanticDerivations'],
      witness: {
        reason: 'semantic global infrastructure readiness boundary mismatch',
        actual: infrastructureNF,
      },
      ledger,
    });
  }

  const overlay = buildInfrastructureOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    infrastructureNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticInfrastructureOverlay',
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

  const gate = makeComputedGlobalGate0({
    predecessorRecord,
    predecessorNF,
    bundleDevelopmentRecord,
    bundleDevelopmentNF,
    bundleFinalRecord: bundleFinalCall.record,
    infrastructureRecord,
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
        reason: 'semantic global infrastructure successor is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticInfrastructureSuccessor0NF',
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
      predecessorGlobalInfrastructureReady: false,

      semanticKBundleDevelopmentAccepted: true,
      semanticKBundleDevelopmentChecker: bundleDevelopmentRecord.checker,
      semanticKBundleDevelopmentDigest:
        bundleDevelopmentRecord.Digest ?? bundleDevelopmentRecord.digest,
      semanticKBundleDevelopmentOnly: true,
      semanticKBundlePublicTheoremEmissionAllowed: false,
      semanticKBundleComputedReadinessDigest:
        bundleDevelopmentNF.computedReadinessDigest ?? null,
      semanticKBundleFinalChecker: bundleFinalCall.record.checker,
      semanticKBundleFinalProbeAccepted: true,
      semanticKBundleFinalProbeDigest:
        bundleFinalCall.record.Digest ?? bundleFinalCall.record.digest,
      kBundleFinalReady: true,

      semanticK0ConformanceReady: true,
      semanticSigmaReady: true,
      semanticReflectionReady: true,
      globalInfrastructureSemanticChecker: infrastructureRecord.checker,
      globalInfrastructureSemanticDigest:
        infrastructureRecord.Digest ?? infrastructureRecord.digest,
      globalInfrastructureSemanticReady: true,
      globalInfrastructureCoordinates:
        infrastructureNF.infrastructureCoordinates ?? [],
      globalInfrastructureDerivationDigests:
        infrastructureNF.infrastructureDerivationDigests ?? [],

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'infrastructure-semantic',

      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),

      legacyFinalNodesStructurallyAccepted: true,
      legacyFinalNodesQuarantined: !finalTheoremReady,
      activeFinalNodeIds: finalTheoremReady
        ? [...gate.requiredFinalNodeIds]
        : [],
      quarantinedFinalNodeIds: finalTheoremReady
        ? []
        : [...gate.quarantinedFinalNodeIds],

      developmentOnly: !finalTheoremReady,
      finalTheoremReady,
      publicTheoremEmissionAllowed: finalTheoremReady,
      finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function buildInfrastructureOverlay0({ dag, predecessorNF, infrastructureNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for infrastructure semantic overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'infrastructure successor requires predecessor reflection semantic overlay',
      { actual: predecessorOverlay },
    );
  }
  if (!sameCanonical0(
    predecessorOverlay.semanticKernelNodeIds,
    COMPLETE_KERNEL_NODE_IDS0,
  )
      || !sameCanonical0(
        predecessorOverlay.semanticSigmaNodeIds,
        SEMANTIC_SIGMA_NODE_IDS0,
      )
      || !sameCanonical0(
        predecessorOverlay.semanticReflectionNodeIds,
        SEMANTIC_REFLECTION_NODE_IDS0,
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'predecessor semantic kernel, Sigma, or reflection node set mismatch',
      { actual: predecessorOverlay },
    );
  }

  const derivationByCoordinate = new Map(
    (infrastructureNF.infrastructureDerivationDigests ?? []).map((entry) => [
      entry.coordinate,
      entry,
    ]),
  );
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const semanticInfrastructureBindings = [];
  for (const coordinate of GLOBAL_INFRASTRUCTURE_NODE_IDS0) {
    const node = nodeById.get(coordinate);
    const derivation = derivationByCoordinate.get(coordinate);
    if (node === undefined || derivation === undefined) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'infrastructure', coordinate],
        'infrastructure overlay requires a checked node and derivation for every coordinate',
        { coordinate, nodePresent: node !== undefined, derivationPresent: derivation !== undefined },
      );
    }
    const nodeDigest = digestCanonical0(stripDigestFields0(node));
    if (!sameCanonical0(nodeDigest, derivation.nodeDigest)) {
      return validationReject0(
        ['InfrastructureSemanticDerivations', coordinate, 'nodeDigest'],
        'infrastructure derivation node digest does not match the global node',
        { coordinate, expected: nodeDigest, actual: derivation.nodeDigest },
      );
    }
    semanticInfrastructureBindings.push(Object.freeze({
      coordinate,
      nodeId: coordinate,
      nodeKind: node.nodeKind,
      nodeDigest,
      derivationDigest: derivation.digest,
      ledgerDigest: derivation.ledgerDigest,
      checkerContractDigest: derivation.checkerContractDigest,
      conclusionDigest: derivation.conclusionDigest,
    }));
  }

  const semanticKernelNodeIds = [...predecessorOverlay.semanticKernelNodeIds];
  const semanticSigmaNodeIds = [...predecessorOverlay.semanticSigmaNodeIds];
  const semanticReflectionNodeIds = [
    ...predecessorOverlay.semanticReflectionNodeIds,
  ];
  const semanticInfrastructureNodeIds = [
    ...GLOBAL_INFRASTRUCTURE_NODE_IDS0,
  ];
  const semanticNodeIds = [
    ...semanticKernelNodeIds,
    ...semanticSigmaNodeIds,
    ...semanticReflectionNodeIds,
    ...semanticInfrastructureNodeIds,
  ];
  const blockedRowNodeIds = nodes
    .filter((node) => node.nodeKind === 'row')
    .map((node) => node.id);
  const blockedPackageNodeIds = nodes
    .filter((node) => node.nodeKind === 'package')
    .map((node) => node.id);
  const blockedFinalNodeIds = nodes
    .filter((node) => node.nodeKind === 'final')
    .map((node) => node.id);
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticNodeIds.includes(node.id))
    .map((node) => node.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticInfrastructureOverlay0NF',
    semanticKBundleDigest:
      infrastructureNF.semanticKBundleFinalDigest ?? null,
    semanticKernelNodeIds,
    blockedKernelNodeIds: [],
    semanticSigmaNodeIds,
    blockedSigmaNodeIds: [],
    semanticSigmaBindings:
      predecessorOverlay.semanticSigmaBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticReflectionNodeIds,
    blockedReflectionNodeIds: [],
    semanticReflectionBindings:
      predecessorOverlay.semanticReflectionBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticInfrastructureNodeIds,
    blockedInfrastructureNodeIds: [],
    semanticInfrastructureBindings,
    blockedRowNodeIds,
    blockedPackageNodeIds,
    blockedFinalNodeIds,
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticKernelNodeCount: semanticKernelNodeIds.length,
    semanticSigmaNodeCount: semanticSigmaNodeIds.length,
    semanticReflectionNodeCount: semanticReflectionNodeIds.length,
    semanticInfrastructureNodeCount: semanticInfrastructureNodeIds.length,
    blockedRowNodeCount: blockedRowNodeIds.length,
    blockedPackageNodeCount: blockedPackageNodeIds.length,
    blockedFinalNodeCount: blockedFinalNodeIds.length,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,

    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: false,
    globalPackageDerivationsReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    rowPackageAndFinalDerivationsRemainSeparate: true,
  });
}

function makeComputedGlobalGate0({
  predecessorRecord,
  predecessorNF,
  bundleDevelopmentRecord,
  bundleDevelopmentNF,
  bundleFinalRecord,
  infrastructureRecord,
  overlay,
}) {
  const nodes = [
    makeGateNode0(
      'Gate.PredecessorReflection.DevelopmentAcceptance',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionDevelopmentAcceptance',
      ['Gate.PredecessorReflection.DevelopmentAcceptance'],
      true,
      bundleDevelopmentRecord.Digest ?? bundleDevelopmentRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.KBundle.ReflectionDevelopmentAcceptance'],
      true,
      bundleFinalRecord.Digest ?? bundleFinalRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.StructuralAcceptance',
      ['Gate.PredecessorReflection.DevelopmentAcceptance'],
      predecessorNF.legacyGlobalDAGAccepted === true,
      predecessorNF.legacyGlobalDAGDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.InfrastructureDerivations',
      [
        'Gate.KBundle.ReflectionFinalReadiness',
        'Gate.GlobalDAG.StructuralAcceptance',
      ],
      overlay.globalInfrastructureSemanticReady === true,
      infrastructureRecord.Digest ?? infrastructureRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.RowDerivations',
      ['Gate.GlobalDAG.InfrastructureDerivations'],
      false,
      digestCanonical0(overlay.blockedRowNodeIds),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.PackageDerivations',
      [
        'Gate.GlobalDAG.InfrastructureDerivations',
        'Gate.GlobalDAG.RowDerivations',
      ],
      false,
      digestCanonical0(overlay.blockedPackageNodeIds),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalDerivations',
      ['Gate.GlobalDAG.PackageDerivations'],
      false,
      digestCanonical0(overlay.blockedFinalNodeIds),
    ),
  ];
  const globalSemanticReady = false;
  nodes.push(makeGateNode0(
    'Gate.GlobalDAG.SemanticNodeDerivations',
    [
      'Gate.GlobalDAG.InfrastructureDerivations',
      'Gate.GlobalDAG.RowDerivations',
      'Gate.GlobalDAG.PackageDerivations',
      'Gate.GlobalDAG.FinalDerivations',
    ],
    globalSemanticReady,
    digestCanonical0({
      infrastructureReady: true,
      rowReady: false,
      packageReady: false,
      finalReady: false,
    }),
  ));
  nodes.push(makeGateNode0(
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
  ));

  const blockers = [
    Object.freeze({
      coordinate: 'KBundle.ReflectionFinalReadiness',
      ready: true,
      reason: null,
      digest: bundleFinalRecord.Digest ?? bundleFinalRecord.digest,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.InfrastructureDerivations',
      ready: true,
      reason: null,
      digest: infrastructureRecord.Digest ?? infrastructureRecord.digest,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.RowDerivations',
      ready: false,
      reason: 'global row-family and locked-NAND proof rows remain structural-only',
      digest: digestCanonical0(overlay.blockedRowNodeIds),
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.PackageDerivations',
      ready: false,
      reason: 'global package theorem nodes remain structural-only',
      digest: digestCanonical0(overlay.blockedPackageNodeIds),
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalDerivations',
      ready: false,
      reason: 'global final theorem nodes remain quarantined without semantic derivations',
      digest: digestCanonical0(overlay.blockedFinalNodeIds),
    }),
  ];
  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticInfrastructureGate0',
    version: CHECKER_VERSION,
    semanticKBundleComputedReadinessDigest:
      bundleDevelopmentNF.computedReadinessDigest ?? null,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: false,
    globalPackageDerivationsReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    requiredFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    legacyFinalNodesStructurallyAccepted: true,
    legacyFinalNodesSemanticallyActive: false,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'semantic global infrastructure successor input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticInfrastructureSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic global infrastructure successor kind must be GlobalProofDAGSemanticInfrastructureSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic global infrastructure successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic global infrastructure successor Purpose is unsupported',
      { actual: input.Purpose },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic global infrastructure successor is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)
      || !isPlainObject0(input.LegacyGlobalProofDAG)
      || !isPlainObject0(input.InfrastructureSemanticDerivations)) {
    return validationReject0(
      ['input'],
      'semantic global infrastructure dependency surfaces must be objects',
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic global infrastructure input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(
    input.Binding,
    GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_BINDING0,
  )) {
    return validationReject0(
      ['Binding'],
      'semantic global infrastructure checker binding mismatch',
      { expected: GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(
    input.Policy,
    GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_POLICY0,
  )) {
    return validationReject0(
      ['Policy'],
      'semantic global infrastructure release policy must match the fail-closed policy',
      { expected: GLOBAL_DAG_INFRASTRUCTURE_SUCCESSOR_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'Purpose',
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic global infrastructure successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticInfrastructureSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKBundleDevelopmentAccepted: true,
    semanticKBundleFinalProbeAccepted: true,
    kBundleFinalReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    legacyGlobalDAGAccepted: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic reflection predecessor global gate boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'semantic reflection predecessor must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  if (!sameCanonical0(
    nf.semanticOverlay?.semanticKernelNodeIds,
    COMPLETE_KERNEL_NODE_IDS0,
  )
      || !sameCanonical0(
        nf.semanticOverlay?.semanticSigmaNodeIds,
        SEMANTIC_SIGMA_NODE_IDS0,
      )
      || !sameCanonical0(
        nf.semanticOverlay?.semanticReflectionNodeIds,
        SEMANTIC_REFLECTION_NODE_IDS0,
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic reflection predecessor semantic-node set mismatch',
      { actual: nf.semanticOverlay },
    );
  }
  if (nf.semanticOverlay?.globalSemanticNodeDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'globalSemanticNodeDerivationsReady'],
      'semantic reflection predecessor must keep global semantic-node derivations blocked',
      { actual: nf.semanticOverlay?.globalSemanticNodeDerivationsReady },
    );
  }
  for (const coordinate of GLOBAL_INFRASTRUCTURE_NODE_IDS0) {
    if (!nf.semanticOverlay?.structuralOnlyNodeIds?.includes(coordinate)) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', 'semanticOverlay', 'structuralOnlyNodeIds'],
        'semantic reflection predecessor must keep infrastructure nodes structural-only',
        { coordinate, actual: nf.semanticOverlay?.structuralOnlyNodeIds },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalProofDAGInfrastructurePredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
    infrastructureCoordinatesStructuralOnly: true,
  });
}

function validateBundleDevelopmentBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKImplDevelopmentAccepted: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    semanticReflectionSoundnessSurfaceReady: true,
    legacyBundleAccepted: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['KBundle', 'NF', field],
        'semantic reflection KBundle development boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(
    nf.computedReadiness?.blockerCoordinates,
    [],
  )
      || nf.computedReadiness?.finalTheoremReady !== true) {
    return validationReject0(
      ['KBundle', 'NF', 'computedReadiness'],
      'semantic reflection KBundle must have no remaining bundle-level blocker',
      { actual: nf.computedReadiness },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGInfrastructureKBundleBoundary0NF',
    ...expected,
    blockerCoordinates: [],
    computedBundleFinalReady: true,
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

function isFinalReadyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true;
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
