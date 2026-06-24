import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGRowSuccessor0,
  GLOBAL_SEMANTIC_ROW_NODE_IDS0,
  makeGlobalProofDAGRowSuccessor0,
} from './pcc-global-proof-dag-row-successor0.mjs';

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
  CheckGlobalPackageSemantic0,
  GLOBAL_PACKAGE_NODE_IDS0,
  GLOBAL_PACKAGE_SEMANTIC_SCOPE0,
  makeGlobalPackageSemanticInput0,
  makeGlobalPackageSemanticSuite0,
} from './pcc-global-package-semantic0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_PACKAGE_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_PACKAGE_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticPackageReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorRowGateMustRemainDevelopmentOnly: true,
  predecessorRowGateCannotImplyPackageReadiness: true,
  semanticRowDerivationsMustRemainReady: true,
  packageRefinementsMustBeComputed: true,
  packageNodesBindSemanticRefinementDigests: true,
  boundedExecutablePackageRefinementsOnly: true,
  unrestrictedPackageTheoremSoundnessNotClaimed: true,
  finalNodesRemainQuarantined: true,
  finalTheoremRequiresSemanticFinalDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_PACKAGE_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticPackageCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGRowSuccessor0',
  semanticPackageChecker: 'CheckGlobalPackageSemantic0',
});

export function makeGlobalProofDAGPackageSuccessor0({
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
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_PACKAGE_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGPackageSuccessor0 Purpose must be one of ${GLOBAL_DAG_PACKAGE_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticPackageSuccessor0',
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
    Binding: { ...GLOBAL_DAG_PACKAGE_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_PACKAGE_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGPackageSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGPackageSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGPackageFinalTheoremReadiness0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGPackageFinalTheoremReadiness0',
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
      reason: 'semantic package global final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGPackagePurpose0NF',
    purpose,
  }));

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGRowSuccessor0',
    () => CheckGlobalProofDAGRowSuccessor0(
      makeGlobalProofDAGRowSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGRowSuccessor0',
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
        reason: 'semantic row predecessor global gate rejected before package upgrade',
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorRowBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorRowBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const packageCall = await callChecker0(
    'CheckGlobalPackageSemantic0',
    () => CheckGlobalPackageSemantic0(makeGlobalPackageSemanticInput0({
      KBundle: input.KBundle,
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      InfrastructureSemanticDerivations:
        input.InfrastructureSemanticDerivations,
      RowPack: input.RowPack,
      RowFamG: input.RowFamG,
      RowSemanticDerivations: input.RowSemanticDerivations,
      LocalPackages: input.LocalPackages,
      SemanticPackages: input.PackageSemanticDerivations,
    })),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalPackageSemantic0',
    packageCall.ok && packageCall.record.tag === 'accept',
    packageCall.ok ? packageCall.record : packageCall.witness,
  ));
  if (!packageCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticPackages.exception`,
      path: ['PackageSemanticDerivations'],
      witness: packageCall.witness,
      ledger,
    });
  }
  const packageRecord = packageCall.record;
  if (packageRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticPackages`,
      path: ['PackageSemanticDerivations'],
      witness: {
        reason: 'bounded semantic package refinement checker rejected',
        inner: compactRecord0(packageRecord),
      },
      ledger,
    });
  }
  const packageNF = packageRecord.NF ?? packageRecord.nf ?? {};
  const packageBoundary = validatePackageBoundary0(packageNF);
  ledger.push(makeLedgerEntry0(
    'semanticPackageBoundary',
    packageBoundary.ok,
    packageBoundary.nf ?? packageBoundary.witness,
  ));
  if (!packageBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticPackageBoundary`,
      packageBoundary,
      ledger,
    );
  }

  const overlay = buildPackageOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    packageNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticPackageOverlay',
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
    packageRecord,
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
        reason: 'semantic package global successor is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        boundedExecutablePackageRefinementsOnly: true,
        unrestrictedPackageTheoremSoundnessNotClaimed: true,
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticPackageSuccessor0NF',
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
      predecessorGlobalRowReady: true,
      predecessorGlobalPackageReady: false,

      semanticKBundleFinalReady: predecessorNF.kBundleFinalReady === true,
      semanticK0ConformanceReady:
        predecessorNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: predecessorNF.semanticSigmaReady === true,
      semanticReflectionReady: predecessorNF.semanticReflectionReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,
      globalRowDerivationsReady: predecessorNF.globalRowDerivationsReady === true,

      globalPackageSemanticChecker: packageRecord.checker,
      globalPackageSemanticDigest:
        packageRecord.Digest ?? packageRecord.digest,
      globalPackageSemanticReady: true,
      globalPackageDerivationsReady: true,
      globalPackageNodeIds: packageNF.globalPackageNodeIds ?? [],
      globalPackageRefinementCount:
        packageNF.globalPackageRefinementCount ?? null,
      globalPackageRefinementDigests:
        packageNF.packageRefinementDigests ?? [],
      boundedExecutablePackageRefinementsOnly: true,
      unrestrictedPackageTheoremSoundnessNotClaimed: true,
      finalTheoremSoundnessNotClaimedHere: true,
      Scope: { ...GLOBAL_PACKAGE_SEMANTIC_SCOPE0 },

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'package-semantic-refinement',

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
      finalTheoremRequiresSemanticFinalDerivations: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function buildPackageOverlay0({ dag, predecessorNF, packageNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for package semantic overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)
      || predecessorOverlay.globalRowDerivationsReady !== true
      || predecessorOverlay.globalPackageDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'package successor requires the semantic row predecessor overlay',
      { actual: predecessorOverlay },
    );
  }
  if (!sameCanonical0(
    predecessorOverlay.semanticRowNodeIds,
    GLOBAL_SEMANTIC_ROW_NODE_IDS0,
  )
      || !sameCanonical0(
        predecessorOverlay.blockedPackageNodeIds,
        GLOBAL_PACKAGE_NODE_IDS0,
      )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'package successor row-node or package-blocker set mismatch',
      {
        expectedRows: [...GLOBAL_SEMANTIC_ROW_NODE_IDS0],
        actualRows: predecessorOverlay.semanticRowNodeIds,
        expectedPackages: [...GLOBAL_PACKAGE_NODE_IDS0],
        actualPackages: predecessorOverlay.blockedPackageNodeIds,
      },
    );
  }

  const refinementByNodeId = new Map(
    (packageNF.packageRefinements ?? []).map((entry) => [
      entry.nodeId,
      entry,
    ]),
  );
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const semanticPackageBindings = [];
  for (const nodeId of GLOBAL_PACKAGE_NODE_IDS0) {
    const node = nodeById.get(nodeId);
    const refinement = refinementByNodeId.get(nodeId);
    if (!isPlainObject0(node) || node.nodeKind !== 'package') {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'package', nodeId],
        'package semantic overlay requires every package coordinate as a package node',
        { nodeId, actualKind: node?.nodeKind ?? null },
      );
    }
    if (!isPlainObject0(refinement) || refinement.ready !== true) {
      return validationReject0(
        ['PackageSemanticDerivations', 'NF', nodeId],
        'package semantic overlay is missing a ready refinement',
        { nodeId, actual: refinement },
      );
    }
    const nodeDigest = digestCanonical0(stripDigestFields0(node));
    if (!sameCanonical0(nodeDigest, refinement.globalNodeDigest)) {
      return validationReject0(
        ['PackageSemanticDerivations', 'NF', nodeId, 'globalNodeDigest'],
        'package semantic refinement global-node digest mismatch',
        { nodeId, expected: nodeDigest, actual: refinement.globalNodeDigest },
      );
    }
    semanticPackageBindings.push(Object.freeze({
      nodeId,
      nodeKind: node.nodeKind,
      family: refinement.family,
      theorem: refinement.theorem,
      globalNodeDigest: nodeDigest,
      refinementDigest: refinement.refinementDigest,
      localPackageDigest: refinement.localPackageDigest,
      rowDerivationDigest: refinement.rowDerivationDigest,
      positiveRecordDigest: refinement.positiveRecordDigest,
      negativeRecordDigest: refinement.negativeRecordDigest,
      checkerContractDigest: refinement.checkerContractDigest,
      conclusionDigest: refinement.conclusionDigest,
      scope: GLOBAL_PACKAGE_SEMANTIC_SCOPE0.scope,
      boundedExecutablePackageRefinement: true,
      unrestrictedPackageTheoremSoundnessNotClaimed: true,
    }));
  }

  const semanticPackageNodeIds = [...GLOBAL_PACKAGE_NODE_IDS0];
  const semanticNodeIds = [
    ...(predecessorOverlay.semanticNodeIds ?? []),
    ...semanticPackageNodeIds,
  ];
  const blockedFinalNodeIds = nodes
    .filter((node) => node.nodeKind === 'final')
    .map((node) => node.id);
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticNodeIds.includes(node.id))
    .map((node) => node.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticPackageOverlay0NF',
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
    semanticPackageNodeIds,
    blockedPackageNodeIds: [],
    semanticPackageBindings,
    blockedFinalNodeIds,
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticPackageNodeCount: semanticPackageNodeIds.length,
    blockedPackageNodeCount: 0,
    blockedFinalNodeCount: blockedFinalNodeIds.length,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,

    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: true,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutablePackageRefinementsOnly: true,
    unrestrictedPackageTheoremSoundnessNotClaimed: true,
    finalDerivationsRemainSeparate: true,
  });
}

function makeComputedGlobalGate0({
  predecessorRecord,
  predecessorNF,
  packageRecord,
  overlay,
}) {
  const nodes = [
    makeGateNode0(
      'Gate.PredecessorRows.DevelopmentAcceptance',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.PredecessorRows.DevelopmentAcceptance'],
      true,
      predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.InfrastructureDerivations',
      ['Gate.PredecessorRows.DevelopmentAcceptance'],
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
      packageRecord.Digest ?? packageRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalDerivations',
      ['Gate.GlobalDAG.PackageDerivations'],
      false,
      digestCanonical0(overlay.blockedFinalNodeIds),
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
      digest: packageRecord.Digest ?? packageRecord.digest,
      boundedExecutablePackageRefinementsOnly: true,
      unrestrictedPackageTheoremSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalDerivations',
      ready: false,
      reason: 'global final theorem nodes remain quarantined without independent semantic derivations',
      digest: digestCanonical0(overlay.blockedFinalNodeIds),
    }),
  ];

  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticPackageGate0',
    version: CHECKER_VERSION,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: true,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutablePackageRefinementsOnly: true,
    unrestrictedPackageTheoremSoundnessNotClaimed: true,
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
    return validationReject0([], 'semantic package global successor input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalProofDAGSemanticPackageSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic package global successor kind must be GlobalProofDAGSemanticPackageSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic package global successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_PACKAGE_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic package global successor Purpose is unsupported',
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
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic package global successor is missing a required field',
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
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'semantic package global successor dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic package global successor input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(
    input.Binding,
    GLOBAL_DAG_PACKAGE_SUCCESSOR_BINDING0,
  )) {
    return validationReject0(
      ['Binding'],
      'semantic package global successor checker binding mismatch',
      { expected: GLOBAL_DAG_PACKAGE_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(
    input.Policy,
    GLOBAL_DAG_PACKAGE_SUCCESSOR_POLICY0,
  )) {
    return validationReject0(
      ['Policy'],
      'semantic package global successor release policy must match the fail-closed policy',
      { expected: GLOBAL_DAG_PACKAGE_SUCCESSOR_POLICY0, actual: input.Policy },
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
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic package global successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticPackageSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    kBundleFinalReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowSemanticReady: true,
    globalRowDerivationsReady: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic row predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  const overlay = nf.semanticOverlay;
  if (!isPlainObject0(overlay)
      || overlay.globalRowDerivationsReady !== true
      || overlay.globalPackageDerivationsReady !== false
      || overlay.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic row predecessor readiness decomposition mismatch',
      { actual: overlay },
    );
  }
  if (!sameCanonical0(overlay.semanticRowNodeIds, GLOBAL_SEMANTIC_ROW_NODE_IDS0)
      || !sameCanonical0(overlay.blockedPackageNodeIds, GLOBAL_PACKAGE_NODE_IDS0)) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic row predecessor row-node or package-blocker set mismatch',
      {
        expectedRows: [...GLOBAL_SEMANTIC_ROW_NODE_IDS0],
        actualRows: overlay.semanticRowNodeIds,
        expectedPackages: [...GLOBAL_PACKAGE_NODE_IDS0],
        actualPackages: overlay.blockedPackageNodeIds,
      },
    );
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'semantic row predecessor must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGPackagePredecessorBoundary0NF',
    ...expected,
    blockedPackageNodeIds: [...GLOBAL_PACKAGE_NODE_IDS0],
    activeFinalNodeIds: [],
  });
}

function validatePackageBoundary0(nf) {
  const expected = {
    globalPackageSemanticReady: true,
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    semanticKBundleFinalReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    boundedExecutablePackageRefinementsOnly: true,
    unrestrictedPackageTheoremSoundnessNotClaimed: true,
    finalTheoremSoundnessNotClaimedHere: true,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PackageSemanticDerivations', 'NF', field],
        'bounded semantic package readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.globalPackageNodeIds, GLOBAL_PACKAGE_NODE_IDS0)) {
    return validationReject0(
      ['PackageSemanticDerivations', 'NF', 'globalPackageNodeIds'],
      'bounded semantic package node coverage mismatch',
      { expected: GLOBAL_PACKAGE_NODE_IDS0, actual: nf.globalPackageNodeIds },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGPackageSemanticBoundary0NF',
    ...expected,
    globalPackageNodeIds: [...GLOBAL_PACKAGE_NODE_IDS0],
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
