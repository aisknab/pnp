import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
  GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0,
} from './pcc-global-final-prefix-contract0.mjs';

const CHECKER_VERSION = 0;

export function buildFinalPrefixOverlay0({ dag, predecessorNF, prefixNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for final-prefix overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)
      || predecessorOverlay.globalPackageDerivationsReady !== true
      || predecessorOverlay.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'final-prefix successor requires the semantic package predecessor overlay',
      { actual: predecessorOverlay },
    );
  }
  if (!sameCanonical0(
    predecessorOverlay.blockedFinalNodeIds,
    GLOBAL_DAG_REQUIRED_FINALS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedFinalNodeIds'],
      'final-prefix predecessor must keep the exact complete final-node set blocked',
      {
        expected: [...GLOBAL_DAG_REQUIRED_FINALS0],
        actual: predecessorOverlay.blockedFinalNodeIds,
      },
    );
  }

  const refinementByNodeId = new Map(
    (prefixNF.finalPrefixRefinements ?? []).map((entry) => [
      entry.nodeId,
      entry,
    ]),
  );
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const semanticFinalPrefixBindings = [];
  for (const nodeId of GLOBAL_FINAL_PREFIX_NODE_IDS0) {
    const node = nodeById.get(nodeId);
    const refinement = refinementByNodeId.get(nodeId);
    if (!isPlainObject0(node) || node.nodeKind !== 'final') {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'finalPrefix', nodeId],
        'final-prefix overlay requires each prefix coordinate as a final node',
        { nodeId, actualKind: node?.nodeKind ?? null },
      );
    }
    if (!isPlainObject0(refinement) || refinement.ready !== true) {
      return validationReject0(
        ['FinalPrefixSemanticDerivations', 'NF', nodeId],
        'final-prefix overlay is missing a ready bounded refinement',
        { nodeId, actual: refinement },
      );
    }
    const nodeDigest = digestCanonical0(stripDigestFields0(node));
    if (!sameCanonical0(nodeDigest, refinement.globalNodeDigest)) {
      return validationReject0(
        ['FinalPrefixSemanticDerivations', 'NF', nodeId, 'globalNodeDigest'],
        'final-prefix refinement global-node digest mismatch',
        { nodeId, expected: nodeDigest, actual: refinement.globalNodeDigest },
      );
    }
    semanticFinalPrefixBindings.push(Object.freeze({
      nodeId,
      nodeKind: node.nodeKind,
      globalNodeDigest: nodeDigest,
      refinementDigest: refinement.refinementDigest,
      dependencyNodeId: refinement.dependencyNodeId,
      dependencyNodeDigest: refinement.dependencyNodeDigest,
      sourceRecordDigest: refinement.sourceRecordDigest,
      positiveRecordDigest: refinement.positiveRecordDigest,
      negativeRecordDigest: refinement.negativeRecordDigest,
      checkerContractDigest: refinement.checkerContractDigest,
      conclusionDigest: refinement.conclusionDigest,
      scope: GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0.scope,
      boundedExecutableFinalPrefixRefinement: true,
      unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
      publiclyActive: false,
    }));
  }

  const semanticFinalPrefixNodeIds = [...GLOBAL_FINAL_PREFIX_NODE_IDS0];
  const semanticNodeIds = [
    ...(predecessorOverlay.semanticNodeIds ?? []),
    ...semanticFinalPrefixNodeIds,
  ];
  const blockedFinalNodeIds = [...GLOBAL_FINAL_REMAINING_NODE_IDS0];
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticNodeIds.includes(node.id))
    .map((node) => node.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalPrefixOverlay0NF',
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

    semanticFinalPrefixNodeIds,
    semanticFinalPrefixBindings,
    blockedFinalNodeIds,
    blockedFinalImplicationNodeIds: [...GLOBAL_FINAL_REMAINING_NODE_IDS0],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticFinalPrefixNodeCount: semanticFinalPrefixNodeIds.length,
    blockedFinalNodeCount: blockedFinalNodeIds.length,
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
    globalFinalSATReductionDerivationReady: false,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutableFinalPrefixRefinementsOnly: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
    semanticallyRefinedFinalNodesRemainPubliclyQuarantined: true,
  });
}

export function makeFinalPrefixComputedGate0({
  predecessorRecord,
  predecessorNF,
  prefixRecord,
  overlay,
}) {
  const nodes = [
    makeGateNode0(
      'Gate.PredecessorPackages.DevelopmentAcceptance',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.PredecessorPackages.DevelopmentAcceptance'],
      true,
      predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.InfrastructureDerivations',
      ['Gate.PredecessorPackages.DevelopmentAcceptance'],
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
      prefixRecord.Digest ?? prefixRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalSATReductionDerivation',
      ['Gate.GlobalDAG.FinalPrefixRefinements'],
      false,
      digestCanonical0('Final.AcceptedPackageImpliesSATinP'),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.FinalComplexityImplication',
      ['Gate.GlobalDAG.FinalSATReductionDerivation'],
      false,
      digestCanonical0('Final.AcceptedPackageImpliesPEqualsNP'),
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
        finalPrefixRefinementsReady: true,
        satReductionDerivationReady: false,
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
      digest: prefixRecord.Digest ?? prefixRecord.digest,
      boundedExecutableFinalPrefixRefinementsOnly: true,
      unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalSATReductionDerivation',
      ready: false,
      reason: 'the accepted-package-to-SAT-in-P implication lacks an independent reduction and exact-minimizer soundness derivation',
      digest: digestCanonical0(overlay.blockedFinalImplicationNodeIds[0]),
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalComplexityImplication',
      ready: false,
      reason: 'the SAT-in-P-to-P-equals-NP implication remains quarantined until the SAT reduction predecessor is independently ready',
      digest: digestCanonical0(overlay.blockedFinalImplicationNodeIds[1]),
    }),
  ];

  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticFinalPrefixGate0',
    version: CHECKER_VERSION,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalFinalSATReductionDerivationReady: false,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutableFinalPrefixRefinementsOnly: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    semanticallyRefinedFinalNodeIds:
      Object.freeze([...GLOBAL_FINAL_PREFIX_NODE_IDS0]),
    remainingBlockedFinalNodeIds:
      Object.freeze([...GLOBAL_FINAL_REMAINING_NODE_IDS0]),
    requiredFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    semanticFinalPrefixNodesPubliclyActive: false,
    legacyFinalNodesStructurallyAccepted: true,
    legacyFinalNodesSemanticallyActive: false,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
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

function stripDigestFields0(value) {
  if (!isPlainObject0(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
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
