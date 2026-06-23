import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGInfrastructureSuccessor0,
  makeGlobalProofDAGInfrastructureSuccessor0,
} from './pcc-global-proof-dag-infrastructure-successor0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  CheckKBundleReflectionFinalTheoremReadiness0,
  CheckKBundleReflectionSuccessor0,
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  CheckGlobalRowSemantic0,
  GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0,
  GLOBAL_ROW_SEMANTIC_SCOPE0,
  makeGlobalRowSemanticInput0,
  makeGlobalRowSemanticSuite0,
} from './pcc-global-row-semantic0.mjs';

import {
  ROW_REQUIRED_FAMILIES0,
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  GLOBAL_INFRASTRUCTURE_NODE_IDS0,
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

export const GLOBAL_ROW_FAMILY_NODE_IDS0 = Object.freeze(
  ROW_REQUIRED_FAMILIES0.map((family) => `Row.${family}`),
);

export const GLOBAL_SEMANTIC_ROW_NODE_IDS0 = Object.freeze([
  ...GLOBAL_ROW_FAMILY_NODE_IDS0,
  ...GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0,
]);

export const GLOBAL_DAG_ROW_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_ROW_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticRowReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorInfrastructureGateMustRemainDevelopmentOnly: true,
  predecessorInfrastructureGateCannotImplyRowReadiness: true,
  reflectionKBundleFinalReadinessMustRemainReady: true,
  globalInfrastructureReadinessMustRemainReady: true,
  rowDerivationsMustBeComputed: true,
  rowNodesBindSemanticDerivationDigests: true,
  rowSchemaAndRouteRefinementOnly: true,
  mathematicalGovernedUniverseCompletenessNotClaimed: true,
  primitiveProofRuleSoundnessNotClaimedHere: true,
  packageAndFinalNodesRemainQuarantined: true,
  finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_ROW_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticRowCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker:
    'CheckGlobalProofDAGInfrastructureSuccessor0',
  semanticKBundleChecker: 'CheckKBundleReflectionSuccessor0',
  semanticKBundleFinalChecker:
    'CheckKBundleReflectionFinalTheoremReadiness0',
  semanticRowChecker: 'CheckGlobalRowSemantic0',
});

export function makeGlobalProofDAGRowSuccessor0({
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
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_ROW_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGRowSuccessor0 Purpose must be one of ${GLOBAL_DAG_ROW_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticRowSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    RowSemanticDerivations,
    Binding: { ...GLOBAL_DAG_ROW_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_ROW_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGRowSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGRowSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGRowFinalTheoremReadiness0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGRowFinalTheoremReadiness0',
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
      reason: 'semantic global row final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGRowPurpose0NF',
    purpose,
  }));

  const predecessorInput = makeGlobalProofDAGInfrastructureSuccessor0({
    KBundle: input.KBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      input.InfrastructureSemanticDerivations,
    Purpose: 'development',
  });
  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGInfrastructureSuccessor0',
    () => CheckGlobalProofDAGInfrastructureSuccessor0(predecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGInfrastructureSuccessor0',
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
        reason: 'semantic infrastructure predecessor global gate rejected before row upgrade',
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorInfrastructureBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorInfrastructureBoundary`,
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
  if (!bundleDevelopmentCall.ok
      || bundleDevelopmentCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle`,
      path: ['KBundle'],
      witness: {
        reason: 'semantic reflection development KBundle rejected during row upgrade',
        inner: bundleDevelopmentCall.ok
          ? compactRecord0(bundleDevelopmentCall.record)
          : bundleDevelopmentCall.witness,
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
  if (!bundleFinalCall.ok || !isFinalReadyAccept0(bundleFinalCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundleFinal`,
      path: ['KBundle'],
      witness: {
        reason: 'reflection KBundle final-readiness probe must remain accepted during row upgrade',
        inner: bundleFinalCall.ok
          ? compactRecord0(bundleFinalCall.record)
          : bundleFinalCall.witness,
      },
      ledger,
    });
  }

  const rowCall = await callChecker0(
    'CheckGlobalRowSemantic0',
    () => CheckGlobalRowSemantic0(makeGlobalRowSemanticInput0({
      KBundle: input.KBundle,
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      InfrastructureSemanticDerivations:
        input.InfrastructureSemanticDerivations,
      RowPack: input.RowPack,
      RowFamG: input.RowFamG,
      SemanticRows: input.RowSemanticDerivations,
    })),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalRowSemantic0',
    rowCall.ok && isRowSemanticAccept0(rowCall.record),
    rowCall.ok ? rowCall.record : rowCall.witness,
  ));
  if (!rowCall.ok || !isRowSemanticAccept0(rowCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticRows`,
      path: ['RowSemanticDerivations'],
      witness: {
        reason: 'semantic global row checker rejected',
        inner: rowCall.ok ? compactRecord0(rowCall.record) : rowCall.witness,
      },
      ledger,
    });
  }
  const rowRecord = rowCall.record;
  const rowNF = rowRecord.NF ?? rowRecord.nf ?? {};

  const overlay = buildRowOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    rowNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticRowOverlay',
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
    rowRecord,
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
        reason: 'semantic global row successor is not ready for final-theorem use',
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
      kind: 'GlobalProofDAGSemanticRowSuccessor0NF',
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
      predecessorGlobalInfrastructureReady: true,
      predecessorGlobalRowReady: false,

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
      globalInfrastructureSemanticReady: true,
      globalRowSemanticChecker: rowRecord.checker,
      globalRowSemanticDigest: rowRecord.Digest ?? rowRecord.digest,
      globalRowSemanticReady: true,
      globalRowDerivationsReady: true,
      globalRowNodeIds: rowNF.semanticGlobalRowNodeIds ?? [],
      globalRowDerivationDigests:
        rowNF.globalRowDerivationDigests ?? [],
      globalRowFamilyCount: rowNF.familyDerivationCount ?? null,
      globalLockedNANDProofRowCount:
        rowNF.lockedNANDProofRowDerivationCount ?? null,

      rowSchemaAndRouteRefinementOnly: true,
      Scope: { ...GLOBAL_ROW_SEMANTIC_SCOPE0 },
      mathematicalGovernedUniverseCompletenessNotClaimed: true,
      primitiveProofRuleSoundnessNotClaimedHere: true,
      packageTheoremSoundnessNotClaimedHere: true,
      finalTheoremSoundnessNotClaimedHere: true,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'row-semantic-refinement',

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

function buildRowOverlay0({ dag, predecessorNF, rowNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for row semantic overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'row successor requires predecessor infrastructure semantic overlay',
      { actual: predecessorOverlay },
    );
  }
  const expectedSets = [
    ['semanticKernelNodeIds', COMPLETE_KERNEL_NODE_IDS0],
    ['semanticSigmaNodeIds', SEMANTIC_SIGMA_NODE_IDS0],
    ['semanticReflectionNodeIds', SEMANTIC_REFLECTION_NODE_IDS0],
    ['semanticInfrastructureNodeIds', GLOBAL_INFRASTRUCTURE_NODE_IDS0],
  ];
  for (const [field, expected] of expectedSets) {
    if (!sameCanonical0(predecessorOverlay[field], expected)) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', 'semanticOverlay', field],
        'predecessor semantic-node set mismatch at row upgrade boundary',
        { field, expected, actual: predecessorOverlay[field] },
      );
    }
  }

  const derivationByNodeId = new Map();
  for (const entry of rowNF.familyDerivations ?? []) {
    derivationByNodeId.set(entry.nodeId, entry);
  }
  for (const entry of rowNF.lockedNANDProofRowDerivations ?? []) {
    derivationByNodeId.set(entry.nodeId, entry);
  }
  if (!sameCanonical0(
    [...derivationByNodeId.keys()],
    GLOBAL_SEMANTIC_ROW_NODE_IDS0,
  )) {
    return validationReject0(
      ['RowSemanticDerivations', 'NF', 'semanticGlobalRowNodeIds'],
      'semantic row checker must expose the exact required global row-node order',
      {
        expected: GLOBAL_SEMANTIC_ROW_NODE_IDS0,
        actual: [...derivationByNodeId.keys()],
      },
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const semanticRowBindings = [];
  for (const nodeId of GLOBAL_SEMANTIC_ROW_NODE_IDS0) {
    const node = nodeById.get(nodeId);
    const derivation = derivationByNodeId.get(nodeId);
    if (!isPlainObject0(node) || node.nodeKind !== 'row') {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'row', nodeId],
        'row semantic overlay requires every row coordinate as a row node',
        { nodeId, actualKind: node?.nodeKind ?? null },
      );
    }
    if (!isPlainObject0(derivation) || derivation.ready !== true) {
      return validationReject0(
        ['RowSemanticDerivations', 'NF', nodeId],
        'row semantic overlay is missing a ready derivation',
        { nodeId, actual: derivation },
      );
    }
    const nodeDigest = digestCanonical0(stripDigestFields0(node));
    if (!sameCanonical0(nodeDigest, derivation.globalNodeDigest)) {
      return validationReject0(
        ['RowSemanticDerivations', 'NF', nodeId, 'globalNodeDigest'],
        'row semantic derivation global-node digest mismatch',
        { nodeId, expected: nodeDigest, actual: derivation.globalNodeDigest },
      );
    }
    semanticRowBindings.push(Object.freeze({
      nodeId,
      nodeKind: node.nodeKind,
      family: derivation.family ?? null,
      rowKind: derivation.rowKind ?? null,
      globalNodeDigest: nodeDigest,
      derivationDigest: derivation.derivationDigest,
      executableRecordDigest:
        derivation.rowDigest ?? derivation.gProofNodeDigest ?? null,
      checkerContractDigest: derivation.checkerContractDigest,
      conclusionDigest: derivation.conclusionDigest,
      scope: GLOBAL_ROW_SEMANTIC_SCOPE0.scope,
      mathematicalGovernedUniverseCompletenessNotClaimed: true,
      primitiveProofRuleSoundnessNotClaimedHere: true,
    }));
  }

  const semanticKernelNodeIds = [...predecessorOverlay.semanticKernelNodeIds];
  const semanticSigmaNodeIds = [...predecessorOverlay.semanticSigmaNodeIds];
  const semanticReflectionNodeIds = [
    ...predecessorOverlay.semanticReflectionNodeIds,
  ];
  const semanticInfrastructureNodeIds = [
    ...predecessorOverlay.semanticInfrastructureNodeIds,
  ];
  const semanticRowNodeIds = [...GLOBAL_SEMANTIC_ROW_NODE_IDS0];
  const semanticNodeIds = [
    ...semanticKernelNodeIds,
    ...semanticSigmaNodeIds,
    ...semanticReflectionNodeIds,
    ...semanticInfrastructureNodeIds,
    ...semanticRowNodeIds,
  ];
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
    kind: 'GlobalProofDAGSemanticRowOverlay0NF',
    semanticKBundleDigest: rowNF.semanticKBundleFinalDigest ?? null,
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
    semanticInfrastructureBindings:
      predecessorOverlay.semanticInfrastructureBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticRowFamilyNodeIds: [...GLOBAL_ROW_FAMILY_NODE_IDS0],
    semanticLockedNANDProofRowNodeIds:
      [...GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0],
    semanticRowNodeIds,
    blockedRowNodeIds: [],
    semanticRowBindings,
    blockedPackageNodeIds,
    blockedFinalNodeIds,
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticKernelNodeCount: semanticKernelNodeIds.length,
    semanticSigmaNodeCount: semanticSigmaNodeIds.length,
    semanticReflectionNodeCount: semanticReflectionNodeIds.length,
    semanticInfrastructureNodeCount: semanticInfrastructureNodeIds.length,
    semanticRowFamilyNodeCount: GLOBAL_ROW_FAMILY_NODE_IDS0.length,
    semanticLockedNANDProofRowNodeCount:
      GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0.length,
    semanticRowNodeCount: semanticRowNodeIds.length,
    blockedPackageNodeCount: blockedPackageNodeIds.length,
    blockedFinalNodeCount: blockedFinalNodeIds.length,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,

    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    rowSchemaAndRouteRefinementOnly: true,
    mathematicalGovernedUniverseCompletenessNotClaimed: true,
    primitiveProofRuleSoundnessNotClaimedHere: true,
    packageAndFinalDerivationsRemainSeparate: true,
  });
}

function makeComputedGlobalGate0({
  predecessorRecord,
  predecessorNF,
  bundleDevelopmentRecord,
  bundleDevelopmentNF,
  bundleFinalRecord,
  rowRecord,
  overlay,
}) {
  const nodes = [
    makeGateNode0(
      'Gate.PredecessorInfrastructure.DevelopmentAcceptance',
      [],
      true,
      predecessorRecord.Digest ?? predecessorRecord.digest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionDevelopmentAcceptance',
      ['Gate.PredecessorInfrastructure.DevelopmentAcceptance'],
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
      'Gate.GlobalDAG.InfrastructureDerivations',
      ['Gate.PredecessorInfrastructure.DevelopmentAcceptance'],
      predecessorNF.globalInfrastructureSemanticReady === true,
      predecessorNF.globalInfrastructureSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.RowDerivations',
      [
        'Gate.KBundle.ReflectionFinalReadiness',
        'Gate.GlobalDAG.InfrastructureDerivations',
      ],
      overlay.globalRowDerivationsReady === true,
      rowRecord.Digest ?? rowRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.PackageDerivations',
      ['Gate.GlobalDAG.RowDerivations'],
      false,
      digestCanonical0(overlay.blockedPackageNodeIds),
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
        packageReady: false,
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
      digest: bundleFinalRecord.Digest ?? bundleFinalRecord.digest,
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
      digest: rowRecord.Digest ?? rowRecord.digest,
      scope: GLOBAL_ROW_SEMANTIC_SCOPE0.scope,
      mathematicalGovernedUniverseCompletenessNotClaimed: true,
      primitiveProofRuleSoundnessNotClaimedHere: true,
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
    kind: 'GlobalProofDAGComputedSemanticRowGate0',
    version: CHECKER_VERSION,
    semanticKBundleComputedReadinessDigest:
      bundleDevelopmentNF.computedReadinessDigest ?? null,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    rowSchemaAndRouteRefinementOnly: true,
    mathematicalGovernedUniverseCompletenessNotClaimed: true,
    primitiveProofRuleSoundnessNotClaimedHere: true,
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
    return validationReject0([], 'semantic global row successor input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalProofDAGSemanticRowSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic global row successor kind must be GlobalProofDAGSemanticRowSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic global row successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_ROW_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic global row successor Purpose is unsupported',
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
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic global row successor is missing a required field',
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
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'semantic global row dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic global row input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Binding, GLOBAL_DAG_ROW_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic global row checker binding mismatch',
      { expected: GLOBAL_DAG_ROW_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_DAG_ROW_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic global row release policy must match the fail-closed policy',
      { expected: GLOBAL_DAG_ROW_SUCCESSOR_POLICY0, actual: input.Policy },
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
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic global row successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticRowSuccessorShape0NF',
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
    globalInfrastructureSemanticReady: true,
    legacyGlobalDAGAccepted: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic infrastructure predecessor global boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'semantic infrastructure predecessor must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  if (nf.semanticOverlay?.globalRowDerivationsReady !== false
      || nf.semanticOverlay?.globalPackageDerivationsReady !== false
      || nf.semanticOverlay?.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic infrastructure predecessor must keep row, package, and final derivations blocked',
      { actual: nf.semanticOverlay },
    );
  }
  for (const nodeId of GLOBAL_SEMANTIC_ROW_NODE_IDS0) {
    if (!nf.semanticOverlay?.blockedRowNodeIds?.includes(nodeId)) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedRowNodeIds'],
        'semantic infrastructure predecessor must keep every phase-35 row coordinate blocked',
        { nodeId, actual: nf.semanticOverlay?.blockedRowNodeIds },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalProofDAGRowPredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
    rowCoordinatesBlocked: true,
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
  if (!sameCanonical0(nf.computedReadiness?.blockerCoordinates, [])
      || nf.computedReadiness?.finalTheoremReady !== true) {
    return validationReject0(
      ['KBundle', 'NF', 'computedReadiness'],
      'semantic reflection KBundle must retain no bundle-level blocker',
      { actual: nf.computedReadiness },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGRowKBundleBoundary0NF',
    ...expected,
    blockerCoordinates: [],
    computedBundleFinalReady: true,
  });
}

function isRowSemanticAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.globalRowSemanticReady === true
    && nf?.globalRowDerivationsReady === true
    && nf?.globalInfrastructureSemanticReady === true
    && nf?.globalPackageDerivationsReady === false
    && nf?.globalFinalDerivationsReady === false;
}

function isFinalReadyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true;
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
