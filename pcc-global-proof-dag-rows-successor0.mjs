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
  GLOBAL_INFRASTRUCTURE_NODE_IDS0,
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  CheckGlobalRowsSemantic0,
  GLOBAL_ROW_SEMANTIC_NODE_IDS0,
  makeGlobalRowsSemanticInput0,
  makeGlobalRowsSemanticSuite0,
} from './pcc-global-rows-semantic0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_ROWS_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_ROWS_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticRowsReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorInfrastructureGateMustRemainDevelopmentOnly: true,
  predecessorInfrastructureCannotImplyRowReadiness: true,
  infrastructureDerivationsMustRemainReady: true,
  rowCoordinateContractsMustBeComputed: true,
  rowNodesBindSemanticCoordinateDigests: true,
  boundedGlobalRowCoordinateContractsOnly: true,
  unrestrictedRowTheoremSoundnessNotClaimed: true,
  rowTheoremDerivationsRemainSeparate: true,
  packageAndFinalNodesRemainQuarantined: true,
  finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_ROWS_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticRowsCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker:
    'CheckGlobalProofDAGInfrastructureSuccessor0',
  semanticRowsChecker: 'CheckGlobalRowsSemantic0',
});

export function makeGlobalProofDAGRowsSuccessor0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  RowSemanticDerivations = makeGlobalRowsSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_ROWS_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGRowsSuccessor0 Purpose must be one of ${GLOBAL_DAG_ROWS_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticRowsSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowSemanticDerivations,
    Binding: { ...GLOBAL_DAG_ROWS_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_ROWS_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGRowsSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGRowsSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGRowsFinalTheoremReadiness0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGRowsFinalTheoremReadiness0',
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
      reason: 'semantic global rows final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGRowsPurpose0NF',
    purpose,
  }));

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGInfrastructureSuccessor0',
    () => CheckGlobalProofDAGInfrastructureSuccessor0(
      makeGlobalProofDAGInfrastructureSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        Purpose: 'development',
      }),
    ),
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
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal`,
      path: ['PredecessorGlobal'],
      witness: {
        reason: 'global infrastructure predecessor rejected before row-coordinate upgrade',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorRecord = predecessorCall.record;
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

  const rowsCall = await callChecker0(
    'CheckGlobalRowsSemantic0',
    () => CheckGlobalRowsSemantic0(makeGlobalRowsSemanticInput0({
      KBundle: input.KBundle,
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      InfrastructureSemanticDerivations:
        input.InfrastructureSemanticDerivations,
      SemanticRows: input.RowSemanticDerivations,
    })),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalRowsSemantic0',
    rowsCall.ok && rowsCall.record.tag === 'accept',
    rowsCall.ok ? rowsCall.record : rowsCall.witness,
  ));
  if (!rowsCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticRows.exception`,
      path: ['RowSemanticDerivations'],
      witness: rowsCall.witness,
      ledger,
    });
  }
  if (rowsCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticRows`,
      path: ['RowSemanticDerivations'],
      witness: {
        reason: 'bounded global row-coordinate checker rejected',
        inner: compactRecord0(rowsCall.record),
      },
      ledger,
    });
  }
  const rowsRecord = rowsCall.record;
  const rowsNF = rowsRecord.NF ?? rowsRecord.nf ?? {};
  const rowsBoundary = validateRowsBoundary0(rowsNF);
  ledger.push(makeLedgerEntry0(
    'semanticRowsBoundary',
    rowsBoundary.ok,
    rowsBoundary.nf ?? rowsBoundary.witness,
  ));
  if (!rowsBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticRowsBoundary`,
      rowsBoundary,
      ledger,
    );
  }

  const overlay = buildRowsOverlay0({
    dag: input.LegacyGlobalProofDAG,
    predecessorNF,
    rowsNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticRowsOverlay',
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
    rowsRecord,
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
        reason: 'semantic global rows successor is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        boundedGlobalRowCoordinateContractsOnly: true,
        unrestrictedRowTheoremSoundnessNotClaimed: true,
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticRowsSuccessor0NF',
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
      predecessorGlobalRowCoordinateDerivationsReady: false,

      semanticKBundleFinalReady: predecessorNF.kBundleFinalReady === true,
      semanticK0ConformanceReady: predecessorNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: predecessorNF.semanticSigmaReady === true,
      semanticReflectionReady: predecessorNF.semanticReflectionReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,

      semanticRowsChecker: rowsRecord.checker,
      semanticRowsDigest: rowsRecord.Digest ?? rowsRecord.digest,
      globalRowCoordinateDerivationsReady: true,
      globalGenericRowFamilyCoordinateDerivationsReady: true,
      globalLockedNANDRowCoordinateDerivationsReady: true,
      globalRowCoordinates: rowsNF.globalRowCoordinates ?? [],
      globalRowCoordinateCount: rowsNF.globalRowCoordinateCount ?? null,
      globalGenericRowFamilyCount: rowsNF.globalGenericRowFamilyCount ?? null,
      globalLockedNANDRowCount: rowsNF.globalLockedNANDRowCount ?? null,
      globalRowDerivationDigests: rowsNF.rowDerivationDigests ?? [],
      boundedGlobalRowCoordinateContractsOnly: true,
      unrestrictedRowTheoremSoundnessNotClaimed: true,
      globalRowTheoremDerivationsReady: false,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'row-coordinate-semantic',

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

function buildRowsOverlay0({ dag, predecessorNF, rowsNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for row semantic overlay',
      { actual: typeof nodes },
    );
  }
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay)
      || predecessorOverlay.globalInfrastructureSemanticReady !== true
      || predecessorOverlay.globalRowDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'row successor requires the infrastructure semantic predecessor overlay',
      { actual: predecessorOverlay },
    );
  }
  if (!sameCanonical0(
    predecessorOverlay.semanticInfrastructureNodeIds,
    GLOBAL_INFRASTRUCTURE_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticInfrastructureNodeIds'],
      'row successor infrastructure-node set mismatch',
      {
        expected: [...GLOBAL_INFRASTRUCTURE_NODE_IDS0],
        actual: predecessorOverlay.semanticInfrastructureNodeIds,
      },
    );
  }

  const derivationByCoordinate = new Map(
    (rowsNF.rowDerivationDigests ?? []).map((entry) => [
      entry.coordinate,
      entry,
    ]),
  );
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const semanticRowBindings = [];
  for (const coordinate of GLOBAL_ROW_SEMANTIC_NODE_IDS0) {
    const node = nodeById.get(coordinate);
    const derivation = derivationByCoordinate.get(coordinate);
    if (node === undefined || derivation === undefined) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'row', coordinate],
        'row semantic overlay requires a checked node and derivation for every row coordinate',
        { coordinate, nodePresent: node !== undefined, derivationPresent: derivation !== undefined },
      );
    }
    const nodeDigest = digestCanonical0(stripDigestFields0(node));
    if (!sameCanonical0(nodeDigest, derivation.nodeDigest)) {
      return validationReject0(
        ['RowSemanticDerivations', coordinate, 'nodeDigest'],
        'row derivation node digest does not match the global row node',
        { coordinate, expected: nodeDigest, actual: derivation.nodeDigest },
      );
    }
    semanticRowBindings.push(Object.freeze({
      coordinate,
      nodeId: coordinate,
      nodeKind: node.nodeKind,
      nodeDigest,
      derivationDigest: derivation.digest,
      premiseDigest: derivation.premiseDigest,
      conclusionDigest: derivation.conclusionDigest,
      payloadDigest: derivation.payloadDigest,
      boundsDigest: derivation.boundsDigest,
      checkerContractDigest: derivation.checkerContractDigest,
      scope: 'bounded-global-row-coordinate-contract',
      unrestrictedRowTheoremSoundnessNotClaimed: true,
    }));
  }

  const semanticRowNodeIds = [...GLOBAL_ROW_SEMANTIC_NODE_IDS0];
  const semanticNodeIds = [
    ...(predecessorOverlay.semanticNodeIds ?? []),
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
    kind: 'GlobalProofDAGSemanticRowsOverlay0NF',
    semanticKBundleDigest: predecessorOverlay.semanticKBundleDigest ?? null,
    semanticKernelNodeIds: [...(predecessorOverlay.semanticKernelNodeIds ?? [])],
    blockedKernelNodeIds: [],
    semanticSigmaNodeIds: [...(predecessorOverlay.semanticSigmaNodeIds ?? [])],
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
    semanticRowNodeIds,
    blockedRowNodeIds: [],
    semanticRowBindings,
    blockedPackageNodeIds,
    blockedFinalNodeIds,
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],

    semanticRowNodeCount: semanticRowNodeIds.length,
    blockedRowNodeCount: 0,
    blockedPackageNodeCount: blockedPackageNodeIds.length,
    blockedFinalNodeCount: blockedFinalNodeIds.length,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,

    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowCoordinateDerivationsReady: true,
    boundedGlobalRowCoordinateContractsOnly: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
    globalRowTheoremDerivationsReady: false,
    globalPackageDerivationsReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
  });
}

function makeComputedGlobalGate0({
  predecessorRecord,
  predecessorNF,
  rowsRecord,
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
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.PredecessorInfrastructure.DevelopmentAcceptance'],
      true,
      predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.InfrastructureDerivations',
      ['Gate.PredecessorInfrastructure.DevelopmentAcceptance'],
      true,
      predecessorNF.globalInfrastructureSemanticDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.RowCoordinateContracts',
      ['Gate.GlobalDAG.InfrastructureDerivations'],
      true,
      rowsRecord.Digest ?? rowsRecord.digest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.RowTheoremDerivations',
      ['Gate.GlobalDAG.RowCoordinateContracts'],
      false,
      digestCanonical0({
        boundedCoordinateContractsReady: true,
        unrestrictedRowTheoremSoundnessNotClaimed: true,
      }),
    ),
    makeGateNode0(
      'Gate.GlobalDAG.PackageDerivations',
      [
        'Gate.GlobalDAG.InfrastructureDerivations',
        'Gate.GlobalDAG.RowTheoremDerivations',
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
    makeGateNode0(
      'Gate.GlobalDAG.SemanticNodeDerivations',
      [
        'Gate.GlobalDAG.InfrastructureDerivations',
        'Gate.GlobalDAG.RowTheoremDerivations',
        'Gate.GlobalDAG.PackageDerivations',
        'Gate.GlobalDAG.FinalDerivations',
      ],
      false,
      digestCanonical0({
        infrastructureReady: true,
        rowCoordinateContractsReady: true,
        rowTheoremDerivationsReady: false,
        packageDerivationsReady: false,
        finalDerivationsReady: false,
      }),
    ),
  ];
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
      digest: predecessorNF.semanticKBundleFinalProbeDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.InfrastructureDerivations',
      ready: true,
      reason: null,
      digest: predecessorNF.globalInfrastructureSemanticDigest ?? null,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.RowCoordinateContracts',
      ready: true,
      reason: null,
      digest: rowsRecord.Digest ?? rowsRecord.digest,
      boundedGlobalRowCoordinateContractsOnly: true,
      unrestrictedRowTheoremSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.RowTheoremDerivations',
      ready: false,
      reason: 'row coordinates are digest-bound, but underlying row theorem soundness has not been independently derived',
      digest: digestCanonical0(overlay.semanticRowBindings),
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
    kind: 'GlobalProofDAGComputedSemanticRowsGate0',
    version: CHECKER_VERSION,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowCoordinateDerivationsReady: true,
    boundedGlobalRowCoordinateContractsOnly: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
    globalRowTheoremDerivationsReady: false,
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
      'semantic global rows successor input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticRowsSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic global rows successor kind must be GlobalProofDAGSemanticRowsSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic global rows successor version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_ROWS_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic global rows successor Purpose is unsupported',
      { actual: input.Purpose },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowSemanticDerivations',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic global rows successor is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)
      || !isPlainObject0(input.LegacyGlobalProofDAG)
      || !isPlainObject0(input.InfrastructureSemanticDerivations)
      || !isPlainObject0(input.RowSemanticDerivations)) {
    return validationReject0(
      ['input'],
      'semantic global rows dependency surfaces must be objects',
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic global rows input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Binding, GLOBAL_DAG_ROWS_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic global rows checker binding mismatch',
      { expected: GLOBAL_DAG_ROWS_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_DAG_ROWS_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic global rows release policy must match the fail-closed policy',
      { expected: GLOBAL_DAG_ROWS_SUCCESSOR_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'Purpose',
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowSemanticDerivations',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic global rows successor rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticRowsSuccessorShape0NF',
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
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'global infrastructure predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(
    nf.semanticOverlay?.blockedRowNodeIds,
    GLOBAL_ROW_SEMANTIC_NODE_IDS0,
  )
      || nf.semanticOverlay?.globalRowDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedRowNodeIds'],
      'global infrastructure predecessor must keep every row coordinate blocked',
      {
        expected: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
        actual: nf.semanticOverlay?.blockedRowNodeIds,
      },
    );
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'global infrastructure predecessor must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGRowsPredecessorBoundary0NF',
    ...expected,
    blockedRowNodeIds: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
    activeFinalNodeIds: [],
  });
}

function validateRowsBoundary0(nf) {
  const expected = {
    globalRowCoordinateDerivationsReady: true,
    globalGenericRowFamilyCoordinateDerivationsReady: true,
    globalLockedNANDRowCoordinateDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    semanticKBundleFinalReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    boundedGlobalRowCoordinateContractsOnly: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
    globalRowTheoremDerivationsReady: false,
    globalPackageDerivationsReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['RowSemanticDerivations', 'NF', field],
        'bounded global row-coordinate readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(nf.globalRowCoordinates, GLOBAL_ROW_SEMANTIC_NODE_IDS0)) {
    return validationReject0(
      ['RowSemanticDerivations', 'NF', 'globalRowCoordinates'],
      'bounded global row-coordinate coverage mismatch',
      {
        expected: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
        actual: nf.globalRowCoordinates,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGRowsSemanticBoundary0NF',
    ...expected,
    globalRowCoordinates: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
