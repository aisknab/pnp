import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  ROW_REQUIRED_FAMILIES0,
} from './pcc-rows0.mjs';

import {
  CheckGlobalProofDAGInfrastructureSuccessor0,
  makeGlobalProofDAGInfrastructureSuccessor0,
} from './pcc-global-proof-dag-infrastructure-successor0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_GENERIC_ROW_NODE_IDS0 = Object.freeze(
  ROW_REQUIRED_FAMILIES0.map((family) => `Row.${family}`),
);

export const GLOBAL_LOCKED_NAND_ROW_NODE_IDS0 = Object.freeze([
  'G.BaselineCert.proof',
  'G.TraceCert.proof',
  'G.ThresholdCert.proof',
]);

export const GLOBAL_ROW_SEMANTIC_NODE_IDS0 = Object.freeze([
  ...GLOBAL_GENERIC_ROW_NODE_IDS0,
  ...GLOBAL_LOCKED_NAND_ROW_NODE_IDS0,
]);

export const GLOBAL_ROW_SEMANTIC_POLICY0 = Object.freeze({
  kind: 'GlobalRowSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresInfrastructureSuccessorAcceptance: true,
  requiresReflectionKBundleFinalReadiness: true,
  oneBindingPerRequiredRowCoordinate: true,
  bindsEveryRowToGlobalNodeDigest: true,
  bindsEveryRowToPremiseDigest: true,
  bindsEveryRowToConclusionDigest: true,
  bindsEveryRowToPayloadDigest: true,
  bindsEveryRowToBoundsDigest: true,
  bindsEveryRowToExecutableContractDigest: true,
  exactGenericRowContractRequired: true,
  exactLockedNANDRowContractRequired: true,
  lockedNANDDependencyChainRecomputed: true,
  callerReadinessAssertionsForbidden: true,
  boundedGlobalRowCoordinateContractsOnly: true,
  unrestrictedRowTheoremSoundnessNotClaimed: true,
  packageAndFinalDerivationsRemainSeparate: true,
});

const GENERIC_ROW_CONTRACT0 = Object.freeze({
  kind: 'GlobalRowCheckerContract0',
  version: CHECKER_VERSION,
  contractClass: 'generic-row-family',
  nodeKind: 'row',
  premises: Object.freeze(['K.Record', 'K.Transport']),
  conclusionTag: 'RowFamilyAccepted0',
  mode: 'Full',
  imports: Object.freeze([]),
  payload: Object.freeze({}),
  semanticChecker: 'CheckGlobalGenericRowCoordinate0',
  scope: 'bounded-global-row-coordinate-contract',
  unrestrictedRowTheoremSoundnessNotClaimed: true,
});

export const GLOBAL_LOCKED_NAND_ROW_CONTRACTS0 = Object.freeze({
  'G.BaselineCert.proof': Object.freeze({
    kind: 'GlobalRowCheckerContract0',
    version: CHECKER_VERSION,
    contractClass: 'locked-nand-baseline',
    nodeKind: 'row',
    label: 'G.BaselineCert.proof',
    premises: Object.freeze(['K.Record', 'K.DAGInd']),
    conclusion: Object.freeze({
      tag: 'GProofNodeAccepted0',
      rowKind: 'BaselineCert',
      theorem: 'BaselineDistinct',
      proofRef: Object.freeze({
        kind: 'ProofRef0',
        refKind: 'KPrimitive',
        id: 'G.BaselineCert.proof',
      }),
    }),
    payload: Object.freeze({
      package: 'G',
      rule: 'BaselineDistinctDirectWire0',
      derivationKind: 'BaselineDerivation0',
      directWireOutputConvention: true,
      lowerBoundRuleApplied: true,
      transparentProof: true,
    }),
    bounds: Object.freeze({ polynomial: true, exponent: 4 }),
    mode: 'Full',
    imports: Object.freeze([]),
    semanticChecker: 'CheckGlobalLockedNANDBaselineCoordinate0',
    scope: 'bounded-global-row-coordinate-contract',
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  }),
  'G.TraceCert.proof': Object.freeze({
    kind: 'GlobalRowCheckerContract0',
    version: CHECKER_VERSION,
    contractClass: 'locked-nand-trace',
    nodeKind: 'row',
    label: 'G.TraceCert.proof',
    premises: Object.freeze(['K.Record', 'K.TraceInd']),
    conclusion: Object.freeze({
      tag: 'GProofNodeAccepted0',
      rowKind: 'TraceCert',
      theorem: 'TraceCoherence',
      proofRef: Object.freeze({
        kind: 'ProofRef0',
        refKind: 'KPrimitive',
        id: 'G.TraceCert.proof',
      }),
    }),
    payload: Object.freeze({
      package: 'G',
      rule: 'NANDTraceCoherence0',
      derivationKind: 'TraceDerivation0',
      topologicalInduction: true,
      traceCoherent: true,
      transparentProof: true,
    }),
    bounds: Object.freeze({ polynomial: true, exponent: 4 }),
    mode: 'Full',
    imports: Object.freeze([]),
    semanticChecker: 'CheckGlobalLockedNANDTraceCoordinate0',
    scope: 'bounded-global-row-coordinate-contract',
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  }),
  'G.ThresholdCert.proof': Object.freeze({
    kind: 'GlobalRowCheckerContract0',
    version: CHECKER_VERSION,
    contractClass: 'locked-nand-threshold',
    nodeKind: 'row',
    label: 'G.ThresholdCert.proof',
    premises: Object.freeze([
      'G.BaselineCert.proof',
      'G.TraceCert.proof',
      'K.IntArith',
    ]),
    conclusion: Object.freeze({
      tag: 'GProofNodeAccepted0',
      rowKind: 'ThresholdCert',
      theorem: 'LockedNANDThreshold',
      proofRef: Object.freeze({
        kind: 'ProofRef0',
        refKind: 'KPrimitive',
        id: 'G.ThresholdCert.proof',
      }),
    }),
    payload: Object.freeze({
      package: 'G',
      rule: 'LockedNANDThreshold0',
      derivationKind: 'ThresholdDerivation0',
      baselineDerivation: 'G.BaselineCert.proof',
      traceDerivation: 'G.TraceCert.proof',
      residualSlackMax: 4,
      satIffMinAboveBaseline: true,
      unsatMinEqualsBaseline: true,
      finalOutputGates: 4,
      transparentProof: true,
    }),
    bounds: Object.freeze({ polynomial: true, exponent: 4 }),
    mode: 'Full',
    imports: Object.freeze([]),
    semanticChecker: 'CheckGlobalLockedNANDThresholdCoordinate0',
    scope: 'bounded-global-row-coordinate-contract',
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  }),
});

export function makeGlobalRowsSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  return Object.freeze({
    kind: 'GlobalRowsSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.rows.semantic-coordinate-contracts0',
    bindings: Object.freeze(
      GLOBAL_ROW_SEMANTIC_NODE_IDS0.map((coordinate, index) => {
        const node = nodeById.get(coordinate) ?? null;
        const contract = contractForCoordinate0(coordinate);
        return makeRowBinding0({
          index,
          coordinate,
          node,
          contract,
        });
      }),
    ),
    Policy: { ...GLOBAL_ROW_SEMANTIC_POLICY0 },
  });
}

export function makeGlobalRowsSemanticInput0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  SemanticRows = makeGlobalRowsSemanticSuite0({ LegacyGlobalProofDAG }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalRowsSemanticInput0',
    version: CHECKER_VERSION,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    SemanticRows,
    Policy: { ...GLOBAL_ROW_SEMANTIC_POLICY0 },
  });
}

export async function CheckGlobalRowsSemantic0(input) {
  const checker = 'CheckGlobalRowsSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

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
      coord: `${checker}.predecessorInfrastructure.exception`,
      path: ['PredecessorInfrastructure'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorInfrastructure`,
      path: ['PredecessorInfrastructure'],
      witness: {
        reason: 'global infrastructure predecessor rejected before row-coordinate upgrade',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorNF =
    predecessorCall.record.NF ?? predecessorCall.record.nf ?? {};
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

  const suite = validateSemanticRowsSuite0(
    input.SemanticRows,
    input.LegacyGlobalProofDAG,
  );
  ledger.push(makeLedgerEntry0(
    'semanticRowsSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticRowsSuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const nodeIndexById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node, index) => [node.id, index]),
  );
  const derivations = [];
  for (let index = 0; index < GLOBAL_ROW_SEMANTIC_NODE_IDS0.length; index += 1) {
    const coordinate = GLOBAL_ROW_SEMANTIC_NODE_IDS0[index];
    const binding = input.SemanticRows.bindings[index];
    const node = nodeById.get(coordinate);
    const contract = contractForCoordinate0(coordinate);
    const checked = coordinate.startsWith('Row.')
      ? checkGenericRowCoordinate0({
          coordinate,
          node,
          binding,
          contract,
          dag: input.LegacyGlobalProofDAG,
          nodeIndexById,
        })
      : checkLockedNANDRowCoordinate0({
          coordinate,
          node,
          binding,
          contract,
          dag: input.LegacyGlobalProofDAG,
          nodeIndexById,
        });
    ledger.push(makeLedgerEntry0(
      `row.${coordinate}`,
      checked.ok,
      checked.nf ?? checked.witness,
    ));
    if (!checked.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.row.${safeCoord0(coordinate)}`,
        checked,
        ledger,
      );
    }
    derivations.push(checked.nf);
  }

  const genericDerivations = derivations.filter(
    (entry) => entry.coordinate.startsWith('Row.'),
  );
  const lockedNANDDerivations = derivations.filter(
    (entry) => entry.coordinate.startsWith('G.'),
  );

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalRowsSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalRowCoordinateDerivationsReady: true,
      globalGenericRowFamilyCoordinateDerivationsReady: true,
      globalLockedNANDRowCoordinateDerivationsReady: true,
      globalRowCoordinateCount: derivations.length,
      globalGenericRowFamilyCount: genericDerivations.length,
      globalLockedNANDRowCount: lockedNANDDerivations.length,
      globalRowCoordinates: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
      genericRowCoordinates: [...GLOBAL_GENERIC_ROW_NODE_IDS0],
      lockedNANDRowCoordinates: [...GLOBAL_LOCKED_NAND_ROW_NODE_IDS0],
      rowDerivations: derivations,
      rowDerivationDigests: derivations.map((entry) => ({
        coordinate: entry.coordinate,
        nodeId: entry.nodeId,
        digest: entry.derivationDigest,
        nodeDigest: entry.nodeDigest,
        premiseDigest: entry.premiseDigest,
        conclusionDigest: entry.conclusionDigest,
        payloadDigest: entry.payloadDigest,
        boundsDigest: entry.boundsDigest,
        checkerContractDigest: entry.checkerContractDigest,
      })),

      infrastructurePredecessorAccepted: true,
      infrastructurePredecessorChecker: predecessorCall.record.checker,
      infrastructurePredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalInfrastructureSemanticReady: true,
      semanticKBundleFinalReady: predecessorNF.kBundleFinalReady === true,
      semanticK0ConformanceReady: predecessorNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: predecessorNF.semanticSigmaReady === true,
      semanticReflectionReady: predecessorNF.semanticReflectionReady === true,

      boundedGlobalRowCoordinateContractsOnly: true,
      unrestrictedRowTheoremSoundnessNotClaimed: true,
      globalRowTheoremDerivationsReady: false,
      globalPackageDerivationsReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      packageAndFinalDerivationsRemainSeparate: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeRowBinding0({ index, coordinate, node, contract }) {
  const base = Object.freeze({
    kind: 'GlobalRowSemanticBinding0',
    version: CHECKER_VERSION,
    index,
    coordinate,
    nodeId: coordinate,
    nodeDigest: digestCanonical0(stripDigestFields0(node)),
    premiseDigest: digestCanonical0(node?.premises ?? null),
    conclusionDigest: digestCanonical0(node?.conclusion ?? null),
    payloadDigest: digestCanonical0(node?.payload ?? null),
    boundsDigest: digestCanonical0(node?.bounds ?? null),
    checkerContractDigest: digestCanonical0(contract),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function contractForCoordinate0(coordinate) {
  if (coordinate.startsWith('Row.')) {
    const family = coordinate.slice('Row.'.length);
    return Object.freeze({
      ...GENERIC_ROW_CONTRACT0,
      coordinate,
      label: family,
      conclusionFamily: family,
    });
  }
  return GLOBAL_LOCKED_NAND_ROW_CONTRACTS0[coordinate] ?? null;
}

function checkGenericRowCoordinate0({
  coordinate,
  node,
  binding,
  contract,
  dag,
  nodeIndexById,
}) {
  const family = coordinate.slice('Row.'.length);
  const base = checkRowNodeBase0({
    coordinate,
    node,
    contract,
    dag,
    nodeIndexById,
  });
  if (!base.ok) return base;
  if (node.label !== family) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'label'],
      'generic row-family node label must match its family coordinate',
      { expected: family, actual: node.label },
    );
  }
  if (node.conclusion?.tag !== 'RowFamilyAccepted0'
      || node.conclusion?.family !== family
      || Object.keys(node.conclusion).length !== 2) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'conclusion'],
      'generic row-family conclusion must exactly identify its family coordinate',
      { expected: { tag: 'RowFamilyAccepted0', family }, actual: node.conclusion },
    );
  }
  if (!sameCanonical0(node.payload, {})) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'payload'],
      'generic row-family coordinate rejects caller-supplied theorem or readiness payload fields',
      { actual: node.payload },
    );
  }

  const conclusion = Object.freeze({
    kind: 'GlobalRowCoordinateConclusion0',
    version: CHECKER_VERSION,
    coordinate,
    family,
    contractClass: 'generic-row-family',
    coordinateContractVerified: true,
    boundedGlobalRowCoordinateContract: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  });
  return makeRowDerivationAccept0({
    coordinate,
    binding,
    contract,
    node,
    detail: {
      kind: 'GlobalGenericRowCoordinate0NF',
      family,
      exactRecordTransportPremises: true,
      exactFamilyConclusion: true,
      emptyCallerPayload: true,
    },
    conclusion,
  });
}

function checkLockedNANDRowCoordinate0({
  coordinate,
  node,
  binding,
  contract,
  dag,
  nodeIndexById,
}) {
  const base = checkRowNodeBase0({
    coordinate,
    node,
    contract,
    dag,
    nodeIndexById,
  });
  if (!base.ok) return base;
  if (!sameCanonical0(node.label, contract.label)
      || !sameCanonical0(node.conclusion, contract.conclusion)
      || !sameCanonical0(node.payload, contract.payload)
      || !sameCanonical0(node.bounds, contract.bounds)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate],
      'locked-NAND row node must exactly match its bounded executable coordinate contract',
      {
        expected: {
          label: contract.label,
          conclusion: contract.conclusion,
          payload: contract.payload,
          bounds: contract.bounds,
        },
        actual: {
          label: node.label,
          conclusion: node.conclusion,
          payload: node.payload,
          bounds: node.bounds,
        },
      },
    );
  }

  let detail;
  if (coordinate === 'G.BaselineCert.proof') {
    detail = {
      kind: 'GlobalLockedNANDBaselineCoordinate0NF',
      directWireOutputConvention: true,
      lowerBoundRuleApplied: true,
      transparentProof: true,
      proofReferenceClosed: node.conclusion.proofRef.id === coordinate,
    };
  } else if (coordinate === 'G.TraceCert.proof') {
    detail = {
      kind: 'GlobalLockedNANDTraceCoordinate0NF',
      topologicalInduction: true,
      traceCoherent: true,
      transparentProof: true,
      proofReferenceClosed: node.conclusion.proofRef.id === coordinate,
    };
  } else {
    const payload = node.payload;
    if (payload.baselineDerivation !== 'G.BaselineCert.proof'
        || payload.traceDerivation !== 'G.TraceCert.proof'
        || payload.residualSlackMax !== payload.finalOutputGates
        || payload.residualSlackMax !== 4) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'payload'],
        'locked-NAND threshold coordinate must close the exact baseline/trace dependency and slack arithmetic',
        { actual: payload },
      );
    }
    detail = {
      kind: 'GlobalLockedNANDThresholdCoordinate0NF',
      baselineDependency: payload.baselineDerivation,
      traceDependency: payload.traceDerivation,
      residualSlackMax: payload.residualSlackMax,
      finalOutputGates: payload.finalOutputGates,
      residualSlackEqualsOutputGateBudget: true,
      satIffMinAboveBaseline: true,
      unsatMinEqualsBaseline: true,
      transparentProof: true,
      proofReferenceClosed: node.conclusion.proofRef.id === coordinate,
    };
  }

  const conclusion = Object.freeze({
    kind: 'GlobalRowCoordinateConclusion0',
    version: CHECKER_VERSION,
    coordinate,
    rowKind: node.conclusion.rowKind,
    theorem: node.conclusion.theorem,
    contractClass: contract.contractClass,
    coordinateContractVerified: true,
    boundedGlobalRowCoordinateContract: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  });
  return makeRowDerivationAccept0({
    coordinate,
    binding,
    contract,
    node,
    detail,
    conclusion,
  });
}

function checkRowNodeBase0({
  coordinate,
  node,
  contract,
  dag,
  nodeIndexById,
}) {
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate],
      'global row coordinate is missing its global proof node',
      { coordinate },
    );
  }
  if (node.id !== coordinate || node.nodeKind !== 'row') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate],
      'global row node id and kind must match its coordinate',
      { expectedId: coordinate, expectedKind: 'row', actual: node },
    );
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'premises'],
      'global row node premise list must exactly match its coordinate contract',
      { expected: contract.premises, actual: node.premises },
    );
  }
  const nodeIndex = nodeIndexById.get(coordinate);
  for (let index = 0; index < node.premises.length; index += 1) {
    const premise = node.premises[index];
    const premiseIndex = nodeIndexById.get(premise);
    if (!Number.isInteger(premiseIndex) || premiseIndex >= nodeIndex) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'premises', index],
        'global row premise must resolve to an earlier global node',
        { coordinate, premise, premiseIndex, nodeIndex },
      );
    }
  }
  if (!sameCanonical0(node.imports, contract.imports)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'imports'],
      'global row coordinate must not introduce undeclared imports',
      { expected: contract.imports, actual: node.imports },
    );
  }
  if (String(node.mode ?? 'Full').trim().toLowerCase() !== 'full') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'mode'],
      'global row coordinate derivation requires Full mode',
      { actual: node.mode },
    );
  }
  const bounds = node.bounds;
  const globalExponent = dag.BoundsLedger?.exponent;
  if (!isPlainObject0(bounds)
      || bounds.polynomial !== true
      || !Number.isInteger(bounds.exponent)
      || bounds.exponent <= 0
      || !Number.isInteger(globalExponent)
      || bounds.exponent > globalExponent) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'bounds'],
      'global row coordinate must carry a positive polynomial bound inside the global envelope',
      { globalExponent, actual: bounds },
    );
  }
  return validationAccept0({
    kind: 'GlobalRowNodeBase0NF',
    coordinate,
    nodeIndex,
    premiseCount: node.premises.length,
    exponent: bounds.exponent,
  });
}

function makeRowDerivationAccept0({
  coordinate,
  binding,
  contract,
  node,
  detail,
  conclusion,
}) {
  const nf = {
    kind: 'GlobalRowSemanticDerivation0NF',
    version: CHECKER_VERSION,
    coordinate,
    nodeId: coordinate,
    nodeDigest: binding.nodeDigest,
    premiseDigest: binding.premiseDigest,
    conclusionDigest: binding.conclusionDigest,
    payloadDigest: binding.payloadDigest,
    boundsDigest: binding.boundsDigest,
    checkerContractDigest: binding.checkerContractDigest,
    bindingDigest: binding.bindingDigest,
    semanticChecker: contract.semanticChecker,
    contractClass: contract.contractClass,
    mode: node.mode,
    exponent: node.bounds.exponent,
    detail,
    derivedConclusion: conclusion,
    derivedConclusionDigest: digestCanonical0(conclusion),
    coordinateContractReady: true,
    boundedGlobalRowCoordinateContract: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'global rows semantic input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalRowsSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global rows semantic input kind must be GlobalRowsSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global rows semantic input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'SemanticRows',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global rows semantic input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)
      || !isPlainObject0(input.LegacyGlobalProofDAG)
      || !isPlainObject0(input.InfrastructureSemanticDerivations)
      || !isPlainObject0(input.SemanticRows)) {
    return validationReject0(
      ['input'],
      'global rows semantic dependency surfaces must be objects',
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global rows semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_ROW_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global rows semantic policy must match the fail-closed policy',
      { expected: GLOBAL_ROW_SEMANTIC_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'SemanticRows',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global rows semantic checker rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'GlobalRowsSemanticInputShape0NF' });
}

function validateSemanticRowsSuite0(suite, dag) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticRows'],
      'global rows semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind', 'version', 'suiteId', 'bindings', 'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticRows', unexpected[0]],
      'global rows semantic suite rejects caller-supplied theorem or readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalRowsSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string'
      || suite.suiteId.length === 0) {
    return validationReject0(
      ['SemanticRows'],
      'global rows semantic suite kind, version, or suiteId is invalid',
      { actual: suite },
    );
  }
  if (!Array.isArray(suite.bindings)
      || suite.bindings.length !== GLOBAL_ROW_SEMANTIC_NODE_IDS0.length) {
    return validationReject0(
      ['SemanticRows', 'bindings'],
      'global rows semantic suite must provide exactly one binding per required row coordinate',
      {
        expected: GLOBAL_ROW_SEMANTIC_NODE_IDS0.length,
        actual: suite.bindings?.length,
      },
    );
  }
  if (!sameCanonical0(suite.Policy, GLOBAL_ROW_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['SemanticRows', 'Policy'],
      'global rows semantic suite policy mismatch',
      { expected: GLOBAL_ROW_SEMANTIC_POLICY0, actual: suite.Policy },
    );
  }

  const expected = makeGlobalRowsSemanticSuite0({
    LegacyGlobalProofDAG: dag,
  });
  for (let index = 0; index < GLOBAL_ROW_SEMANTIC_NODE_IDS0.length; index += 1) {
    if (!sameCanonical0(suite.bindings[index], expected.bindings[index])) {
      return validationReject0(
        ['SemanticRows', 'bindings', index],
        'global row binding must exactly match the computed node and executable coordinate contract',
        {
          coordinate: GLOBAL_ROW_SEMANTIC_NODE_IDS0[index],
          expected: expected.bindings[index],
          actual: suite.bindings[index],
        },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalRowsSemanticSuite0NF',
    suiteId: suite.suiteId,
    bindingCount: suite.bindings.length,
    coordinates: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
    bindingDigests: suite.bindings.map((entry) => entry.bindingDigest),
    policyDigest: digestCanonical0(suite.Policy),
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
        ['PredecessorInfrastructure', 'NF', field],
        'global infrastructure predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (nf.semanticOverlay?.globalRowDerivationsReady !== false
      || nf.semanticOverlay?.globalPackageDerivationsReady !== false
      || nf.semanticOverlay?.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorInfrastructure', 'NF', 'semanticOverlay'],
      'global infrastructure predecessor must keep row, package, and final derivations blocked',
      { actual: nf.semanticOverlay },
    );
  }
  if (!sameCanonical0(
    nf.semanticOverlay?.blockedRowNodeIds,
    GLOBAL_ROW_SEMANTIC_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorInfrastructure', 'NF', 'semanticOverlay', 'blockedRowNodeIds'],
      'global infrastructure predecessor row blocker set mismatch',
      {
        expected: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
        actual: nf.semanticOverlay?.blockedRowNodeIds,
      },
    );
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorInfrastructure', 'NF', 'activeFinalNodeIds'],
      'global infrastructure predecessor must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  return validationAccept0({
    kind: 'GlobalRowsInfrastructurePredecessorBoundary0NF',
    ...expected,
    blockedRowNodeIds: [...GLOBAL_ROW_SEMANTIC_NODE_IDS0],
    activeFinalNodeIds: [],
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

function safeCoord0(value) {
  return String(value).replace(/[^A-Za-z0-9_.-]/g, '_');
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
