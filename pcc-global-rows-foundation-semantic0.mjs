import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckBootBatch0,
  BOOT_BATCH0_REQUIRED_ROWS,
} from './pcc-boot0.mjs';

import {
  DigestObject0,
} from './pcc-core.mjs';

import {
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

import {
  CheckGPack0,
  CheckRowFamG0,
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGInfrastructureSuccessor0,
  makeGlobalProofDAGInfrastructureSuccessor0,
} from './pcc-global-proof-dag-infrastructure-successor0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FOUNDATION_ROW_FAMILIES0 = Object.freeze(
  BOOT_BATCH0_REQUIRED_ROWS.map((spec) => spec.family),
);

export const GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0 = Object.freeze([
  'G.BaselineCert.proof',
  'G.TraceCert.proof',
  'G.ThresholdCert.proof',
]);

export const GLOBAL_FOUNDATION_ROW_NODE_IDS0 = Object.freeze([
  ...GLOBAL_FOUNDATION_ROW_FAMILIES0.map((family) => `Row.${family}`),
  ...GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0,
]);

export const GLOBAL_FOUNDATION_ROWS_POLICY0 = Object.freeze({
  kind: 'GlobalFoundationRowsSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresInfrastructureSuccessorAcceptance: true,
  requiresBootstrapBatchAcceptance: true,
  requiresLockedNANDPackageAcceptance: true,
  requiresLockedNANDRowFamilyAcceptance: true,
  oneBindingPerBootstrapFamily: true,
  oneBindingPerLockedNANDProofRow: true,
  bindsEveryBootstrapRowToRowKeyAndHash: true,
  bindsEveryBootstrapRowToSemanticPrimitiveCoordinate: true,
  bindsEveryLockedNANDProofRowToPiGNodeAndCertificate: true,
  bindsEveryDerivationToGlobalNodeDigest: true,
  callerReadinessAssertionsForbidden: true,
  boundedExecutableRowBindingsOnly: true,
  unrestrictedRowTheoremSoundnessNotClaimed: true,
  remainingRowFamiliesRemainSeparate: true,
  packageAndFinalNodesRemainQuarantined: true,
});

export const GLOBAL_FOUNDATION_ROW_CONTRACTS0 = Object.freeze({
  bootstrap: Object.freeze({
    kind: 'GlobalFoundationBootstrapRowContract0',
    version: CHECKER_VERSION,
    semanticChecker: 'CheckBootBatch0',
    globalNodeKind: 'row',
    globalNodePremises: Object.freeze(['K.Record', 'K.Transport']),
    globalConclusionTag: 'RowFamilyAccepted0',
    selectedRoute: 'Accept',
    mode: 'Full',
  }),
  'G.BaselineCert.proof': Object.freeze({
    kind: 'GlobalFoundationLockedNANDProofContract0',
    version: CHECKER_VERSION,
    semanticChecker: 'CheckGPack0',
    rowKind: 'BaselineCert',
    theorem: 'BaselineDistinct',
    globalPremises: Object.freeze(['K.Record', 'K.DAGInd']),
    piGPremises: Object.freeze([]),
    rule: 'BaselineDistinctDirectWire0',
    derivationKind: 'BaselineDerivation0',
  }),
  'G.TraceCert.proof': Object.freeze({
    kind: 'GlobalFoundationLockedNANDProofContract0',
    version: CHECKER_VERSION,
    semanticChecker: 'CheckGPack0',
    rowKind: 'TraceCert',
    theorem: 'TraceCoherence',
    globalPremises: Object.freeze(['K.Record', 'K.TraceInd']),
    piGPremises: Object.freeze([]),
    rule: 'NANDTraceCoherence0',
    derivationKind: 'TraceDerivation0',
  }),
  'G.ThresholdCert.proof': Object.freeze({
    kind: 'GlobalFoundationLockedNANDProofContract0',
    version: CHECKER_VERSION,
    semanticChecker: 'CheckGPack0',
    rowKind: 'ThresholdCert',
    theorem: 'LockedNANDThreshold',
    globalPremises: Object.freeze([
      'G.BaselineCert.proof',
      'G.TraceCert.proof',
      'K.IntArith',
    ]),
    piGPremises: Object.freeze([
      'G.BaselineCert.proof',
      'G.TraceCert.proof',
    ]),
    rule: 'LockedNANDThreshold0',
    derivationKind: 'ThresholdDerivation0',
  }),
});

export function makeGlobalFoundationRowsSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  const rowByFamily = new Map(
    (RowPack?.Rows ?? [])
      .filter((row) => row?.BatchID === 'B0')
      .map((row) => [row?.FamilyID ?? row?.RowFamily, row]),
  );
  const piGNodeById = new Map(
    (getPiG0(RowFamG?.GPack)?.proofNodes ?? []).map((node) => [node?.id, node]),
  );

  const bootstrapBindings = BOOT_BATCH0_REQUIRED_ROWS.map((spec, index) =>
    makeBootstrapBinding0({
      index,
      spec,
      row: rowByFamily.get(spec.family) ?? null,
      node: nodeById.get(`Row.${spec.family}`) ?? null,
      kernelNode: nodeById.get(`K.${spec.proofRule}`) ?? null,
    }));

  const lockedNANDBindings = GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0.map(
    (nodeId, index) => makeLockedNANDBinding0({
      index,
      nodeId,
      node: nodeById.get(nodeId) ?? null,
      piGNode: piGNodeById.get(nodeId) ?? null,
      gpack: RowFamG?.GPack ?? null,
    }),
  );

  return Object.freeze({
    kind: 'GlobalFoundationRowsSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.foundation-rows.semantic0',
    bootstrapBindings: Object.freeze(bootstrapBindings),
    lockedNANDBindings: Object.freeze(lockedNANDBindings),
    Policy: { ...GLOBAL_FOUNDATION_ROWS_POLICY0 },
  });
}

export function makeGlobalFoundationRowsSemanticInput0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  SemanticFoundationRows = makeGlobalFoundationRowsSemanticSuite0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
  }),
} = {}) {
  return {
    kind: 'GlobalFoundationRowsSemanticInput0',
    version: CHECKER_VERSION,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    SemanticFoundationRows,
    Policy: { ...GLOBAL_FOUNDATION_ROWS_POLICY0 },
  };
}

export async function CheckGlobalFoundationRowsSemantic0(input) {
  const checker = 'CheckGlobalFoundationRowsSemantic0';
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
    predecessorCall.ok && isInfrastructureAccept0(predecessorCall.record),
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.infrastructurePredecessor.exception`,
      path: ['InfrastructureSemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (!isInfrastructureAccept0(predecessorCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.infrastructurePredecessor`,
      path: ['InfrastructureSemanticDerivations'],
      witness: {
        reason: 'foundation-row derivations require accepted global infrastructure semantics',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }

  const b0Rows = input.RowPack.Rows.filter((row) => row?.BatchID === 'B0');
  const bootCall = await callChecker0(
    'CheckBootBatch0',
    () => CheckBootBatch0(b0Rows),
  );
  ledger.push(makeLedgerEntry0(
    'CheckBootBatch0',
    bootCall.ok && bootCall.record.tag === 'accept',
    bootCall.ok ? bootCall.record : bootCall.witness,
  ));
  if (!bootCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.bootBatch.exception`,
      path: ['RowPack', 'Rows'],
      witness: bootCall.witness,
      ledger,
    });
  }
  if (bootCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.bootBatch`,
      path: ['RowPack', 'Rows'],
      witness: {
        reason: 'foundation-row derivations require accepted bootstrap row coverage',
        inner: compactRecord0(bootCall.record),
      },
      ledger,
    });
  }

  const gpackCall = await callChecker0(
    'CheckGPack0',
    () => CheckGPack0(input.RowFamG.GPack),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGPack0',
    gpackCall.ok && gpackCall.record.tag === 'accept',
    gpackCall.ok ? gpackCall.record : gpackCall.witness,
  ));
  if (!gpackCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.lockedNANDPackage.exception`,
      path: ['RowFamG', 'GPack'],
      witness: gpackCall.witness,
      ledger,
    });
  }
  if (gpackCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.lockedNANDPackage`,
      path: ['RowFamG', 'GPack'],
      witness: {
        reason: 'foundation-row derivations require an accepted locked-NAND package',
        inner: compactRecord0(gpackCall.record),
      },
      ledger,
    });
  }

  const rowFamGCall = await callChecker0(
    'CheckRowFamG0',
    () => CheckRowFamG0(input.RowFamG),
  );
  ledger.push(makeLedgerEntry0(
    'CheckRowFamG0',
    rowFamGCall.ok && rowFamGCall.record.tag === 'accept',
    rowFamGCall.ok ? rowFamGCall.record : rowFamGCall.witness,
  ));
  if (!rowFamGCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.lockedNANDRows.exception`,
      path: ['RowFamG'],
      witness: rowFamGCall.witness,
      ledger,
    });
  }
  if (rowFamGCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.lockedNANDRows`,
      path: ['RowFamG'],
      witness: {
        reason: 'foundation-row derivations require accepted locked-NAND row-family coverage',
        inner: compactRecord0(rowFamGCall.record),
      },
      ledger,
    });
  }

  const suite = validateSemanticSuite0(
    input.SemanticFoundationRows,
    input.LegacyGlobalProofDAG,
    input.RowPack,
    input.RowFamG,
  );
  ledger.push(makeLedgerEntry0(
    'semanticFoundationRowsSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticFoundationRowsSuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const rowByFamily = new Map(
    b0Rows.map((row) => [row.FamilyID ?? row.RowFamily, row]),
  );
  const piGNodeById = new Map(
    (getPiG0(input.RowFamG.GPack)?.proofNodes ?? [])
      .map((node) => [node.id, node]),
  );

  const bootstrapDerivations = [];
  for (let index = 0; index < BOOT_BATCH0_REQUIRED_ROWS.length; index += 1) {
    const spec = BOOT_BATCH0_REQUIRED_ROWS[index];
    const result = checkBootstrapRow0({
      index,
      spec,
      binding: input.SemanticFoundationRows.bootstrapBindings[index],
      row: rowByFamily.get(spec.family),
      node: nodeById.get(`Row.${spec.family}`),
      kernelNode: nodeById.get(`K.${spec.proofRule}`),
      bootRecord: bootCall.record,
    });
    ledger.push(makeLedgerEntry0(
      `bootstrap.${spec.family}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.bootstrap.${spec.family}`,
        result,
        ledger,
      );
    }
    bootstrapDerivations.push(result.nf);
  }

  const lockedNANDDerivations = [];
  for (let index = 0;
    index < GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0.length;
    index += 1) {
    const nodeId = GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0[index];
    const result = checkLockedNANDProofRow0({
      index,
      nodeId,
      binding: input.SemanticFoundationRows.lockedNANDBindings[index],
      node: nodeById.get(nodeId),
      piGNode: piGNodeById.get(nodeId),
      gpack: input.RowFamG.GPack,
      gpackRecord: gpackCall.record,
      rowFamGRecord: rowFamGCall.record,
    });
    ledger.push(makeLedgerEntry0(
      `lockedNAND.${nodeId}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.lockedNAND.${safeCoord0(nodeId)}`,
        result,
        ledger,
      );
    }
    lockedNANDDerivations.push(result.nf);
  }

  const predecessorNF = predecessorCall.record.NF
    ?? predecessorCall.record.nf
    ?? {};
  const bootNF = bootCall.record.NF ?? bootCall.record.nf ?? {};
  const gpackNF = gpackCall.record.NF ?? gpackCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalFoundationRowsSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalFoundationRowsSemanticReady: true,
      globalFoundationRowDerivationsReady: true,
      boundedExecutableRowBindingsOnly: true,
      unrestrictedRowTheoremSoundnessNotClaimed: true,

      infrastructurePredecessorAccepted: true,
      infrastructurePredecessorChecker: predecessorCall.record.checker,
      infrastructurePredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,

      bootstrapBatchAccepted: true,
      bootstrapBatchChecker: bootCall.record.checker,
      bootstrapBatchDigest: bootCall.record.Digest ?? bootCall.record.digest,
      bootstrapBatchRowCount: bootNF.rowCount ?? b0Rows.length,
      bootstrapFamilies: [...GLOBAL_FOUNDATION_ROW_FAMILIES0],
      bootstrapDerivations,
      bootstrapDerivationDigests: bootstrapDerivations.map((entry) => ({
        family: entry.family,
        nodeId: entry.nodeId,
        digest: entry.derivationDigest,
        nodeDigest: entry.nodeDigest,
        rowDigest: entry.rowDigest,
        rowKeyDigest: entry.rowKeyDigest,
        kernelNodeDigest: entry.kernelNodeDigest,
        checkerContractDigest: entry.checkerContractDigest,
        conclusionDigest: entry.conclusionDigest,
      })),

      lockedNANDPackageAccepted: true,
      lockedNANDPackageChecker: gpackCall.record.checker,
      lockedNANDPackageDigest:
        gpackCall.record.Digest ?? gpackCall.record.digest,
      lockedNANDBaseline: gpackNF.baseline ?? null,
      lockedNANDResidualSlackMax: gpackNF.residualSlackMax ?? null,
      lockedNANDRowFamilyAccepted: true,
      lockedNANDRowFamilyChecker: rowFamGCall.record.checker,
      lockedNANDRowFamilyDigest:
        rowFamGCall.record.Digest ?? rowFamGCall.record.digest,
      lockedNANDProofRowIds: [...GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0],
      lockedNANDDerivations,
      lockedNANDDerivationDigests: lockedNANDDerivations.map((entry) => ({
        nodeId: entry.nodeId,
        rowKind: entry.rowKind,
        digest: entry.derivationDigest,
        nodeDigest: entry.nodeDigest,
        piGNodeDigest: entry.piGNodeDigest,
        certificateDigest: entry.certificateDigest,
        checkerContractDigest: entry.checkerContractDigest,
        conclusionDigest: entry.conclusionDigest,
      })),

      semanticFoundationRowNodeIds: [...GLOBAL_FOUNDATION_ROW_NODE_IDS0],
      semanticFoundationRowNodeCount: GLOBAL_FOUNDATION_ROW_NODE_IDS0.length,
      remainingRowFamiliesReady: false,
      globalRowDerivationsReady: false,
      globalPackageDerivationsReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      remainingRowFamiliesRemainSeparate: true,
      packageAndFinalNodesRemainQuarantined: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeBootstrapBinding0({ index, spec, row, node, kernelNode }) {
  const contract = {
    ...GLOBAL_FOUNDATION_ROW_CONTRACTS0.bootstrap,
    family: spec.family,
    proofRule: spec.proofRule,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    kindKey: spec.kindKey,
    arityKey: spec.arityKey,
    payloadKey: spec.payloadKey,
    bound: spec.bound,
  };
  const base = Object.freeze({
    kind: 'GlobalFoundationBootstrapRowBinding0',
    version: CHECKER_VERSION,
    index,
    family: spec.family,
    nodeId: `Row.${spec.family}`,
    nodeDigest: digestCanonical0(stripDigestFields0(node)),
    rowDigest: digestCanonical0(row),
    rowKeyDigest: digestCanonical0(row?.RowKey ?? null),
    rowHashKey: row?.HashKey ?? null,
    proofRule: spec.proofRule,
    kernelNodeId: `K.${spec.proofRule}`,
    kernelNodeDigest: digestCanonical0(stripDigestFields0(kernelNode)),
    checkerContractDigest: digestCanonical0(contract),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function makeLockedNANDBinding0({ index, nodeId, node, piGNode, gpack }) {
  const contract = GLOBAL_FOUNDATION_ROW_CONTRACTS0[nodeId];
  const certificate = getGCertificate0(gpack, contract.rowKind);
  const base = Object.freeze({
    kind: 'GlobalFoundationLockedNANDBinding0',
    version: CHECKER_VERSION,
    index,
    nodeId,
    rowKind: contract.rowKind,
    theorem: contract.theorem,
    nodeDigest: digestCanonical0(stripDigestFields0(node)),
    piGNodeDigest: digestCanonical0(piGNode),
    certificateDigest: digestCanonical0(certificate),
    checkerContractDigest: digestCanonical0(contract),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function checkBootstrapRow0({
  index,
  spec,
  binding,
  row,
  node,
  kernelNode,
  bootRecord,
}) {
  if (!isPlainObject0(row)) {
    return validationReject0(
      ['RowPack', 'Rows', 'B0', spec.family],
      'foundation bootstrap family is missing its concrete row',
      { family: spec.family },
    );
  }
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', `Row.${spec.family}`],
      'foundation bootstrap family is missing its global row node',
      { family: spec.family },
    );
  }
  if (!isPlainObject0(kernelNode)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', `K.${spec.proofRule}`],
      'foundation bootstrap row proof rule must resolve to a semantic kernel coordinate',
      { family: spec.family, proofRule: spec.proofRule },
    );
  }
  if (!SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.includes(spec.proofRule)) {
    return validationReject0(
      ['RowPack', 'Rows', 'B0', spec.family, 'ProofRef', 'rule'],
      'foundation bootstrap row proof rule is not in the complete semantic kernel',
      { family: spec.family, proofRule: spec.proofRule },
    );
  }

  const expectedFields = {
    BatchID: 'B0',
    FamilyID: spec.family,
    PackageID: spec.packageId,
    SchemaID: spec.schemaId,
    KindKey: spec.kindKey,
    ArityKey: spec.arityKey,
    ModeKey: 'Full',
    PayloadKey: spec.payloadKey,
    SelectedRoute: 'Accept',
  };
  for (const [field, expected] of Object.entries(expectedFields)) {
    if (row[field] !== expected) {
      return validationReject0(
        ['RowPack', 'Rows', 'B0', spec.family, field],
        'foundation bootstrap row field mismatch',
        { family: spec.family, field, expected, actual: row[field] },
      );
    }
  }
  if (!sameCanonical0(row.CandidateRoutes, ['Accept'])
      || !sameCanonical0(row.ActiveRouteSet, ['Accept'])) {
    return validationReject0(
      ['RowPack', 'Rows', 'B0', spec.family, 'CandidateRoutes'],
      'foundation bootstrap row must select the unique Accept route',
      {
        family: spec.family,
        candidateRoutes: row.CandidateRoutes,
        activeRouteSet: row.ActiveRouteSet,
      },
    );
  }
  if (row.ProofRef?.rule !== spec.proofRule
      || row.ProofRef?.id !== `B0.${spec.family}.proof`) {
    return validationReject0(
      ['RowPack', 'Rows', 'B0', spec.family, 'ProofRef'],
      'foundation bootstrap row proof reference mismatch',
      {
        family: spec.family,
        expectedRule: spec.proofRule,
        expectedId: `B0.${spec.family}.proof`,
        actual: row.ProofRef,
      },
    );
  }
  if (row.BoundsRef?.bound !== spec.bound
      || row.BoundsRef?.id !== `B0.${spec.family}.bounds`) {
    return validationReject0(
      ['RowPack', 'Rows', 'B0', spec.family, 'BoundsRef'],
      'foundation bootstrap row bounds reference mismatch',
      { family: spec.family, actual: row.BoundsRef },
    );
  }
  const recomputedHash = DigestObject0(row.RowKey);
  if (!sameCanonical0(row.HashKey, recomputedHash)) {
    return validationReject0(
      ['RowPack', 'Rows', 'B0', spec.family, 'HashKey'],
      'foundation bootstrap row hash must equal the recomputed row-key hash',
      { family: spec.family, expected: recomputedHash, actual: row.HashKey },
    );
  }

  const contract = GLOBAL_FOUNDATION_ROW_CONTRACTS0.bootstrap;
  if (node.nodeKind !== contract.globalNodeKind
      || node.label !== spec.family
      || !sameCanonical0(node.premises, contract.globalNodePremises)
      || node.conclusion?.tag !== contract.globalConclusionTag
      || node.conclusion?.family !== spec.family) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', `Row.${spec.family}`],
      'foundation bootstrap global row node contract mismatch',
      {
        family: spec.family,
        expectedPremises: contract.globalNodePremises,
        actual: node,
      },
    );
  }
  if (kernelNode.nodeKind !== 'kernel'
      || kernelNode.conclusion?.tag !== 'KernelRuleAccepted0'
      || kernelNode.conclusion?.rule !== spec.proofRule) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', `K.${spec.proofRule}`],
      'foundation bootstrap row semantic kernel coordinate mismatch',
      { family: spec.family, actual: kernelNode },
    );
  }

  const expectedBinding = makeBootstrapBinding0({
    index,
    spec,
    row,
    node,
    kernelNode,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticFoundationRows', 'bootstrapBindings', index],
      'foundation bootstrap binding must exactly match the concrete row, global node, kernel coordinate, and executable contract',
      { family: spec.family, expected: expectedBinding, actual: binding },
    );
  }

  const conclusion = Object.freeze({
    kind: 'GlobalFoundationBootstrapRowConclusion0',
    version: CHECKER_VERSION,
    family: spec.family,
    nodeId: `Row.${spec.family}`,
    batchId: 'B0',
    proofRule: spec.proofRule,
    selectedRoute: 'Accept',
    rowKeyAndHashRecomputed: true,
    semanticPrimitiveCoordinateBound: true,
    boundedExecutableRowBinding: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  });
  const nf = {
    kind: 'GlobalFoundationBootstrapRowDerivation0NF',
    version: CHECKER_VERSION,
    family: spec.family,
    nodeId: `Row.${spec.family}`,
    batchId: 'B0',
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    proofRule: spec.proofRule,
    nodeDigest: expectedBinding.nodeDigest,
    rowDigest: expectedBinding.rowDigest,
    rowKeyDigest: expectedBinding.rowKeyDigest,
    rowHashKey: expectedBinding.rowHashKey,
    kernelNodeDigest: expectedBinding.kernelNodeDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    bootBatchDigest: bootRecord.Digest ?? bootRecord.digest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    ready: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function checkLockedNANDProofRow0({
  index,
  nodeId,
  binding,
  node,
  piGNode,
  gpack,
  gpackRecord,
  rowFamGRecord,
}) {
  const contract = GLOBAL_FOUNDATION_ROW_CONTRACTS0[nodeId];
  const certificate = getGCertificate0(gpack, contract.rowKind);
  if (!isPlainObject0(node)
      || !isPlainObject0(piGNode)
      || !isPlainObject0(certificate)) {
    return validationReject0(
      ['LockedNAND', nodeId],
      'locked-NAND foundation proof row requires a global node, PiG node, and certificate',
      {
        nodeId,
        nodePresent: isPlainObject0(node),
        piGNodePresent: isPlainObject0(piGNode),
        certificatePresent: isPlainObject0(certificate),
      },
    );
  }
  if (node.nodeKind !== 'row'
      || node.label !== nodeId
      || !sameCanonical0(node.premises, contract.globalPremises)
      || node.conclusion?.tag !== 'GProofNodeAccepted0'
      || node.conclusion?.rowKind !== contract.rowKind
      || node.conclusion?.theorem !== contract.theorem
      || node.conclusion?.proofRef?.id !== nodeId
      || node.payload?.package !== 'G'
      || node.payload?.rule !== contract.rule
      || node.payload?.derivationKind !== contract.derivationKind
      || node.payload?.transparentProof !== true) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId],
      'locked-NAND global proof row contract mismatch',
      { nodeId, contract, actual: node },
    );
  }
  if (piGNode.kind !== 'KProofNode0'
      || piGNode.id !== nodeId
      || piGNode.refKind !== 'KPrimitive'
      || piGNode.rowKind !== contract.rowKind
      || piGNode.rule !== contract.rule
      || piGNode.mode !== 'full'
      || !sameCanonical0(piGNode.premises, contract.piGPremises)
      || piGNode.conclusion?.kind !== 'GProofConclusion0'
      || piGNode.conclusion?.rowKind !== contract.rowKind
      || piGNode.conclusion?.theorem !== contract.theorem
      || piGNode.conclusion?.accepted !== true
      || piGNode.payload?.derivationKind !== contract.derivationKind) {
    return validationReject0(
      ['RowFamG', 'GPack', 'PiG', 'proofNodes', nodeId],
      'locked-NAND PiG proof row contract mismatch',
      { nodeId, contract, actual: piGNode },
    );
  }
  if (certificate.derivation?.proofRef?.id !== nodeId
      || certificate.derivation?.proofRef?.refKind !== 'KPrimitive') {
    return validationReject0(
      ['RowFamG', 'GPack', contract.rowKind, 'derivation', 'proofRef'],
      'locked-NAND certificate derivation must reference its exact PiG proof row',
      { nodeId, actual: certificate.derivation?.proofRef },
    );
  }

  if (contract.rowKind === 'BaselineCert') {
    if (node.payload.directWireOutputConvention !== true
        || node.payload.lowerBoundRuleApplied !== true
        || certificate.lowerBound !== true
        || certificate.directWireOutputLowerBound !== true
        || certificate.baseline !== certificate.derivation?.baseline) {
      return validationReject0(
        ['LockedNAND', nodeId, 'baseline'],
        'locked-NAND baseline proof row failed its exact lower-bound contract',
        { node: node.payload, certificate },
      );
    }
  } else if (contract.rowKind === 'TraceCert') {
    if (node.payload.topologicalInduction !== true
        || node.payload.traceCoherent !== true
        || certificate.traceCoherent !== true
        || certificate.topologicalTraceInduction !== true) {
      return validationReject0(
        ['LockedNAND', nodeId, 'trace'],
        'locked-NAND trace proof row failed its exact coherence contract',
        { node: node.payload, certificate },
      );
    }
  } else if (contract.rowKind === 'ThresholdCert') {
    const expected = {
      residualSlackMax: certificate.residualSlackMax,
      satIffMinAboveBaseline: certificate.satIffMinAboveBaseline,
      unsatMinEqualsBaseline: certificate.unsatMinEqualsBaseline,
      finalOutputGates: certificate.derivation?.finalOutputGates,
    };
    for (const [field, value] of Object.entries(expected)) {
      if (node.payload[field] !== value) {
        return validationReject0(
          ['LockedNAND', nodeId, 'payload', field],
          'locked-NAND threshold proof row must bind the exact checked certificate value',
          { field, expected: value, actual: node.payload[field] },
        );
      }
    }
    if (certificate.lockedThreshold !== true
        || certificate.residualSlackMax !== 4
        || certificate.satIffMinAboveBaseline !== true
        || certificate.unsatMinEqualsBaseline !== true) {
      return validationReject0(
        ['LockedNAND', nodeId, 'threshold'],
        'locked-NAND threshold certificate contract mismatch',
        { certificate },
      );
    }
  }

  const expectedBinding = makeLockedNANDBinding0({
    index,
    nodeId,
    node,
    piGNode,
    gpack,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticFoundationRows', 'lockedNANDBindings', index],
      'locked-NAND foundation binding must exactly match the global node, PiG node, certificate, and executable contract',
      { nodeId, expected: expectedBinding, actual: binding },
    );
  }

  const conclusion = Object.freeze({
    kind: 'GlobalFoundationLockedNANDProofConclusion0',
    version: CHECKER_VERSION,
    nodeId,
    rowKind: contract.rowKind,
    theorem: contract.theorem,
    globalNodeContractVerified: true,
    piGNodeContractVerified: true,
    certificateContractVerified: true,
    boundedExecutableRowBinding: true,
    unrestrictedRowTheoremSoundnessNotClaimed: true,
  });
  const nf = {
    kind: 'GlobalFoundationLockedNANDProofDerivation0NF',
    version: CHECKER_VERSION,
    nodeId,
    rowKind: contract.rowKind,
    theorem: contract.theorem,
    nodeDigest: expectedBinding.nodeDigest,
    piGNodeDigest: expectedBinding.piGNodeDigest,
    certificateDigest: expectedBinding.certificateDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    gpackDigest: gpackRecord.Digest ?? gpackRecord.digest,
    rowFamGDigest: rowFamGRecord.Digest ?? rowFamGRecord.digest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    ready: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'global foundation-row semantic input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalFoundationRowsSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global foundation-row semantic input kind must be GlobalFoundationRowsSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global foundation-row semantic input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowPack',
    'RowFamG',
    'SemanticFoundationRows',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global foundation-row semantic input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)
      || !isPlainObject0(input.LegacyGlobalProofDAG)
      || !isPlainObject0(input.InfrastructureSemanticDerivations)
      || !isPlainObject0(input.RowPack)
      || !isPlainObject0(input.RowFamG)
      || !isPlainObject0(input.SemanticFoundationRows)) {
    return validationReject0(
      ['input'],
      'global foundation-row semantic dependency surfaces must be objects',
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global foundation-row semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)
      || !Array.isArray(input.RowPack.Rows)) {
    return validationReject0(
      ['input'],
      'global foundation-row semantic input requires global Nodes and RowPack Rows arrays',
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_FOUNDATION_ROWS_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global foundation-row semantic policy must match the fail-closed policy',
      { expected: GLOBAL_FOUNDATION_ROWS_POLICY0, actual: input.Policy },
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
    'SemanticFoundationRows',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global foundation-row semantic checker rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalFoundationRowsSemanticInputShape0NF',
  });
}

function validateSemanticSuite0(suite, dag, rowPack, rowFamG) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticFoundationRows'],
      'global foundation-row semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'suiteId',
    'bootstrapBindings',
    'lockedNANDBindings',
    'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticFoundationRows', unexpected[0]],
      'global foundation-row semantic suite rejects caller-supplied truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalFoundationRowsSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string'
      || suite.suiteId.length === 0) {
    return validationReject0(
      ['SemanticFoundationRows'],
      'global foundation-row semantic suite kind, version, or suiteId is invalid',
      { actual: suite },
    );
  }
  if (!Array.isArray(suite.bootstrapBindings)
      || suite.bootstrapBindings.length !== BOOT_BATCH0_REQUIRED_ROWS.length) {
    return validationReject0(
      ['SemanticFoundationRows', 'bootstrapBindings'],
      'global foundation-row suite must provide one bootstrap binding per required B0 family',
      {
        expected: BOOT_BATCH0_REQUIRED_ROWS.length,
        actual: suite.bootstrapBindings?.length,
      },
    );
  }
  if (!Array.isArray(suite.lockedNANDBindings)
      || suite.lockedNANDBindings.length
        !== GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0.length) {
    return validationReject0(
      ['SemanticFoundationRows', 'lockedNANDBindings'],
      'global foundation-row suite must provide one binding per locked-NAND proof row',
      {
        expected: GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0.length,
        actual: suite.lockedNANDBindings?.length,
      },
    );
  }
  if (!sameCanonical0(suite.Policy, GLOBAL_FOUNDATION_ROWS_POLICY0)) {
    return validationReject0(
      ['SemanticFoundationRows', 'Policy'],
      'global foundation-row semantic suite policy mismatch',
      { expected: GLOBAL_FOUNDATION_ROWS_POLICY0, actual: suite.Policy },
    );
  }
  const expected = makeGlobalFoundationRowsSemanticSuite0({
    LegacyGlobalProofDAG: dag,
    RowPack: rowPack,
    RowFamG: rowFamG,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SemanticFoundationRows'],
      'global foundation-row semantic suite must exactly match the computed row, node, certificate, and checker bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalFoundationRowsSemanticSuite0NF',
    suiteId: suite.suiteId,
    bootstrapBindingCount: suite.bootstrapBindings.length,
    lockedNANDBindingCount: suite.lockedNANDBindings.length,
    foundationRowNodeIds: [...GLOBAL_FOUNDATION_ROW_NODE_IDS0],
    bindingDigests: [
      ...suite.bootstrapBindings.map((entry) => entry.bindingDigest),
      ...suite.lockedNANDBindings.map((entry) => entry.bindingDigest),
    ],
    policyDigest: digestCanonical0(suite.Policy),
  });
}

function getPiG0(gpack) {
  return gpack?.PiG ?? gpack?.['ΠG'] ?? gpack?.piG;
}

function getGCertificate0(gpack, rowKind) {
  if (rowKind === 'BaselineCert') return gpack?.BaselineCert;
  if (rowKind === 'TraceCert') return gpack?.TraceCert;
  if (rowKind === 'ThresholdCert') return gpack?.ThresholdCert;
  return null;
}

function stripDigestFields0(value) {
  if (!isPlainObject0(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
}

function isInfrastructureAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.globalInfrastructureSemanticReady === true
    && nf?.semanticOverlay?.globalInfrastructureSemanticReady === true
    && nf?.semanticOverlay?.globalRowDerivationsReady === false
    && nf?.finalTheoremReady === false
    && nf?.publicTheoremEmissionAllowed === false;
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
