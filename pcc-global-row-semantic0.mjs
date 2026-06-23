import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGlobalProofDAG0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalInfrastructureSemantic0,
  makeGlobalInfrastructureSemanticInput0,
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  CheckBatchDeps0,
  CheckRowFamilies0,
  CheckRows0,
  ROW_REQUIRED_FAMILIES0,
  ROW_REQUIRED_FAMILY_SPECS0,
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

import {
  CheckGPack0,
  CheckRowFamG0,
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_LOCKED_NAND_PROOF_ROW_IDS0 = Object.freeze([
  'G.BaselineCert.proof',
  'G.TraceCert.proof',
  'G.ThresholdCert.proof',
]);

export const GLOBAL_ROW_SEMANTIC_SCOPE0 = Object.freeze({
  kind: 'GlobalRowSemanticScope0',
  version: CHECKER_VERSION,
  scope: 'executable-row-schema-route-and-locked-nand-proof-refinement',
  rowPackCoverageAndCanonicalityChecked: true,
  selectedRoutesChecked: true,
  proofReferencesChecked: true,
  globalNodeBindingsChecked: true,
  lockedNANDProofNodesChecked: true,
  mathematicalGovernedUniverseCompletenessNotClaimed: true,
  primitiveProofRuleSoundnessNotClaimedHere: true,
  packageTheoremSoundnessNotClaimedHere: true,
  finalTheoremSoundnessNotClaimedHere: true,
});

export const GLOBAL_ROW_SEMANTIC_POLICY0 = Object.freeze({
  kind: 'GlobalRowSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresGlobalInfrastructureSemanticReadiness: true,
  requiresLegacyGlobalDAGStructuralAcceptance: true,
  requiresRowPackAcceptance: true,
  requiresBatchDependencyAcceptance: true,
  requiresRowFamilyCoverageAcceptance: true,
  requiresLockedNANDGPackAcceptance: true,
  requiresLockedNANDRowFamilyAcceptance: true,
  oneDerivationPerRequiredRowFamily: true,
  threeLockedNANDProofRowDerivationsRequired: true,
  bindsGlobalNodeDigest: true,
  bindsExecutableRowDigest: true,
  bindsRowKeyProofRefAndBoundsDigests: true,
  bindsCheckerContractDigest: true,
  callerReadinessAssertionsForbidden: true,
  mathematicalGovernedUniverseCompletenessNotClaimed: true,
  primitiveProofRuleSoundnessNotClaimedHere: true,
  packageAndFinalDerivationsRemainSeparate: true,
});

export const GLOBAL_LOCKED_NAND_PROOF_ROW_CONTRACTS0 = Object.freeze([
  Object.freeze({
    kind: 'GlobalLockedNANDProofRowContract0',
    version: CHECKER_VERSION,
    index: 0,
    nodeId: 'G.BaselineCert.proof',
    rowKind: 'BaselineCert',
    certificateField: 'BaselineCert',
    theorem: 'BaselineDistinct',
    rule: 'BaselineDistinctDirectWire0',
    derivationKind: 'BaselineDerivation0',
    globalPremises: Object.freeze(['K.Record', 'K.DAGInd']),
    gProofPremises: Object.freeze([]),
  }),
  Object.freeze({
    kind: 'GlobalLockedNANDProofRowContract0',
    version: CHECKER_VERSION,
    index: 1,
    nodeId: 'G.TraceCert.proof',
    rowKind: 'TraceCert',
    certificateField: 'TraceCert',
    theorem: 'TraceCoherence',
    rule: 'NANDTraceCoherence0',
    derivationKind: 'TraceDerivation0',
    globalPremises: Object.freeze(['K.Record', 'K.TraceInd']),
    gProofPremises: Object.freeze([]),
  }),
  Object.freeze({
    kind: 'GlobalLockedNANDProofRowContract0',
    version: CHECKER_VERSION,
    index: 2,
    nodeId: 'G.ThresholdCert.proof',
    rowKind: 'ThresholdCert',
    certificateField: 'ThresholdCert',
    theorem: 'LockedNANDThreshold',
    rule: 'LockedNANDThreshold0',
    derivationKind: 'ThresholdDerivation0',
    globalPremises: Object.freeze([
      'G.BaselineCert.proof',
      'G.TraceCert.proof',
      'K.IntArith',
    ]),
    gProofPremises: Object.freeze([
      'G.BaselineCert.proof',
      'G.TraceCert.proof',
    ]),
  }),
]);

export function makeGlobalRowSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  const rowByFamily = new Map(
    (RowPack?.Rows ?? []).map((row) => [row?.FamilyID, row]),
  );
  const gRowByKind = new Map(
    (RowFamG?.rows ?? []).map((row) => [row?.rowKind, row]),
  );
  const gProofNodeById = new Map(
    getGProofNodes0(RowFamG?.GPack).map((node) => [node?.id, node]),
  );

  return Object.freeze({
    kind: 'GlobalRowSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.rows.semantic.phase35',
    familyBindings: Object.freeze(
      ROW_REQUIRED_FAMILY_SPECS0.map((spec, index) => makeFamilyBinding0({
        index,
        spec,
        node: nodeById.get(`Row.${spec.family}`) ?? null,
        row: rowByFamily.get(spec.family) ?? null,
      })),
    ),
    lockedNANDBindings: Object.freeze(
      GLOBAL_LOCKED_NAND_PROOF_ROW_CONTRACTS0.map((contract) =>
        makeLockedNANDBinding0({
          contract,
          globalNode: nodeById.get(contract.nodeId) ?? null,
          gProofNode: gProofNodeById.get(contract.nodeId) ?? null,
          rowFamGRow: gRowByKind.get(contract.rowKind) ?? null,
          certificate: RowFamG?.GPack?.[contract.certificateField] ?? null,
        })),
    ),
    Scope: { ...GLOBAL_ROW_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_ROW_SEMANTIC_POLICY0 },
  });
}

export function makeGlobalRowSemanticInput0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  SemanticRows = makeGlobalRowSemanticSuite0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
  }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalRowSemanticInput0',
    version: CHECKER_VERSION,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    SemanticRows,
    Scope: { ...GLOBAL_ROW_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_ROW_SEMANTIC_POLICY0 },
  });
}

export async function CheckGlobalRowSemantic0(input) {
  const checker = 'CheckGlobalRowSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
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
    infrastructureCall.ok && isInfrastructureAccept0(infrastructureCall.record),
    infrastructureCall.ok ? infrastructureCall.record : infrastructureCall.witness,
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
  if (!isInfrastructureAccept0(infrastructureCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticInfrastructure`,
      path: ['InfrastructureSemanticDerivations'],
      witness: {
        reason: 'global row derivations require accepted global infrastructure semantics',
        inner: compactRecord0(infrastructureCall.record),
      },
      ledger,
    });
  }

  const legacyCall = await callChecker0(
    'CheckGlobalProofDAG0',
    () => CheckGlobalProofDAG0(input.LegacyGlobalProofDAG),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAG0',
    legacyCall.ok && legacyCall.record.tag === 'accept',
    legacyCall.ok ? legacyCall.record : legacyCall.witness,
  ));
  if (!legacyCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyGlobalDAG.exception`,
      path: ['LegacyGlobalProofDAG'],
      witness: legacyCall.witness,
      ledger,
    });
  }
  if (legacyCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyGlobalDAG`,
      path: ['LegacyGlobalProofDAG'],
      witness: {
        reason: 'legacy global proof DAG rejected before row semantic upgrade',
        inner: compactRecord0(legacyCall.record),
      },
      ledger,
    });
  }

  const rowsCall = await callChecker0(
    'CheckRows0',
    () => CheckRows0(input.RowPack),
  );
  ledger.push(makeLedgerEntry0(
    'CheckRows0',
    rowsCall.ok && rowsCall.record.tag === 'accept',
    rowsCall.ok ? rowsCall.record : rowsCall.witness,
  ));
  if (!rowsCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.rows.exception`,
      path: ['RowPack'],
      witness: rowsCall.witness,
      ledger,
    });
  }
  if (rowsCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.rows`,
      path: ['RowPack'],
      witness: {
        reason: 'row package rejected before global row semantic upgrade',
        inner: compactRecord0(rowsCall.record),
      },
      ledger,
    });
  }

  const batchCall = await callChecker0(
    'CheckBatchDeps0',
    () => CheckBatchDeps0(input.RowPack.BatchInv),
  );
  ledger.push(makeLedgerEntry0(
    'CheckBatchDeps0',
    batchCall.ok && batchCall.record.tag === 'accept',
    batchCall.ok ? batchCall.record : batchCall.witness,
  ));
  if (!batchCall.ok || batchCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.batchDependencies`,
      path: ['RowPack', 'BatchInv'],
      witness: {
        reason: 'row batch dependencies rejected before global row semantic upgrade',
        inner: batchCall.ok ? compactRecord0(batchCall.record) : batchCall.witness,
      },
      ledger,
    });
  }

  const familiesCall = await callChecker0(
    'CheckRowFamilies0',
    () => CheckRowFamilies0(input.RowPack),
  );
  ledger.push(makeLedgerEntry0(
    'CheckRowFamilies0',
    familiesCall.ok && familiesCall.record.tag === 'accept',
    familiesCall.ok ? familiesCall.record : familiesCall.witness,
  ));
  if (!familiesCall.ok || familiesCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.rowFamilies`,
      path: ['RowPack'],
      witness: {
        reason: 'row-family coverage rejected before global row semantic upgrade',
        inner: familiesCall.ok
          ? compactRecord0(familiesCall.record)
          : familiesCall.witness,
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
  if (!gpackCall.ok || gpackCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.gpack`,
      path: ['RowFamG', 'GPack'],
      witness: {
        reason: 'locked-NAND GPack rejected before proof-row semantic upgrade',
        inner: gpackCall.ok ? compactRecord0(gpackCall.record) : gpackCall.witness,
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
  if (!rowFamGCall.ok || rowFamGCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.rowFamG`,
      path: ['RowFamG'],
      witness: {
        reason: 'locked-NAND row family rejected before proof-row semantic upgrade',
        inner: rowFamGCall.ok
          ? compactRecord0(rowFamGCall.record)
          : rowFamGCall.witness,
      },
      ledger,
    });
  }

  const suite = validateSemanticSuite0(input.SemanticRows, input);
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
  const rowByFamily = new Map(
    input.RowPack.Rows.map((row) => [row.FamilyID, row]),
  );
  const familyDerivations = [];
  for (let index = 0; index < ROW_REQUIRED_FAMILY_SPECS0.length; index += 1) {
    const spec = ROW_REQUIRED_FAMILY_SPECS0[index];
    const result = deriveFamily0({
      index,
      spec,
      node: nodeById.get(`Row.${spec.family}`),
      row: rowByFamily.get(spec.family),
      binding: input.SemanticRows.familyBindings[index],
      rowsRecord: rowsCall.record,
      familiesRecord: familiesCall.record,
    });
    ledger.push(makeLedgerEntry0(
      `rowFamily.${spec.family}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.rowFamily.${safeCoord0(spec.family)}`,
        result,
        ledger,
      );
    }
    familyDerivations.push(result.nf);
  }

  const gProofNodeById = new Map(
    getGProofNodes0(input.RowFamG.GPack).map((node) => [node.id, node]),
  );
  const gRowByKind = new Map(
    input.RowFamG.rows.map((row) => [row.rowKind, row]),
  );
  const lockedNANDDerivations = [];
  for (let index = 0;
    index < GLOBAL_LOCKED_NAND_PROOF_ROW_CONTRACTS0.length;
    index += 1) {
    const contract = GLOBAL_LOCKED_NAND_PROOF_ROW_CONTRACTS0[index];
    const result = deriveLockedNANDProofRow0({
      contract,
      globalNode: nodeById.get(contract.nodeId),
      gProofNode: gProofNodeById.get(contract.nodeId),
      rowFamGRow: gRowByKind.get(contract.rowKind),
      certificate: input.RowFamG.GPack[contract.certificateField],
      binding: input.SemanticRows.lockedNANDBindings[index],
      gpackRecord: gpackCall.record,
      rowFamGRecord: rowFamGCall.record,
    });
    ledger.push(makeLedgerEntry0(
      `lockedNAND.${contract.rowKind}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.lockedNAND.${contract.rowKind}`,
        result,
        ledger,
      );
    }
    lockedNANDDerivations.push(result.nf);
  }

  const infrastructureNF =
    infrastructureCall.record.NF ?? infrastructureCall.record.nf ?? {};
  const legacyNF = legacyCall.record.NF ?? legacyCall.record.nf ?? {};
  const rowsNF = rowsCall.record.NF ?? rowsCall.record.nf ?? {};
  const rowFamGNF = rowFamGCall.record.NF ?? rowFamGCall.record.nf ?? {};
  const allDerivations = [...familyDerivations, ...lockedNANDDerivations];
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalRowSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalRowSemanticReady: true,
      globalRowFamilyDerivationsReady: true,
      globalLockedNANDProofRowsReady: true,
      globalRowDerivationsReady: true,

      globalInfrastructureSemanticReady:
        infrastructureNF.globalInfrastructureSemanticReady === true,
      globalInfrastructureSemanticDigest:
        infrastructureCall.record.Digest ?? infrastructureCall.record.digest,
      semanticKBundleFinalReady:
        infrastructureNF.semanticKBundleFinalReady === true,
      semanticK0ConformanceReady:
        infrastructureNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: infrastructureNF.semanticSigmaReady === true,
      semanticReflectionReady:
        infrastructureNF.semanticReflectionReady === true,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: legacyCall.record.checker,
      legacyGlobalDAGDigest: legacyCall.record.Digest ?? legacyCall.record.digest,
      legacyGlobalDAGNodeCount: legacyNF.nodeCount ?? null,

      rowPackAccepted: true,
      rowPackChecker: rowsCall.record.checker,
      rowPackDigest: rowsCall.record.Digest ?? rowsCall.record.digest,
      rowPackObjectDigest: digestCanonical0(input.RowPack),
      rowCount: rowsNF.rowCount ?? input.RowPack.Rows.length,
      requiredRowFamilyCount: ROW_REQUIRED_FAMILIES0.length,
      requiredRowFamilies: [...ROW_REQUIRED_FAMILIES0],
      rowFamilyChecker: familiesCall.record.checker,
      rowFamilyCheckerDigest:
        familiesCall.record.Digest ?? familiesCall.record.digest,
      batchDependencyChecker: batchCall.record.checker,
      batchDependencyCheckerDigest:
        batchCall.record.Digest ?? batchCall.record.digest,

      lockedNANDGPackAccepted: true,
      lockedNANDGPackChecker: gpackCall.record.checker,
      lockedNANDGPackDigest:
        gpackCall.record.Digest ?? gpackCall.record.digest,
      lockedNANDRowFamilyAccepted: true,
      lockedNANDRowFamilyChecker: rowFamGCall.record.checker,
      lockedNANDRowFamilyDigest:
        rowFamGCall.record.Digest ?? rowFamGCall.record.digest,
      lockedNANDRowFamilyCount: rowFamGNF.rowCount ?? null,

      familyDerivationCount: familyDerivations.length,
      lockedNANDProofRowDerivationCount: lockedNANDDerivations.length,
      totalGlobalRowDerivationCount: allDerivations.length,
      semanticRowNodeIds: familyDerivations.map((entry) => entry.nodeId),
      semanticLockedNANDProofRowNodeIds:
        lockedNANDDerivations.map((entry) => entry.nodeId),
      semanticGlobalRowNodeIds: allDerivations.map((entry) => entry.nodeId),
      familyDerivations,
      lockedNANDProofRowDerivations: lockedNANDDerivations,
      globalRowDerivationDigests: allDerivations.map((entry) => ({
        nodeId: entry.nodeId,
        family: entry.family ?? null,
        rowKind: entry.rowKind ?? null,
        digest: entry.derivationDigest,
        globalNodeDigest: entry.globalNodeDigest,
        executableRecordDigest:
          entry.rowDigest ?? entry.gProofNodeDigest ?? null,
        checkerContractDigest: entry.checkerContractDigest,
        conclusionDigest: entry.conclusionDigest,
      })),

      Scope: { ...GLOBAL_ROW_SEMANTIC_SCOPE0 },
      scopeDigest: digestCanonical0(input.Scope),
      mathematicalGovernedUniverseCompletenessNotClaimed: true,
      primitiveProofRuleSoundnessNotClaimedHere: true,
      packageTheoremSoundnessNotClaimedHere: true,
      finalTheoremSoundnessNotClaimedHere: true,

      globalPackageDerivationsReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      packageAndFinalDerivationsRemainSeparate: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeFamilyBinding0({ index, spec, node, row }) {
  const contract = makeFamilyContract0(spec);
  const base = Object.freeze({
    kind: 'GlobalRowFamilySemanticBinding0',
    version: CHECKER_VERSION,
    index,
    family: spec.family,
    nodeId: `Row.${spec.family}`,
    batchId: spec.batchId,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    proofRule: spec.proofRule,
    selectedRoute: row?.SelectedRoute ?? null,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    rowDigest: digestCanonical0(row),
    rowKeyDigest: digestCanonical0(row?.RowKey ?? null),
    proofRefDigest: digestCanonical0(row?.ProofRef ?? null),
    boundsRefDigest: digestCanonical0(row?.BoundsRef ?? null),
    checkerContractDigest: digestCanonical0(contract),
    conclusionDigest: digestCanonical0(node?.conclusion ?? null),
    scope: GLOBAL_ROW_SEMANTIC_SCOPE0.scope,
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function makeLockedNANDBinding0({
  contract,
  globalNode,
  gProofNode,
  rowFamGRow,
  certificate,
}) {
  const base = Object.freeze({
    kind: 'GlobalLockedNANDProofRowSemanticBinding0',
    version: CHECKER_VERSION,
    index: contract.index,
    nodeId: contract.nodeId,
    rowKind: contract.rowKind,
    theorem: contract.theorem,
    rule: contract.rule,
    globalNodeDigest: digestCanonical0(stripDigestFields0(globalNode)),
    gProofNodeDigest: digestCanonical0(gProofNode),
    rowFamGRowDigest: digestCanonical0(rowFamGRow),
    certificateDigest: digestCanonical0(certificate),
    checkerContractDigest: digestCanonical0(contract),
    conclusionDigest: digestCanonical0(globalNode?.conclusion ?? null),
    scope: GLOBAL_ROW_SEMANTIC_SCOPE0.scope,
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function makeFamilyContract0(spec) {
  return Object.freeze({
    kind: 'GlobalRowFamilyExecutableContract0',
    version: CHECKER_VERSION,
    family: spec.family,
    nodeId: `Row.${spec.family}`,
    nodeKind: 'row',
    globalPremises: Object.freeze(['K.Record', 'K.Transport']),
    conclusionTag: 'RowFamilyAccepted0',
    batchId: spec.batchId,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    kindKey: spec.kindKey,
    arityKey: spec.arityKey,
    payloadKey: spec.payloadKey,
    proofRule: spec.proofRule,
    bound: spec.bound,
    requiredSelectedRoute: 'Accept',
    semanticChecker: 'CheckRows0',
    familyChecker: 'CheckRowFamilies0',
  });
}

function deriveFamily0({
  index,
  spec,
  node,
  row,
  binding,
  rowsRecord,
  familiesRecord,
}) {
  const contract = makeFamilyContract0(spec);
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', `Row.${spec.family}`],
      'global row-family semantic coordinate is missing its global node',
      { family: spec.family },
    );
  }
  for (const [field, expected] of Object.entries({
    id: `Row.${spec.family}`,
    nodeKind: 'row',
    label: spec.family,
  })) {
    if (node[field] !== expected) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', node.id ?? `Row.${spec.family}`, field],
        'global row-family node identity or kind mismatch',
        { family: spec.family, field, expected, actual: node[field] },
      );
    }
  }
  if (!sameCanonical0(node.premises, contract.globalPremises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', node.id, 'premises'],
      'global row-family node must retain the exact Record and Transport prerequisites',
      { family: spec.family, expected: contract.globalPremises, actual: node.premises },
    );
  }
  if (node.conclusion?.tag !== 'RowFamilyAccepted0'
      || node.conclusion?.family !== spec.family) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', node.id, 'conclusion'],
      'global row-family conclusion must match its family coordinate',
      { family: spec.family, actual: node.conclusion },
    );
  }

  if (!isPlainObject0(row)) {
    return validationReject0(
      ['RowPack', 'Rows', spec.family],
      'global row-family derivation is missing its executable row record',
      { family: spec.family },
    );
  }
  for (const [field, expected] of Object.entries({
    BatchID: spec.batchId,
    FamilyID: spec.family,
    PackageID: spec.packageId,
    SchemaID: spec.schemaId,
    KindKey: spec.kindKey,
    ArityKey: spec.arityKey,
    PayloadKey: spec.payloadKey,
    ModeKey: 'Full',
    SelectedRoute: 'Accept',
  })) {
    if (row[field] !== expected) {
      return validationReject0(
        ['RowPack', 'Rows', spec.family, field],
        'executable row record must exactly match its required family contract',
        { family: spec.family, field, expected, actual: row[field] },
      );
    }
  }
  if (!Array.isArray(row.CandidateRoutes)
      || !row.CandidateRoutes.includes('Accept')
      || !Array.isArray(row.ActiveRouteSet)
      || !row.ActiveRouteSet.includes('Accept')) {
    return validationReject0(
      ['RowPack', 'Rows', spec.family, 'SelectedRoute'],
      'executable row record must expose Accept as an active candidate route',
      {
        family: spec.family,
        candidateRoutes: row.CandidateRoutes,
        activeRouteSet: row.ActiveRouteSet,
      },
    );
  }
  if (row.TransportProof?.kind !== 'identity') {
    return validationReject0(
      ['RowPack', 'Rows', spec.family, 'TransportProof', 'kind'],
      'phase-35 row semantic contract requires the generated identity transport proof',
      { family: spec.family, actual: row.TransportProof },
    );
  }
  if (row.ProofRef?.rule !== spec.proofRule) {
    return validationReject0(
      ['RowPack', 'Rows', spec.family, 'ProofRef', 'rule'],
      'row proof reference must bind the declared primitive proof rule',
      { family: spec.family, expected: spec.proofRule, actual: row.ProofRef?.rule },
    );
  }
  if (row.BoundsRef?.bound !== spec.bound) {
    return validationReject0(
      ['RowPack', 'Rows', spec.family, 'BoundsRef', 'bound'],
      'row bounds reference must bind the declared family bound',
      { family: spec.family, expected: spec.bound, actual: row.BoundsRef?.bound },
    );
  }

  const expectedBinding = makeFamilyBinding0({ index, spec, node, row });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticRows', 'familyBindings', index],
      'global row-family binding must exactly match the computed global-node and executable-row boundary',
      { family: spec.family, expected: expectedBinding, actual: binding },
    );
  }

  const conclusion = Object.freeze({
    kind: 'GlobalRowFamilySemanticConclusion0',
    version: CHECKER_VERSION,
    family: spec.family,
    nodeId: node.id,
    batchId: spec.batchId,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    selectedRoute: 'Accept',
    proofRule: spec.proofRule,
    executableSchemaRouteRefinementAccepted: true,
    mathematicalGovernedUniverseCompletenessNotClaimed: true,
    primitiveProofRuleSoundnessNotClaimedHere: true,
  });
  const nf = {
    kind: 'GlobalRowFamilySemanticDerivation0NF',
    version: CHECKER_VERSION,
    family: spec.family,
    nodeId: node.id,
    batchId: spec.batchId,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    selectedRoute: row.SelectedRoute,
    proofRule: spec.proofRule,
    globalNodeDigest: binding.globalNodeDigest,
    rowDigest: binding.rowDigest,
    rowKeyDigest: binding.rowKeyDigest,
    proofRefDigest: binding.proofRefDigest,
    boundsRefDigest: binding.boundsRefDigest,
    checkerContractDigest: binding.checkerContractDigest,
    bindingDigest: binding.bindingDigest,
    rowsAcceptDigest: rowsRecord.Digest ?? rowsRecord.digest,
    familiesAcceptDigest: familiesRecord.Digest ?? familiesRecord.digest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    ready: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function deriveLockedNANDProofRow0({
  contract,
  globalNode,
  gProofNode,
  rowFamGRow,
  certificate,
  binding,
  gpackRecord,
  rowFamGRecord,
}) {
  if (!isPlainObject0(globalNode)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'locked-NAND proof-row coordinate is missing its global node',
      { nodeId: contract.nodeId },
    );
  }
  if (globalNode.id !== contract.nodeId || globalNode.nodeKind !== 'row') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'locked-NAND proof-row global node identity or kind mismatch',
      { expectedId: contract.nodeId, actual: globalNode },
    );
  }
  if (!sameCanonical0(globalNode.premises, contract.globalPremises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'],
      'locked-NAND proof-row global premises must exactly match the phase-35 contract',
      { expected: contract.globalPremises, actual: globalNode.premises },
    );
  }
  if (globalNode.conclusion?.tag !== 'GProofNodeAccepted0'
      || globalNode.conclusion?.rowKind !== contract.rowKind
      || globalNode.conclusion?.theorem !== contract.theorem
      || globalNode.conclusion?.proofRef?.id !== contract.nodeId) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'conclusion'],
      'locked-NAND proof-row global conclusion mismatch',
      { contract, actual: globalNode.conclusion },
    );
  }
  for (const [field, expected] of Object.entries({
    package: 'G',
    rule: contract.rule,
    derivationKind: contract.derivationKind,
    transparentProof: true,
  })) {
    if (globalNode.payload?.[field] !== expected) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'payload', field],
        'locked-NAND proof-row global payload mismatch',
        { field, expected, actual: globalNode.payload?.[field] },
      );
    }
  }

  if (!isPlainObject0(gProofNode)
      || gProofNode.kind !== 'KProofNode0'
      || gProofNode.id !== contract.nodeId
      || gProofNode.refKind !== 'KPrimitive'
      || gProofNode.rowKind !== contract.rowKind
      || gProofNode.rule !== contract.rule
      || gProofNode.mode !== 'full') {
    return validationReject0(
      ['RowFamG', 'GPack', 'PiG', 'proofNodes', contract.nodeId],
      'locked-NAND executable proof node identity or rule mismatch',
      { contract, actual: gProofNode },
    );
  }
  if (!sameCanonical0(gProofNode.premises, contract.gProofPremises)) {
    return validationReject0(
      ['RowFamG', 'GPack', 'PiG', 'proofNodes', contract.nodeId, 'premises'],
      'locked-NAND executable proof-node premise list mismatch',
      { expected: contract.gProofPremises, actual: gProofNode.premises },
    );
  }
  if (gProofNode.conclusion?.kind !== 'GProofConclusion0'
      || gProofNode.conclusion?.rowKind !== contract.rowKind
      || gProofNode.conclusion?.theorem !== contract.theorem
      || gProofNode.conclusion?.accepted !== true
      || gProofNode.payload?.derivationKind !== contract.derivationKind
      || gProofNode.payload?.proofRef?.id !== contract.nodeId) {
    return validationReject0(
      ['RowFamG', 'GPack', 'PiG', 'proofNodes', contract.nodeId],
      'locked-NAND executable proof-node conclusion or derivation payload mismatch',
      { contract, actual: gProofNode },
    );
  }
  if (gProofNode.boundsRef?.id !== `G.${contract.rowKind}.bounds`
      || gProofNode.boundsRef?.finite !== true
      || gProofNode.boundsRef?.polynomial !== true) {
    return validationReject0(
      ['RowFamG', 'GPack', 'PiG', 'proofNodes', contract.nodeId, 'boundsRef'],
      'locked-NAND executable proof-node bounds mismatch',
      { actual: gProofNode.boundsRef },
    );
  }

  if (!isPlainObject0(rowFamGRow)
      || rowFamGRow.rowKind !== contract.rowKind
      || rowFamGRow.rowId !== `G.${contract.rowKind}`
      || rowFamGRow.family !== 'G'
      || rowFamGRow.selectedRoute !== 'Accept'
      || rowFamGRow.proofRef?.id !== contract.nodeId) {
    return validationReject0(
      ['RowFamG', 'rows', contract.rowKind],
      'locked-NAND RowFamG executable row binding mismatch',
      { contract, actual: rowFamGRow },
    );
  }
  if (!isPlainObject0(certificate)
      || certificate.derivation?.kind !== contract.derivationKind
      || certificate.derivation?.rule !== contract.rule
      || certificate.derivation?.proofRef?.id !== contract.nodeId) {
    return validationReject0(
      ['RowFamG', 'GPack', contract.certificateField],
      'locked-NAND certificate derivation binding mismatch',
      { contract, actual: certificate },
    );
  }

  const expectedBinding = makeLockedNANDBinding0({
    contract,
    globalNode,
    gProofNode,
    rowFamGRow,
    certificate,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticRows', 'lockedNANDBindings', contract.index],
      'locked-NAND proof-row binding must exactly match the global node, G proof node, RowFamG row, and certificate',
      { contract, expected: expectedBinding, actual: binding },
    );
  }

  const conclusion = Object.freeze({
    kind: 'GlobalLockedNANDProofRowSemanticConclusion0',
    version: CHECKER_VERSION,
    nodeId: contract.nodeId,
    rowKind: contract.rowKind,
    theorem: contract.theorem,
    rule: contract.rule,
    executableProofNodeRefinementAccepted: true,
    mathematicalTheoremSoundnessNotClaimedHere: true,
  });
  const nf = {
    kind: 'GlobalLockedNANDProofRowSemanticDerivation0NF',
    version: CHECKER_VERSION,
    nodeId: contract.nodeId,
    rowKind: contract.rowKind,
    theorem: contract.theorem,
    rule: contract.rule,
    globalNodeDigest: binding.globalNodeDigest,
    gProofNodeDigest: binding.gProofNodeDigest,
    rowFamGRowDigest: binding.rowFamGRowDigest,
    certificateDigest: binding.certificateDigest,
    checkerContractDigest: binding.checkerContractDigest,
    bindingDigest: binding.bindingDigest,
    gpackAcceptDigest: gpackRecord.Digest ?? gpackRecord.digest,
    rowFamGAcceptDigest: rowFamGRecord.Digest ?? rowFamGRecord.digest,
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
    return validationReject0([], 'global row semantic input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalRowSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global row semantic input kind must be GlobalRowSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global row semantic input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowPack',
    'RowFamG',
    'SemanticRows',
    'Scope',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global row semantic input is missing a required field',
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
    'SemanticRows',
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'global row semantic dependency surfaces must be objects',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global row semantic input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Scope, GLOBAL_ROW_SEMANTIC_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'global row semantic scope must match the bounded executable refinement scope',
      { expected: GLOBAL_ROW_SEMANTIC_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_ROW_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global row semantic policy must match the fail-closed policy',
      { expected: GLOBAL_ROW_SEMANTIC_POLICY0, actual: input.Policy },
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
    'SemanticRows',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global row semantic checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'GlobalRowSemanticInputShape0NF' });
}

function validateSemanticSuite0(suite, input) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticRows'],
      'global row semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const expected = makeGlobalRowSemanticSuite0({
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    RowPack: input.RowPack,
    RowFamG: input.RowFamG,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SemanticRows'],
      'global row semantic suite must exactly match the computed row, global-node, and locked-NAND bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalRowSemanticSuite0NF',
    suiteId: suite.suiteId,
    familyBindingCount: suite.familyBindings.length,
    lockedNANDBindingCount: suite.lockedNANDBindings.length,
    totalBindingCount:
      suite.familyBindings.length + suite.lockedNANDBindings.length,
    familyBindingDigests:
      suite.familyBindings.map((entry) => entry.bindingDigest),
    lockedNANDBindingDigests:
      suite.lockedNANDBindings.map((entry) => entry.bindingDigest),
    scopeDigest: digestCanonical0(suite.Scope),
    policyDigest: digestCanonical0(suite.Policy),
  });
}

function getGProofNodes0(gpack) {
  const piG = gpack?.PiG ?? gpack?.['ΠG'] ?? gpack?.piG;
  return Array.isArray(piG?.proofNodes) ? piG.proofNodes : [];
}

function isInfrastructureAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.globalInfrastructureSemanticReady === true
    && nf?.globalInfrastructureDerivationsReady === true
    && nf?.semanticKBundleFinalReady === true;
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
