import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGlobalProofDAG0,
  GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0,
  GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckKBundleReflectionFinalTheoremReadiness0,
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

const CHECKER_VERSION = 0;

const REQUIRED_EXPANSION_ROOTS0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
]);

const EXECUTABLE_KEYS0 = new Set([
  'exec',
  'execs',
  'execCall',
  'execCalls',
  'call',
  'calls',
  'callee',
  'operator',
  'operation',
  'program',
  'body',
  'macroBody',
  'templateBody',
  'generatedBody',
]);

export const GLOBAL_INFRASTRUCTURE_NODE_IDS0 = Object.freeze([
  'Bounds.Polynomial',
  'NoMin.Global',
  'Mode.Firewall',
  'Import.Acyclic',
]);

export const GLOBAL_INFRASTRUCTURE_POLICY0 = Object.freeze({
  kind: 'GlobalInfrastructureSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresReflectionKBundleFinalReadiness: true,
  requiresLegacyGlobalDAGStructuralAcceptance: true,
  oneDerivationPerInfrastructureCoordinate: true,
  bindsEveryDerivationToGlobalNodeDigest: true,
  bindsEveryDerivationToLedgerDigest: true,
  bindsEveryDerivationToExecutableContractDigest: true,
  polynomialBoundsRecomputed: true,
  noHiddenMinimizationRecomputed: true,
  modeFirewallRecomputed: true,
  importAcyclicityRecomputed: true,
  callerReadinessAssertionsForbidden: true,
  rowPackageAndFinalDerivationsRemainSeparate: true,
});

export const GLOBAL_INFRASTRUCTURE_CONTRACTS0 = Object.freeze({
  'Bounds.Polynomial': Object.freeze({
    kind: 'GlobalInfrastructureCheckerContract0',
    version: CHECKER_VERSION,
    coordinate: 'Bounds.Polynomial',
    nodeKind: 'bounds',
    label: 'PolynomialBounds',
    premises: Object.freeze(['K.IntArith', 'K.DPInd']),
    conclusionTag: 'PolynomialBoundsAccepted0',
    ledgerField: 'BoundsLedger',
    semanticChecker: 'CheckGlobalInfrastructureBounds0',
  }),
  'NoMin.Global': Object.freeze({
    kind: 'GlobalInfrastructureCheckerContract0',
    version: CHECKER_VERSION,
    coordinate: 'NoMin.Global',
    nodeKind: 'nomin',
    label: 'NoHiddenMinGlobal',
    premises: Object.freeze(['K.Record']),
    conclusionTag: 'NoHiddenMinAccepted0',
    ledgerField: 'NoMinLedger',
    semanticChecker: 'CheckGlobalInfrastructureNoMin0',
  }),
  'Mode.Firewall': Object.freeze({
    kind: 'GlobalInfrastructureCheckerContract0',
    version: CHECKER_VERSION,
    coordinate: 'Mode.Firewall',
    nodeKind: 'mode',
    label: 'ModeFirewall',
    premises: Object.freeze(['K.Transport']),
    conclusionTag: 'ModeFirewallAccepted0',
    ledgerField: 'ModeLedger',
    semanticChecker: 'CheckGlobalInfrastructureMode0',
  }),
  'Import.Acyclic': Object.freeze({
    kind: 'GlobalInfrastructureCheckerContract0',
    version: CHECKER_VERSION,
    coordinate: 'Import.Acyclic',
    nodeKind: 'import',
    label: 'ImportAcyclicity',
    premises: Object.freeze(['K.DAGInd']),
    conclusionTag: 'ImportGraphAccepted0',
    ledgerField: 'ImportGraph',
    semanticChecker: 'CheckGlobalInfrastructureImport0',
  }),
});

export function makeGlobalInfrastructureSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  return Object.freeze({
    kind: 'GlobalInfrastructureSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.infrastructure.semantic0',
    derivations: Object.freeze(
      GLOBAL_INFRASTRUCTURE_NODE_IDS0.map((coordinate, index) => {
        const contract = GLOBAL_INFRASTRUCTURE_CONTRACTS0[coordinate];
        const node = nodeById.get(coordinate) ?? null;
        const ledger = LegacyGlobalProofDAG?.[contract.ledgerField] ?? null;
        return makeInfrastructureBinding0({
          index,
          coordinate,
          node,
          ledger,
          contract,
        });
      }),
    ),
    Policy: { ...GLOBAL_INFRASTRUCTURE_POLICY0 },
  });
}

export function makeGlobalInfrastructureSemanticInput0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  SemanticInfrastructure = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalInfrastructureSemanticInput0',
    version: CHECKER_VERSION,
    KBundle,
    LegacyGlobalProofDAG,
    SemanticInfrastructure,
    Policy: { ...GLOBAL_INFRASTRUCTURE_POLICY0 },
  });
}

export async function CheckGlobalInfrastructureSemantic0(input) {
  const checker = 'CheckGlobalInfrastructureSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
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
    bundleFinalCall.ok && isBundleFinalReadyAccept0(bundleFinalCall.record),
    bundleFinalCall.ok ? bundleFinalCall.record : bundleFinalCall.witness,
  ));
  if (!bundleFinalCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle.exception`,
      path: ['KBundle'],
      witness: bundleFinalCall.witness,
      ledger,
    });
  }
  if (!isBundleFinalReadyAccept0(bundleFinalCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle`,
      path: ['KBundle'],
      witness: {
        reason: 'global infrastructure derivations require reflection KBundle final readiness',
        inner: compactRecord0(bundleFinalCall.record),
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
        reason: 'legacy global proof DAG rejected before infrastructure semantic upgrade',
        inner: compactRecord0(legacyCall.record),
      },
      ledger,
    });
  }

  const suite = validateSemanticSuite0(
    input.SemanticInfrastructure,
    input.LegacyGlobalProofDAG,
  );
  ledger.push(makeLedgerEntry0(
    'semanticInfrastructureSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticInfrastructureSuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const checkedDerivations = [];
  for (let index = 0; index < GLOBAL_INFRASTRUCTURE_NODE_IDS0.length; index += 1) {
    const coordinate = GLOBAL_INFRASTRUCTURE_NODE_IDS0[index];
    const contract = GLOBAL_INFRASTRUCTURE_CONTRACTS0[coordinate];
    const binding = input.SemanticInfrastructure.derivations[index];
    const result = checkInfrastructureCoordinate0({
      coordinate,
      contract,
      binding,
      dag: input.LegacyGlobalProofDAG,
      node: nodeById.get(coordinate),
    });
    ledger.push(makeLedgerEntry0(
      `infrastructure.${coordinate}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.infrastructure.${safeCoord0(coordinate)}`,
        result,
        ledger,
      );
    }
    checkedDerivations.push(result.nf);
  }

  const bundleNF = bundleFinalCall.record.NF ?? bundleFinalCall.record.nf ?? {};
  const legacyNF = legacyCall.record.NF ?? legacyCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalInfrastructureSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalInfrastructureSemanticReady: true,
      globalInfrastructureDerivationsReady: true,
      infrastructureCoordinateCount: checkedDerivations.length,
      infrastructureCoordinates: [...GLOBAL_INFRASTRUCTURE_NODE_IDS0],
      infrastructureDerivations: checkedDerivations,
      infrastructureDerivationDigests: checkedDerivations.map((entry) => ({
        coordinate: entry.coordinate,
        nodeId: entry.nodeId,
        digest: entry.derivationDigest,
        nodeDigest: entry.nodeDigest,
        ledgerDigest: entry.ledgerDigest,
        checkerContractDigest: entry.checkerContractDigest,
        conclusionDigest: entry.conclusionDigest,
      })),

      semanticKBundleFinalReady: true,
      semanticKBundleFinalChecker: bundleFinalCall.record.checker,
      semanticKBundleFinalDigest:
        bundleFinalCall.record.Digest ?? bundleFinalCall.record.digest,
      semanticKImplFinalReady:
        bundleNF.computedReadiness?.semanticKImplFinalReady === true,
      semanticK0ConformanceReady:
        bundleNF.computedReadiness?.semanticConformanceReady === true,
      semanticSigmaReady:
        bundleNF.computedReadiness?.semanticSigmaReady === true,
      semanticReflectionReady:
        bundleNF.computedReadiness?.semanticReflectionReady === true,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: legacyCall.record.checker,
      legacyGlobalDAGDigest: legacyCall.record.Digest ?? legacyCall.record.digest,
      legacyGlobalDAGNodeCount: legacyNF.nodeCount ?? null,

      polynomialBoundsReady: true,
      noHiddenMinimizationReady: true,
      modeFirewallReady: true,
      importAcyclicityReady: true,
      globalRowDerivationsReady: false,
      globalPackageDerivationsReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      rowPackageAndFinalDerivationsRemainSeparate: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeInfrastructureBinding0({
  index,
  coordinate,
  node,
  ledger,
  contract,
}) {
  const base = Object.freeze({
    kind: 'GlobalInfrastructureSemanticBinding0',
    version: CHECKER_VERSION,
    index,
    coordinate,
    nodeId: coordinate,
    nodeDigest: digestCanonical0(stripDigestFields0(node)),
    ledgerField: contract.ledgerField,
    ledgerDigest: digestCanonical0(ledger),
    checkerContractDigest: digestCanonical0(contract),
    conclusionDigest: digestCanonical0(node?.conclusion ?? null),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function checkInfrastructureCoordinate0({
  coordinate,
  contract,
  binding,
  dag,
  node,
}) {
  const base = validateInfrastructureNodeBase0({
    coordinate,
    contract,
    node,
  });
  if (!base.ok) return base;

  let detail;
  if (coordinate === 'Bounds.Polynomial') {
    detail = checkBoundsCoordinate0(dag, node);
  } else if (coordinate === 'NoMin.Global') {
    detail = checkNoMinCoordinate0(dag, node);
  } else if (coordinate === 'Mode.Firewall') {
    detail = checkModeCoordinate0(dag, node);
  } else if (coordinate === 'Import.Acyclic') {
    detail = checkImportCoordinate0(dag, node);
  } else {
    return validationReject0(
      ['SemanticInfrastructure', 'coordinate', coordinate],
      'unsupported global infrastructure coordinate',
      { coordinate },
    );
  }
  if (!detail.ok) return detail;

  const conclusion = Object.freeze({
    kind: 'GlobalInfrastructureDerivationConclusion0',
    version: CHECKER_VERSION,
    coordinate,
    nodeId: coordinate,
    semanticProperty: detail.nf.semanticProperty,
    ready: true,
    rowPackageAndFinalDerivationsRemainSeparate: true,
  });
  const nf = {
    kind: 'GlobalInfrastructureSemanticDerivation0NF',
    version: CHECKER_VERSION,
    coordinate,
    nodeId: coordinate,
    nodeDigest: binding.nodeDigest,
    ledgerField: binding.ledgerField,
    ledgerDigest: binding.ledgerDigest,
    checkerContractDigest: binding.checkerContractDigest,
    bindingDigest: binding.bindingDigest,
    semanticChecker: contract.semanticChecker,
    semanticProperty: detail.nf.semanticProperty,
    detail: detail.nf,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    ready: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function validateInfrastructureNodeBase0({ coordinate, contract, node }) {
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate],
      'global infrastructure coordinate is missing its global proof node',
      { coordinate },
    );
  }
  for (const [field, expected] of Object.entries({
    id: coordinate,
    nodeKind: contract.nodeKind,
    label: contract.label,
  })) {
    if (node[field] !== expected) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', coordinate, field],
        'global infrastructure node identity or kind mismatch',
        { coordinate, field, expected, actual: node[field] },
      );
    }
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'premises'],
      'global infrastructure node premise list must exactly match its semantic contract',
      { coordinate, expected: contract.premises, actual: node.premises },
    );
  }
  if (!Array.isArray(node.imports)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'imports'],
      'global infrastructure node imports must be an array',
      { coordinate, actual: typeof node.imports },
    );
  }
  if (node.conclusion?.tag !== contract.conclusionTag) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', coordinate, 'conclusion', 'tag'],
      'global infrastructure node conclusion tag mismatch',
      {
        coordinate,
        expected: contract.conclusionTag,
        actual: node.conclusion?.tag ?? null,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalInfrastructureNodeBase0NF',
    coordinate,
  });
}

function checkBoundsCoordinate0(dag, node) {
  const ledger = dag.BoundsLedger;
  if (!isPlainObject0(ledger)
      || ledger.kind !== 'GlobalBoundsLedger0'
      || ledger.polynomial !== true
      || ledger.finite !== true
      || !Number.isInteger(ledger.exponent)
      || ledger.exponent <= 0) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'BoundsLedger'],
      'global polynomial-bounds ledger must be finite, polynomial, and positively bounded',
      { actual: ledger },
    );
  }
  if (!isPlainObject0(node.bounds)
      || node.bounds.polynomial !== true
      || !Number.isInteger(node.bounds.exponent)
      || node.bounds.exponent !== ledger.exponent) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', node.id, 'bounds'],
      'Bounds.Polynomial node must bind the exact global polynomial exponent',
      { expectedExponent: ledger.exponent, actual: node.bounds },
    );
  }

  let maxNodeExponent = 0;
  const nodeBounds = [];
  for (let index = 0; index < dag.Nodes.length; index += 1) {
    const candidate = dag.Nodes[index];
    const bounds = candidate?.bounds;
    if (!isPlainObject0(bounds) || bounds.polynomial !== true) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', index, 'bounds', 'polynomial'],
        'every global proof node must carry a polynomial bounds record',
        { nodeId: candidate?.id ?? null, actual: bounds },
      );
    }
    const exponent = bounds.exponent ?? 1;
    if (!Number.isInteger(exponent) || exponent <= 0 || exponent > ledger.exponent) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', index, 'bounds', 'exponent'],
        'global proof node exponent must be positive and within the global envelope',
        {
          nodeId: candidate?.id ?? null,
          globalExponent: ledger.exponent,
          actual: exponent,
        },
      );
    }
    maxNodeExponent = Math.max(maxNodeExponent, exponent);
    nodeBounds.push({ id: candidate.id, exponent });
  }

  return validationAccept0({
    kind: 'GlobalInfrastructureBounds0NF',
    semanticProperty: 'polynomial-bounds-envelope',
    globalExponent: ledger.exponent,
    maxNodeExponent,
    nodeCount: dag.Nodes.length,
    nodeBoundsDigest: digestCanonical0(nodeBounds),
    finiteProofUniverse: true,
    polynomialEnvelopeVerified: true,
  });
}

function checkNoMinCoordinate0(dag, node) {
  const ledger = dag.NoMinLedger;
  if (!isPlainObject0(ledger)
      || ledger.kind !== 'GlobalNoMinLedger0'
      || !sameCanonical0(ledger.expanded, REQUIRED_EXPANSION_ROOTS0)
      || !sameCanonical0(
        ledger.forbiddenSymbols,
        GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0,
      )) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'NoMinLedger'],
      'global no-hidden-minimization ledger must bind the exact expansion roots and forbidden symbols',
      {
        expectedExpanded: REQUIRED_EXPANSION_ROOTS0,
        expectedForbiddenSymbols: GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0,
        actual: ledger,
      },
    );
  }
  if (!sameCanonical0(node.conclusion?.expanded, REQUIRED_EXPANSION_ROOTS0)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', node.id, 'conclusion', 'expanded'],
      'NoMin.Global conclusion must bind the exact expansion roots',
      { expected: REQUIRED_EXPANSION_ROOTS0, actual: node.conclusion?.expanded },
    );
  }

  const hit = findForbiddenExecutableUse0(dag, ['LegacyGlobalProofDAG'], false);
  if (hit !== null) {
    return validationReject0(
      hit.path,
      'forbidden minimization symbol appears in an executable global-DAG position',
      hit,
    );
  }
  const scan = summarizeExecutableScan0(dag);
  return validationAccept0({
    kind: 'GlobalInfrastructureNoMin0NF',
    semanticProperty: 'expanded-no-hidden-minimization',
    expandedRoots: [...REQUIRED_EXPANSION_ROOTS0],
    forbiddenSymbols: [...GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0],
    forbiddenHitCount: 0,
    executableValueCount: scan.executableValueCount,
    scannedObjectCount: scan.scannedObjectCount,
    scanDigest: digestCanonical0(scan),
  });
}

function checkModeCoordinate0(dag, node) {
  const ledger = dag.ModeLedger;
  if (!isPlainObject0(ledger)
      || ledger.kind !== 'GlobalModeLedger0'
      || ledger.quotientNotReplacement !== true
      || ledger.constructiveFirewall !== true) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'ModeLedger'],
      'global mode ledger must enforce quotient-not-replacement and constructive firewall safety',
      { actual: ledger },
    );
  }
  if (node.conclusion?.quotientNotReplacement !== true) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', node.id, 'conclusion', 'quotientNotReplacement'],
      'Mode.Firewall conclusion must enforce quotient-not-replacement',
      { actual: node.conclusion },
    );
  }

  let fullNodeCount = 0;
  let quotientNodeCount = 0;
  const modeSummary = [];
  for (let index = 0; index < dag.Nodes.length; index += 1) {
    const candidate = dag.Nodes[index];
    const mode = String(candidate?.mode ?? candidate?.Mode ?? 'Full')
      .trim()
      .toLowerCase();
    if (!['full', 'quot'].includes(mode)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', index, 'mode'],
        'semantic mode derivation accepts only Full or Quot node modes',
        { nodeId: candidate?.id ?? null, actual: candidate?.mode },
      );
    }
    const payload = candidate?.payload ?? candidate?.Payload ?? {};
    if (mode === 'quot') {
      quotientNodeCount += 1;
      if (candidate.nodeKind === 'package' || candidate.nodeKind === 'final') {
        return validationReject0(
          ['LegacyGlobalProofDAG', 'Nodes', index, 'mode'],
          'package and final theorem nodes cannot be justified only in quotient mode',
          { nodeId: candidate.id, nodeKind: candidate.nodeKind },
        );
      }
      if (isPlainObject0(payload)
          && (
            payload.constructiveFullReplacement === true
            || payload.replacementEquality === true
            || payload.fullModeConstruction === true
          )) {
        return validationReject0(
          ['LegacyGlobalProofDAG', 'Nodes', index, 'payload'],
          'quotient proof node cannot construct a full-mode replacement',
          { nodeId: candidate.id },
        );
      }
    } else {
      fullNodeCount += 1;
    }
    modeSummary.push({ id: candidate.id, mode });
  }

  return validationAccept0({
    kind: 'GlobalInfrastructureMode0NF',
    semanticProperty: 'quotient-not-constructive-firewall',
    fullNodeCount,
    quotientNodeCount,
    nodeCount: dag.Nodes.length,
    quotientNotReplacement: true,
    constructiveFirewall: true,
    modeSummaryDigest: digestCanonical0(modeSummary),
  });
}

function checkImportCoordinate0(dag, node) {
  const graphRecord = dag.ImportGraph;
  if (!isPlainObject0(graphRecord)
      || graphRecord.kind !== 'GlobalImportGraph0'
      || graphRecord.acyclic !== true
      || !sameCanonical0(
        graphRecord.forbiddenEdges,
        GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0,
      )
      || !Array.isArray(graphRecord.edges)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'ImportGraph'],
      'global import graph must bind the exact forbidden-edge policy and an explicit edge list',
      { actual: graphRecord },
    );
  }
  if (node.conclusion?.acyclic !== true
      || !sameCanonical0(
        node.conclusion?.forbiddenEdges,
        GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0,
      )) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', node.id, 'conclusion'],
      'Import.Acyclic conclusion must bind acyclicity and the exact forbidden-edge policy',
      { actual: node.conclusion },
    );
  }

  const forbidden = new Set(
    GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge)),
  );
  const normalizedEdges = [];
  for (let index = 0; index < graphRecord.edges.length; index += 1) {
    const edge = normalizeImportEdge0(graphRecord.edges[index]);
    if (edge === null) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'ImportGraph', 'edges', index],
        'global import edge must expose from and to endpoints',
        { actual: graphRecord.edges[index] },
      );
    }
    if (edge.from === edge.to) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'ImportGraph', 'edges', index],
        'global import graph rejects self-import edges',
        { edge },
      );
    }
    if (forbidden.has(edgeKey0(edge))) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'ImportGraph', 'edges', index],
        'global import graph contains a forbidden package edge',
        { edge },
      );
    }
    normalizedEdges.push(edge);
  }

  const packageGraph = makeAdjacency0(normalizedEdges);
  const packageCycle = findCycle0(packageGraph);
  if (packageCycle !== null) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'ImportGraph', 'cycle'],
      'global package import graph contains a cycle',
      { cycle: packageCycle },
    );
  }

  const nodeIdSet = new Set(dag.Nodes.map((candidate) => candidate.id));
  const nodeGraph = new Map();
  const topologicalOrder = [];
  for (let index = 0; index < dag.Nodes.length; index += 1) {
    const candidate = dag.Nodes[index];
    topologicalOrder.push(candidate.id);
    const deps = [];
    for (const ref of [...(candidate.premises ?? []), ...(candidate.imports ?? [])]) {
      const id = normalizeRefId0(ref);
      if (!isNonEmptyString0(id)) {
        return validationReject0(
          ['LegacyGlobalProofDAG', 'Nodes', index, 'imports'],
          'global proof dependency must resolve to a non-empty node id',
          { nodeId: candidate.id, ref },
        );
      }
      if (!nodeIdSet.has(id)) {
        return validationReject0(
          ['LegacyGlobalProofDAG', 'Nodes', index, 'imports'],
          'global proof dependency must resolve to a declared node',
          { nodeId: candidate.id, dependency: id },
        );
      }
      deps.push(id);
    }
    nodeGraph.set(candidate.id, deps);
  }
  const nodeCycle = findCycle0(nodeGraph);
  if (nodeCycle !== null) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', 'cycle'],
      'global proof dependency graph contains a cycle',
      { cycle: nodeCycle },
    );
  }

  return validationAccept0({
    kind: 'GlobalInfrastructureImport0NF',
    semanticProperty: 'global-import-acyclicity',
    explicitImportEdgeCount: normalizedEdges.length,
    nodeDependencyCount: [...nodeGraph.values()].reduce(
      (sum, deps) => sum + deps.length,
      0,
    ),
    forbiddenEdges: GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0.map((edge) => [...edge]),
    packageImportAcyclic: true,
    nodeDependencyAcyclic: true,
    topologicalOrder,
    topologicalOrderDigest: digestCanonical0(topologicalOrder),
    importEdgesDigest: digestCanonical0(normalizedEdges),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'global infrastructure semantic input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalInfrastructureSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global infrastructure semantic input kind must be GlobalInfrastructureSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global infrastructure semantic input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'SemanticInfrastructure',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global infrastructure semantic input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)
      || !isPlainObject0(input.LegacyGlobalProofDAG)
      || !isPlainObject0(input.SemanticInfrastructure)) {
    return validationReject0(
      ['input'],
      'global infrastructure semantic dependency surfaces must be objects',
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global infrastructure semantic input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_INFRASTRUCTURE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global infrastructure semantic policy must match the fail-closed policy',
      { expected: GLOBAL_INFRASTRUCTURE_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'KBundle',
    'LegacyGlobalProofDAG',
    'SemanticInfrastructure',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global infrastructure semantic checker rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalInfrastructureSemanticInputShape0NF',
  });
}

function validateSemanticSuite0(suite, dag) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticInfrastructure'],
      'global infrastructure semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind', 'version', 'suiteId', 'derivations', 'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticInfrastructure', unexpected[0]],
      'global infrastructure semantic suite rejects caller-supplied truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalInfrastructureSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || !isNonEmptyString0(suite.suiteId)) {
    return validationReject0(
      ['SemanticInfrastructure'],
      'global infrastructure semantic suite kind, version, or suiteId is invalid',
      { actual: suite },
    );
  }
  if (!Array.isArray(suite.derivations)
      || suite.derivations.length !== GLOBAL_INFRASTRUCTURE_NODE_IDS0.length) {
    return validationReject0(
      ['SemanticInfrastructure', 'derivations'],
      'global infrastructure suite must provide exactly one binding per infrastructure coordinate',
      {
        expected: GLOBAL_INFRASTRUCTURE_NODE_IDS0.length,
        actual: suite.derivations?.length,
      },
    );
  }
  if (!sameCanonical0(suite.Policy, GLOBAL_INFRASTRUCTURE_POLICY0)) {
    return validationReject0(
      ['SemanticInfrastructure', 'Policy'],
      'global infrastructure semantic suite policy mismatch',
      { expected: GLOBAL_INFRASTRUCTURE_POLICY0, actual: suite.Policy },
    );
  }

  const expectedSuite = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG: dag,
  });
  for (let index = 0; index < GLOBAL_INFRASTRUCTURE_NODE_IDS0.length; index += 1) {
    const actual = suite.derivations[index];
    const expected = expectedSuite.derivations[index];
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        ['SemanticInfrastructure', 'derivations', index],
        'global infrastructure binding must exactly match the computed node, ledger, and executable contract binding',
        {
          coordinate: GLOBAL_INFRASTRUCTURE_NODE_IDS0[index],
          expected,
          actual,
        },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalInfrastructureSemanticSuite0NF',
    suiteId: suite.suiteId,
    derivationCount: suite.derivations.length,
    coordinates: [...GLOBAL_INFRASTRUCTURE_NODE_IDS0],
    bindingDigests: suite.derivations.map((entry) => entry.bindingDigest),
    policyDigest: digestCanonical0(suite.Policy),
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition
        && GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
      return { symbol: value, path };
    }
    return null;
  }
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findForbiddenExecutableUse0(
        value[index],
        [...path, index],
        inExecutablePosition,
      );
      if (hit !== null) return hit;
    }
    return null;
  }
  if (!isPlainObject0(value)) return null;
  for (const key of Object.keys(value)) {
    const nextExecutablePosition = inExecutablePosition
      || EXECUTABLE_KEYS0.has(key)
      || /exec|call|program|body|operator|operation/i.test(key);
    const hit = findForbiddenExecutableUse0(
      value[key],
      [...path, key],
      nextExecutablePosition,
    );
    if (hit !== null) return hit;
  }
  return null;
}

function summarizeExecutableScan0(value) {
  let scannedObjectCount = 0;
  let executableValueCount = 0;
  function visit(current, inExecutablePosition = false) {
    if (typeof current === 'string') {
      if (inExecutablePosition) executableValueCount += 1;
      return;
    }
    if (Array.isArray(current)) {
      for (const entry of current) visit(entry, inExecutablePosition);
      return;
    }
    if (!isPlainObject0(current)) return;
    scannedObjectCount += 1;
    for (const key of Object.keys(current)) {
      const nextExecutablePosition = inExecutablePosition
        || EXECUTABLE_KEYS0.has(key)
        || /exec|call|program|body|operator|operation/i.test(key);
      visit(current[key], nextExecutablePosition);
    }
  }
  visit(value, false);
  return { scannedObjectCount, executableValueCount };
}

function stripDigestFields0(value) {
  if (!isPlainObject0(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
}

function normalizeImportEdge0(edge) {
  if (Array.isArray(edge) && edge.length >= 2) {
    return { from: String(edge[0]), to: String(edge[1]) };
  }
  if (isPlainObject0(edge)) {
    const from = edge.from ?? edge.src;
    const to = edge.to ?? edge.dst;
    if (from !== undefined && to !== undefined) {
      return { from: String(from), to: String(to) };
    }
  }
  return null;
}

function normalizeRefId0(ref) {
  if (typeof ref === 'string') return ref;
  if (isPlainObject0(ref)) {
    return ref.id ?? ref.ref ?? ref.nodeId ?? ref.NodeID ?? null;
  }
  return null;
}

function edgeKey0(edge) {
  return Array.isArray(edge)
    ? `${String(edge[0])}->${String(edge[1])}`
    : `${String(edge.from)}->${String(edge.to)}`;
}

function makeAdjacency0(edges) {
  const graph = new Map();
  for (const edge of edges) {
    if (!graph.has(edge.from)) graph.set(edge.from, []);
    if (!graph.has(edge.to)) graph.set(edge.to, []);
    graph.get(edge.from).push(edge.to);
  }
  return graph;
}

function findCycle0(graph) {
  const visiting = new Set();
  const visited = new Set();
  function visit(nodeId, path) {
    if (visiting.has(nodeId)) return [...path, nodeId];
    if (visited.has(nodeId)) return null;
    visiting.add(nodeId);
    for (const next of graph.get(nodeId) ?? []) {
      const hit = visit(next, [...path, nodeId]);
      if (hit !== null) return hit;
    }
    visiting.delete(nodeId);
    visited.add(nodeId);
    return null;
  }
  for (const nodeId of graph.keys()) {
    const hit = visit(nodeId, []);
    if (hit !== null) return hit;
  }
  return null;
}

function isBundleFinalReadyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true
    && nf?.computedReadiness?.semanticReflectionReady === true;
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

function isNonEmptyString0(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
