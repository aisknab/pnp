import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  KERNEL_RULES0,
  SIGMA_REQUIRED_THEOREMS0,
  REFLECTION_REQUIRED_CHECKERS0,
} from './pcc-kimpl0.mjs';

import {
  ROW_REQUIRED_FAMILIES0,
  ROW_BATCH_IDS0,
} from './pcc-rows0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_NODE_KINDS0 = Object.freeze([
  'kernel',
  'sigma',
  'row',
  'package',
  'reflection',
  'bounds',
  'nomin',
  'mode',
  'import',
  'final',
]);

export const GLOBAL_DAG_REQUIRED_FINALS0 = Object.freeze([
  'Final.PackageSoundness',
  'Final.GeneratedPackageSufficiency',
  'Final.AcceptedPackageImpliesSATinP',
  'Final.AcceptedPackageImpliesPEqualsNP',
]);

export const GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0 = Object.freeze([
  'E.VerifyDWSoundness',
  'N.TraceableNormalization',
  'Splice.BoundedAndComposed',
  'FT.FiniteTableCoverage',
  'X.CriticalWindowRouting',
  'BC.BranchCycleRouting',
  'UN.UnaryDecoderRouting',
  'HN.LeafTightness',
  'HResolve.GlobalHereditaryResolver',
  'BUD.BudgetResolver',
  'NORFF.FrontierFaithfulComparison',
  'RW.BCELReady',
  'BN2.SideTightCoherentOptimum',
  'BN3.SimultaneousEnvelope',
  'BN4.ActivationExact',
  'BN5.FullShadowLocalization',
  'PkgC.SeparatingConsumers',
  'BN6.HypergraphPacket',
  'Packet.SelectorSeeds',
  'R.SelectorRealization',
  'HB.NegativeClosure',
  'O.ZeroSlackOracle',
  'G.LockedNANDThreshold',
  'Final.FrameworkMatch',
  'PACK.PackageSufficiency',
]);

export const GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
  'µ',
  'µ*',
  'µ#',
  'Can',
  'argmin',
  'maxG',
  'minimumEquivalent',
  'optimalCircuit',
  'exactMinSearch',
  'canonicalMinimizer',
  'maximizeGain',
]);

export const GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0 = Object.freeze([
  Object.freeze(['BC', 'UN']),
  Object.freeze(['UN', 'BC']),
  Object.freeze(['BCEL', 'R']),
  Object.freeze(['BUD', 'R']),
  Object.freeze(['O', 'G']),
  Object.freeze(['G', 'O']),
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

export function makeGlobalProofDAGNode0({
  id,
  kind,
  label = id,
  premises = [],
  imports = [],
  mode = 'Full',
  conclusion = {
    tag: 'GlobalConclusion0',
    id,
  },
  payload = {},
  bounds = {
    polynomial: true,
    exponent: 6,
  },
  route = null,
  rank = null,
}) {
  if (!isNonEmptyString(id)) {
    throw new TypeError('makeGlobalProofDAGNode0 requires a non-empty id');
  }

  if (!GLOBAL_DAG_NODE_KINDS0.includes(kind)) {
    throw new TypeError(`unknown global DAG node kind: ${String(kind)}`);
  }

  const node = {
    kind: 'GlobalProofNode0',
    version: CHECKER_VERSION,
    id,
    nodeKind: kind,
    label,
    premises,
    imports,
    mode,
    conclusion,
    payload,
    bounds,
    route,
    rank,
  };

  return {
    ...node,
    Digest: digestCanonical0(node),
  };
}

export function makeSyntheticGlobalProofDAG0(overrides = {}) {
  const nodes = [];

  for (const rule of KERNEL_RULES0) {
    nodes.push(makeGlobalProofDAGNode0({
      id: `K.${rule}`,
      kind: 'kernel',
      label: rule,
      conclusion: {
        tag: 'KernelRuleAccepted0',
        rule,
      },
    }));
  }

  for (const theorem of SIGMA_REQUIRED_THEOREMS0) {
    nodes.push(makeGlobalProofDAGNode0({
      id: `Sigma.${theorem}`,
      kind: 'sigma',
      label: theorem,
      premises: [
        'K.FiniteRel',
        'K.IntArith',
      ],
      conclusion: {
        tag: 'SigmaTheoremAccepted0',
        theorem,
      },
    }));
  }

  for (const checker of REFLECTION_REQUIRED_CHECKERS0) {
    nodes.push(makeGlobalProofDAGNode0({
      id: `Reflection.${checker}`,
      kind: 'reflection',
      label: checker,
      premises: [
        'K.Record',
        'K.Transport',
      ],
      conclusion: {
        tag: 'ReflectionAccepted0',
        checker,
      },
    }));
  }

  for (const family of ROW_REQUIRED_FAMILIES0) {
    nodes.push(makeGlobalProofDAGNode0({
      id: `Row.${family}`,
      kind: 'row',
      label: family,
      premises: [
        'K.Record',
        'K.Transport',
      ],
      conclusion: {
        tag: 'RowFamilyAccepted0',
        family,
      },
    }));
  }

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Bounds.Polynomial',
    kind: 'bounds',
    label: 'PolynomialBounds',
    premises: [
      'K.IntArith',
      'K.DPInd',
    ],
    conclusion: {
      tag: 'PolynomialBoundsAccepted0',
    },
    bounds: {
      polynomial: true,
      exponent: 8,
    },
  }));

  nodes.push(makeGlobalProofDAGNode0({
    id: 'NoMin.Global',
    kind: 'nomin',
    label: 'NoHiddenMinGlobal',
    premises: [
      'K.Record',
    ],
    conclusion: {
      tag: 'NoHiddenMinAccepted0',
      expanded: [
        'macros',
        'aliases',
        'generatedTemplates',
        'imports',
      ],
    },
  }));

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Mode.Firewall',
    kind: 'mode',
    label: 'ModeFirewall',
    premises: [
      'K.Transport',
    ],
    conclusion: {
      tag: 'ModeFirewallAccepted0',
      quotientNotReplacement: true,
    },
  }));

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Import.Acyclic',
    kind: 'import',
    label: 'ImportAcyclicity',
    premises: [
      'K.DAGInd',
    ],
    conclusion: {
      tag: 'ImportGraphAccepted0',
      acyclic: true,
      forbiddenEdges: GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0,
    },
  }));

  for (const theorem of GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0) {
    nodes.push(makeGlobalProofDAGNode0({
      id: `Package.${theorem}`,
      kind: 'package',
      label: theorem,
      premises: [
        'Bounds.Polynomial',
        'NoMin.Global',
        'Mode.Firewall',
        'Import.Acyclic',
      ],
      conclusion: {
        tag: 'PackageTheoremAccepted0',
        theorem,
      },
    }));
  }

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Final.PackageSoundness',
    kind: 'final',
    label: 'Final.PackageSoundness',
    premises: [
      'Package.PACK.PackageSufficiency',
    ],
    conclusion: {
      tag: 'FinalTheoremAccepted0',
      theorem: 'Final.PackageSoundness',
    },
  }));

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Final.GeneratedPackageSufficiency',
    kind: 'final',
    label: 'Final.GeneratedPackageSufficiency',
    premises: [
      'Final.PackageSoundness',
    ],
    conclusion: {
      tag: 'FinalTheoremAccepted0',
      theorem: 'Final.GeneratedPackageSufficiency',
    },
  }));

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Final.AcceptedPackageImpliesSATinP',
    kind: 'final',
    label: 'Final.AcceptedPackageImpliesSATinP',
    premises: [
      'Package.G.LockedNANDThreshold',
      'Package.O.ZeroSlackOracle',
      'Final.GeneratedPackageSufficiency',
    ],
    conclusion: {
      tag: 'FinalTheoremAccepted0',
      theorem: 'Final.AcceptedPackageImpliesSATinP',
    },
  }));

  nodes.push(makeGlobalProofDAGNode0({
    id: 'Final.AcceptedPackageImpliesPEqualsNP',
    kind: 'final',
    label: 'Final.AcceptedPackageImpliesPEqualsNP',
    premises: [
      'Final.AcceptedPackageImpliesSATinP',
    ],
    conclusion: {
      tag: 'FinalTheoremAccepted0',
      theorem: 'Final.AcceptedPackageImpliesPEqualsNP',
    },
  }));

  const dag = {
    kind: 'GlobalProofDAG0',
    version: CHECKER_VERSION,
    SchedHash: {
      alg: 'SHA256',
      hex: 'sched.synthetic',
    },
    IfaceHash: {
      alg: 'SHA256',
      hex: 'iface.synthetic',
    },
    BatchIDs: ROW_BATCH_IDS0,
    Nodes: nodes,
    ImportGraph: {
      kind: 'GlobalImportGraph0',
      acyclic: true,
      forbiddenEdges: GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0,
      edges: [],
    },
    ModeLedger: {
      kind: 'GlobalModeLedger0',
      quotientNotReplacement: true,
      constructiveFirewall: true,
    },
    BoundsLedger: {
      kind: 'GlobalBoundsLedger0',
      polynomial: true,
      finite: true,
      exponent: 8,
    },
    NoMinLedger: {
      kind: 'GlobalNoMinLedger0',
      expanded: [
        'macros',
        'aliases',
        'generatedTemplates',
        'imports',
      ],
      forbiddenSymbols: GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0,
    },
    PiGlobalDAG: {
      kind: 'PiGlobalDAG0',
      version: CHECKER_VERSION,
      note: 'synthetic global proof DAG witness',
    },
  };

  return {
    ...dag,
    ...overrides,
  };
}

export async function CheckGlobalProofDAG0(dag) {
  const checker = 'CheckGlobalProofDAG0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateGlobalDAGShape0(dag)],
    ['nodes', `${checker}.nodes`, () => validateGlobalNodes0(dag.Nodes)],
    ['coverage', `${checker}.coverage`, () => validateGlobalCoverage0(dag)],
    ['imports', `${checker}.imports`, () => validateGlobalImports0(dag)],
    ['mode', `${checker}.mode`, () => validateGlobalMode0(dag)],
    ['bounds', `${checker}.bounds`, () => validateGlobalBounds0(dag)],
    ['nomin', `${checker}.noHiddenMin`, () => validateGlobalNoHiddenMin0(dag)],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(dag, ['GlobalProofDAG0'])],
    ['digests', `${checker}.digests`, () => validateNodeDigests0(dag.Nodes)],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'GlobalProofDAG0NF',
    checker,
    version: CHECKER_VERSION,
    nodeCount: dag.Nodes.length,
    nodeKinds: summarizeKinds0(dag.Nodes),
    kernelRuleCount: KERNEL_RULES0.length,
    sigmaTheoremCount: SIGMA_REQUIRED_THEOREMS0.length,
    rowFamilyCount: ROW_REQUIRED_FAMILIES0.length,
    packageTheoremCount: GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.length,
    finalTheorems: GLOBAL_DAG_REQUIRED_FINALS0,
    piGlobalDAGDigest: digestCanonical0(getPiGlobalDAG0(dag)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateGlobalDAGShape0(dag) {
  if (!isPlainObject(dag)) {
    return validationReject0([], 'GlobalProofDAG0 must be an object', {
      actual: typeof dag,
    });
  }

  if (dag.kind !== undefined && dag.kind !== 'GlobalProofDAG0') {
    return validationReject0(['kind'], 'GlobalProofDAG0 kind must be GlobalProofDAG0 when present', {
      actual: dag.kind,
    });
  }

  if (dag.version !== undefined && dag.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `GlobalProofDAG0 version must be ${CHECKER_VERSION} when present`, {
      actual: dag.version,
    });
  }

  for (const field of [
    'SchedHash',
    'IfaceHash',
    'Nodes',
    'ImportGraph',
    'ModeLedger',
    'BoundsLedger',
    'NoMinLedger',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(dag, field)) {
      return validationReject0([field], 'GlobalProofDAG0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(dag.Nodes)) {
    return validationReject0(['Nodes'], 'GlobalProofDAG0 Nodes must be an array', {
      actual: typeof dag.Nodes,
    });
  }

  if (getPiGlobalDAG0(dag) === undefined) {
    return validationReject0(['PiGlobalDAG'], 'GlobalProofDAG0 is missing PiGlobalDAG or Πglobal', null);
  }

  return validationAccept0({
    kind: 'GlobalProofDAGShape0NF',
  });
}

function validateGlobalNodes0(nodes) {
  const accepted = new Set();

  for (let index = 0; index < nodes.length; index += 1) {
    const node = nodes[index];

    if (!isPlainObject(node)) {
      return validationReject0(['Nodes', index], 'global proof node must be an object', {
        actual: typeof node,
      });
    }

    if (!isNonEmptyString(node.id)) {
      return validationReject0(['Nodes', index, 'id'], 'global proof node must have a non-empty id', {
        actual: node.id,
      });
    }

    if (accepted.has(node.id)) {
      return validationReject0(['Nodes', index, 'id'], 'global proof node ids must be unique', {
        id: node.id,
      });
    }

    if (!GLOBAL_DAG_NODE_KINDS0.includes(node.nodeKind)) {
      return validationReject0(['Nodes', index, 'nodeKind'], 'global proof node has an unknown node kind', {
        nodeKind: node.nodeKind,
      });
    }

    if (!Array.isArray(node.premises)) {
      return validationReject0(['Nodes', index, 'premises'], 'global proof node premises must be an array', null);
    }

    for (let premiseIndex = 0; premiseIndex < node.premises.length; premiseIndex += 1) {
      const premiseId = normalizeRefId0(node.premises[premiseIndex]);

      if (!isNonEmptyString(premiseId)) {
        return validationReject0(['Nodes', index, 'premises', premiseIndex], 'premise must resolve to a non-empty id', {
          premise: node.premises[premiseIndex],
        });
      }

      if (!accepted.has(premiseId)) {
        return validationReject0(['Nodes', index, 'premises', premiseIndex], 'premise must reference an earlier global proof node', {
          nodeId: node.id,
          premiseId,
        });
      }
    }

    if (!Array.isArray(node.imports)) {
      return validationReject0(['Nodes', index, 'imports'], 'global proof node imports must be an array', null);
    }

    if (node.conclusion === undefined) {
      return validationReject0(['Nodes', index, 'conclusion'], 'global proof node must have a conclusion', {
        nodeId: node.id,
      });
    }

    const modeResult = validateNodeMode0(node, ['Nodes', index]);

    if (!modeResult.ok) {
      return modeResult;
    }

    const boundsResult = validateNodeBounds0(node, ['Nodes', index]);

    if (!boundsResult.ok) {
      return boundsResult;
    }

    const routeResult = validateNodeRoute0(node, ['Nodes', index]);

    if (!routeResult.ok) {
      return routeResult;
    }

    const rankResult = validateNodeRank0(node, ['Nodes', index]);

    if (!rankResult.ok) {
      return rankResult;
    }

    accepted.add(node.id);
  }

  return validationAccept0({
    kind: 'GlobalNodes0NF',
    nodeCount: nodes.length,
  });
}

function validateGlobalCoverage0(dag) {
  const nodes = dag.Nodes;
  const ids = new Set(nodes.map((node) => node.id));
  const labels = new Set(nodes.map((node) => String(node.label ?? node.id)));

  for (const kind of GLOBAL_DAG_NODE_KINDS0) {
    if (!nodes.some((node) => node.nodeKind === kind)) {
      return validationReject0(['Nodes', 'coverage', kind], 'GlobalProofDAG0 is missing a required node kind', {
        kind,
      });
    }
  }

  for (const rule of KERNEL_RULES0) {
    if (!ids.has(`K.${rule}`) && !labels.has(rule)) {
      return validationReject0(['Nodes', 'coverage', 'kernel', rule], 'GlobalProofDAG0 is missing a kernel primitive rule node', {
        rule,
      });
    }
  }

  for (const theorem of SIGMA_REQUIRED_THEOREMS0) {
    if (!ids.has(`Sigma.${theorem}`) && !labels.has(theorem)) {
      return validationReject0(['Nodes', 'coverage', 'sigma', theorem], 'GlobalProofDAG0 is missing a required Sigma theorem node', {
        theorem,
      });
    }
  }

  for (const checker of REFLECTION_REQUIRED_CHECKERS0) {
    if (!ids.has(`Reflection.${checker}`) && !labels.has(checker)) {
      return validationReject0(['Nodes', 'coverage', 'reflection', checker], 'GlobalProofDAG0 is missing a checker reflection node', {
        checker,
      });
    }
  }

  for (const family of ROW_REQUIRED_FAMILIES0) {
    if (!ids.has(`Row.${family}`) && !labels.has(family)) {
      return validationReject0(['Nodes', 'coverage', 'row', family], 'GlobalProofDAG0 is missing a row-family proof node', {
        family,
      });
    }
  }

  for (const theorem of GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0) {
    if (!ids.has(`Package.${theorem}`) && !labels.has(theorem)) {
      return validationReject0(['Nodes', 'coverage', 'package', theorem], 'GlobalProofDAG0 is missing a required package theorem node', {
        theorem,
      });
    }
  }

  for (const theorem of GLOBAL_DAG_REQUIRED_FINALS0) {
    if (!ids.has(theorem) && !labels.has(theorem)) {
      return validationReject0(['Nodes', 'coverage', 'final', theorem], 'GlobalProofDAG0 is missing a required final theorem node', {
        theorem,
      });
    }
  }

  return validationAccept0({
    kind: 'GlobalCoverage0NF',
    nodeKindCount: GLOBAL_DAG_NODE_KINDS0.length,
    kernelRuleCount: KERNEL_RULES0.length,
    rowFamilyCount: ROW_REQUIRED_FAMILIES0.length,
    packageTheoremCount: GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.length,
    finalTheoremCount: GLOBAL_DAG_REQUIRED_FINALS0.length,
  });
}

function validateGlobalImports0(dag) {
  if (!isPlainObject(dag.ImportGraph)) {
    return validationReject0(['ImportGraph'], 'ImportGraph must be an object', {
      actual: typeof dag.ImportGraph,
    });
  }

  if (dag.ImportGraph.acyclic === false) {
    return validationReject0(['ImportGraph', 'acyclic'], 'ImportGraph must be acyclic', null);
  }

  const edges = dag.ImportGraph.edges ?? [];
  const forbidden = new Set(GLOBAL_DAG_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge)));

  if (!Array.isArray(edges)) {
    return validationReject0(['ImportGraph', 'edges'], 'ImportGraph edges must be an array', null);
  }

  for (let index = 0; index < edges.length; index += 1) {
    const edge = normalizeImportEdge0(edges[index]);

    if (edge === null) {
      return validationReject0(['ImportGraph', 'edges', index], 'ImportGraph edge must have from and to endpoints', {
        edge: edges[index],
      });
    }

    if (forbidden.has(edgeKey0([edge.from, edge.to]))) {
      return validationReject0(['ImportGraph', 'edges', index], 'ImportGraph contains a forbidden package edge', {
        edge,
      });
    }
  }

  const graph = new Map();

  for (const node of dag.Nodes) {
    graph.set(node.id, node.premises.map((premise) => normalizeRefId0(premise)));
  }

  const cycle = findCycle0(graph);

  if (cycle !== null) {
    return validationReject0(['Nodes', 'cycle'], 'GlobalProofDAG0 contains a cycle', {
      cycle,
    });
  }

  return validationAccept0({
    kind: 'GlobalImports0NF',
    edgeCount: edges.length,
  });
}

function validateGlobalMode0(dag) {
  if (!isPlainObject(dag.ModeLedger)) {
    return validationReject0(['ModeLedger'], 'ModeLedger must be an object', {
      actual: typeof dag.ModeLedger,
    });
  }

  if (dag.ModeLedger.quotientNotReplacement !== true) {
    return validationReject0(['ModeLedger', 'quotientNotReplacement'], 'ModeLedger must enforce quotient-not-replacement', null);
  }

  if (dag.ModeLedger.constructiveFirewall !== true) {
    return validationReject0(['ModeLedger', 'constructiveFirewall'], 'ModeLedger must enforce constructive firewall safety', null);
  }

  for (let index = 0; index < dag.Nodes.length; index += 1) {
    const result = validateNodeMode0(dag.Nodes[index], ['Nodes', index]);

    if (!result.ok) {
      return result;
    }
  }

  return validationAccept0({
    kind: 'GlobalMode0NF',
  });
}

function validateGlobalBounds0(dag) {
  if (!isPlainObject(dag.BoundsLedger)) {
    return validationReject0(['BoundsLedger'], 'BoundsLedger must be an object', {
      actual: typeof dag.BoundsLedger,
    });
  }

  if (dag.BoundsLedger.polynomial !== true) {
    return validationReject0(['BoundsLedger', 'polynomial'], 'BoundsLedger must enforce polynomial bounds', null);
  }

  if (dag.BoundsLedger.finite !== true) {
    return validationReject0(['BoundsLedger', 'finite'], 'BoundsLedger must enforce finite proof universes', null);
  }

  if (!Number.isInteger(dag.BoundsLedger.exponent) || dag.BoundsLedger.exponent <= 0) {
    return validationReject0(['BoundsLedger', 'exponent'], 'BoundsLedger exponent must be a positive integer', {
      actual: dag.BoundsLedger.exponent,
    });
  }

  for (let index = 0; index < dag.Nodes.length; index += 1) {
    const result = validateNodeBounds0(dag.Nodes[index], ['Nodes', index]);

    if (!result.ok) {
      return result;
    }
  }

  return validationAccept0({
    kind: 'GlobalBounds0NF',
    exponent: dag.BoundsLedger.exponent,
  });
}

function validateGlobalNoHiddenMin0(dag) {
  if (!isPlainObject(dag.NoMinLedger)) {
    return validationReject0(['NoMinLedger'], 'NoMinLedger must be an object', {
      actual: typeof dag.NoMinLedger,
    });
  }

  if (!arrayContainsAll0(dag.NoMinLedger.expanded, [
    'macros',
    'aliases',
    'generatedTemplates',
    'imports',
  ])) {
    return validationReject0(['NoMinLedger', 'expanded'], 'NoMinLedger must expand macros, aliases, generated templates, and imports', {
      actual: dag.NoMinLedger.expanded,
    });
  }

  if (!arrayContainsAll0(dag.NoMinLedger.forbiddenSymbols, GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['NoMinLedger', 'forbiddenSymbols'], 'NoMinLedger is missing a forbidden executable symbol', {
      actual: dag.NoMinLedger.forbiddenSymbols,
    });
  }

  const hit = findForbiddenExecutableUse0(dag, ['GlobalProofDAG0'], false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'GlobalNoHiddenMin0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in GlobalProofDAG0', hit);
  }

  return validationAccept0({
    kind: 'NoOpaqueProof0NF',
  });
}

function validateNodeDigests0(nodes) {
  for (let index = 0; index < nodes.length; index += 1) {
    const node = nodes[index];

    if (node.Digest !== undefined) {
      const expected = digestCanonical0(nodeDigestMaterial0(node));

      if (!sameDigest0(node.Digest, expected)) {
        return validationReject0(['Nodes', index, 'Digest'], 'global proof node digest mismatch', {
          id: node.id,
          expected,
          actual: node.Digest,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'GlobalNodeDigests0NF',
    nodeCount: nodes.length,
  });
}

function validateNodeMode0(node, path) {
  const mode = node.mode ?? node.Mode ?? 'Full';

  if (!isNonEmptyString(mode)) {
    return validationReject0([...path, 'mode'], 'global proof node mode must be a non-empty string', {
      id: node.id,
      mode,
    });
  }

  const normalizedMode = String(mode).trim().toLowerCase();
  const payload = node.payload ?? node.Payload ?? {};

  if (
    normalizedMode === 'quot' &&
    isPlainObject(payload) &&
    (
      payload.constructiveFullReplacement === true ||
      payload.replacementEquality === true ||
      payload.fullModeConstruction === true
    )
  ) {
    return validationReject0([...path, 'payload'], 'quotient proof node cannot construct a full-mode replacement', {
      id: node.id,
      mode,
    });
  }

  return validationAccept0({
    kind: 'GlobalNodeMode0NF',
  });
}

function validateNodeBounds0(node, path) {
  const bounds = node.bounds ?? node.Bounds ?? {};

  if (!isPlainObject(bounds)) {
    return validationReject0([...path, 'bounds'], 'global proof node bounds must be an object', {
      id: node.id,
      actual: typeof bounds,
    });
  }

  if (bounds.polynomial !== true) {
    return validationReject0([...path, 'bounds', 'polynomial'], 'global proof node bounds must be polynomial', {
      id: node.id,
      actual: bounds.polynomial,
    });
  }

  if (bounds.exponent !== undefined && (!Number.isInteger(bounds.exponent) || bounds.exponent <= 0)) {
    return validationReject0([...path, 'bounds', 'exponent'], 'global proof node bounds exponent must be positive when present', {
      id: node.id,
      actual: bounds.exponent,
    });
  }

  return validationAccept0({
    kind: 'GlobalNodeBounds0NF',
  });
}

function validateNodeRoute0(node, path) {
  const route = node.route ?? node.Route;

  if (route === null || route === undefined) {
    return validationAccept0({
      kind: 'GlobalNodeRoute0NF',
    });
  }

  if (!isPlainObject(route)) {
    return validationReject0([...path, 'route'], 'global proof node route must be an object when present', {
      id: node.id,
    });
  }

  if (route.kind === 'Gain' && route.verifyDWAccepted !== true) {
    return validationReject0([...path, 'route', 'verifyDWAccepted'], 'constructive Gain route must compile to VerifyDW acceptance', {
      id: node.id,
    });
  }

  if (route.kind === 'ExactRoute' && route.exactCertificateAccepted !== true) {
    return validationReject0([...path, 'route', 'exactCertificateAccepted'], 'ExactRoute must carry an accepted exact certificate', {
      id: node.id,
    });
  }

  if (route.kind === 'Descent' && route.rankDecreases !== true) {
    return validationReject0([...path, 'route', 'rankDecreases'], 'Descent route must certify rank decrease', {
      id: node.id,
    });
  }

  return validationAccept0({
    kind: 'GlobalNodeRoute0NF',
  });
}

function validateNodeRank0(node, path) {
  const route = node.route ?? node.Route;

  if (!isPlainObject(route) || route.kind !== 'Descent') {
    return validationAccept0({
      kind: 'GlobalNodeRank0NF',
    });
  }

  const before = route.rankBefore;
  const after = route.rankAfter;

  if (Array.isArray(before) && Array.isArray(after)) {
    if (compareLexRank0(after, before) >= 0) {
      return validationReject0([...path, 'route', 'rankAfter'], 'Descent route rankAfter must be lexicographically smaller than rankBefore', {
        id: node.id,
        rankBefore: before,
        rankAfter: after,
      });
    }
  }

  return validationAccept0({
    kind: 'GlobalNodeRank0NF',
  });
}

function summarizeKinds0(nodes) {
  const out = {};

  for (const kind of GLOBAL_DAG_NODE_KINDS0) {
    out[kind] = 0;
  }

  for (const node of nodes) {
    out[node.nodeKind] = (out[node.nodeKind] ?? 0) + 1;
  }

  return out;
}

function normalizeRefId0(ref) {
  if (typeof ref === 'string') {
    return ref;
  }

  if (isPlainObject(ref)) {
    return ref.id ?? ref.ref ?? ref.nodeId ?? ref.NodeID;
  }

  return null;
}

function normalizeImportEdge0(edge) {
  if (Array.isArray(edge) && edge.length >= 2) {
    return {
      from: String(edge[0]),
      to: String(edge[1]),
    };
  }

  if (isPlainObject(edge)) {
    const from = edge.from ?? edge.src;
    const to = edge.to ?? edge.dst;

    if (from !== undefined && to !== undefined) {
      return {
        from: String(from),
        to: String(to),
      };
    }
  }

  return null;
}

function edgeKey0(edge) {
  if (Array.isArray(edge)) {
    return `${String(edge[0])}->${String(edge[1])}`;
  }

  return `${String(edge.from)}->${String(edge.to)}`;
}

function findCycle0(graph) {
  const visiting = new Set();
  const visited = new Set();

  function dfs(nodeId, path) {
    if (visiting.has(nodeId)) {
      return [...path, nodeId];
    }

    if (visited.has(nodeId)) {
      return null;
    }

    visiting.add(nodeId);

    for (const next of graph.get(nodeId) ?? []) {
      if (!graph.has(next)) {
        continue;
      }

      const hit = dfs(next, [...path, nodeId]);

      if (hit !== null) {
        return hit;
      }
    }

    visiting.delete(nodeId);
    visited.add(nodeId);

    return null;
  }

  for (const nodeId of graph.keys()) {
    const hit = dfs(nodeId, []);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function findOpaqueProof0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findOpaqueProof0(value[index], [...path, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    if (/opaque|proofblob|trustedblob|assumeproof/i.test(key)) {
      return {
        key,
        path: [...path, key],
        value: value[key],
      };
    }

    const hit = findOpaqueProof0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && GLOBAL_DAG_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
      return {
        symbol: value,
        path,
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findForbiddenExecutableUse0(value[index], [...path, index], inExecutablePosition);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    const nextExecutablePosition =
      inExecutablePosition ||
      EXECUTABLE_KEYS0.has(key) ||
      /exec|call|program|body|operator|operation/i.test(key);

    const hit = findForbiddenExecutableUse0(value[key], [...path, key], nextExecutablePosition);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function nodeDigestMaterial0(node) {
  const out = {};

  for (const key of Object.keys(node).sort()) {
    if (key !== 'Digest' && key !== 'digest') {
      out[key] = node[key];
    }
  }

  return out;
}

function sameDigest0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.alg === b.alg &&
    a.hex === b.hex
  );
}

function compareLexRank0(a, b) {
  const n = Math.max(a.length, b.length);

  for (let index = 0; index < n; index += 1) {
    const aa = Number(a[index] ?? 0);
    const bb = Number(b[index] ?? 0);

    if (aa < bb) {
      return -1;
    }

    if (aa > bb) {
      return 1;
    }
  }

  return 0;
}

function getPiGlobalDAG0(dag) {
  return dag.PiGlobalDAG ?? dag['Πglobal'] ?? dag.piGlobalDAG;
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
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

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

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
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}