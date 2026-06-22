import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofDPInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0,
} from './pcc-kernel-dpind-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_LEFT_VERTICES = 4_096;
const MAX_RIGHT_VERTICES = 4_096;
const MAX_HALL_EDGES = 131_072;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_HALL_OPERATIONS0 = Object.freeze(['decide']);
export const SEMANTIC_HALL_OUTCOMES0 = Object.freeze([
  'complete-matching',
  'hall-deficient',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_HALL0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0,
  'Hall',
]);

export function makeSemanticHallEdge0({ leftId, rightId } = {}) {
  requireIdentifier0(leftId, 'makeSemanticHallEdge0 leftId');
  requireIdentifier0(rightId, 'makeSemanticHallEdge0 rightId');
  return Object.freeze({
    kind: 'SemanticHallEdge0',
    version: CHECKER_VERSION,
    leftId,
    rightId,
  });
}

/**
 * Constructs an explicit finite bipartite graph. Constructors canonicalize for
 * generator convenience; the checker independently revalidates strict vertex
 * order, disjoint sides, edge order, endpoint membership, and uniqueness.
 */
export function makeSemanticHallGraph0({
  graphId,
  leftVertexIds = [],
  rightVertexIds = [],
  edges = [],
} = {}) {
  requireIdentifier0(graphId, 'makeSemanticHallGraph0 graphId');
  const left = canonicalIdentifierArray0(
    leftVertexIds,
    'makeSemanticHallGraph0 leftVertexIds',
    { allowEmpty: false },
  );
  const right = canonicalIdentifierArray0(
    rightVertexIds,
    'makeSemanticHallGraph0 rightVertexIds',
    { allowEmpty: true },
  );

  const rightSet = new Set(right);
  for (const leftId of left) {
    if (rightSet.has(leftId)) {
      throw new TypeError(
        'makeSemanticHallGraph0 left and right vertex ids must be disjoint',
      );
    }
  }

  if (!Array.isArray(edges)) {
    throw new TypeError('makeSemanticHallGraph0 edges must be an array');
  }
  const canonicalEdges = edges.map((edge) => {
    if (!isPlainObject0(edge)) {
      throw new TypeError('makeSemanticHallGraph0 edge must be an object');
    }
    return makeSemanticHallEdge0({
      leftId: edge.leftId,
      rightId: edge.rightId,
    });
  }).sort(compareHallEdge0);

  const edgeKeys = canonicalEdges.map(edgeKey0);
  if (new Set(edgeKeys).size !== edgeKeys.length) {
    throw new TypeError('makeSemanticHallGraph0 edges must be unique');
  }

  const graph = Object.freeze({
    kind: 'SemanticHallGraph0',
    version: CHECKER_VERSION,
    graphId,
    leftVertexIds: Object.freeze(left),
    rightVertexIds: Object.freeze(right),
    edges: Object.freeze(canonicalEdges),
  });
  const checked = validateGraph0(graph, ['graph']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return graph;
}

/**
 * Computes the deterministic maximum matching and, when the left side is not
 * saturated, the canonical alternating-reachability Hall-deficient set and its
 * exact neighbourhood. No matching or deficiency assertion is accepted from a
 * caller.
 */
export function deriveSemanticHallJudgment0({ graph } = {}) {
  const graphCheck = validateGraph0(graph, ['graph']);
  if (!graphCheck.ok) throw new TypeError(graphCheck.witness.reason);
  const analysis = computeHallAnalysis0(graphCheck, ['analysis']);
  if (!analysis.ok) throw new TypeError(analysis.witness.reason);
  return makeHallJudgment0(graphCheck, analysis);
}

export function CheckSemanticKernelReadinessHall0() {
  const checker = 'CheckSemanticKernelReadinessHall0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_HALL0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessHall0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofDPInd0',
    proofChecker: 'CheckSemanticKernelProofHall0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_HALL0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    hallOperations: [...SEMANTIC_HALL_OPERATIONS0],
    explicitFiniteBipartiteGraphRequired: true,
    canonicalVertexAndEdgeOrderRequired: true,
    deterministicMaximumMatchingRequired: true,
    exactNeighbourhoodComputationRequired: true,
    completeMatchingOrExactDeficiencyComputed: true,
    callerMatchingAndDeficiencyAssertionsForbidden: true,
    domainSpecificEdgeSemanticsNotInferred: true,
  };
  const ledger = [makeLedgerEntry0(
    'semanticRuleCoverage',
    missingRules.length === 0,
    nf,
  )];

  if (missingRules.length !== 0) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.coverage`,
      path: ['missingRules'],
      witness: {
        reason: 'Hall-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks all predecessor rule families with the merged DPInd checker and then
 * decides Hall over each explicit finite bipartite graph by recomputation.
 */
export function CheckSemanticKernelProofHall0(input) {
  const checker = 'CheckSemanticKernelProofHall0';
  const ledger = [];

  const dag = normalizeProofDAG0(input);
  ledger.push(makeLedgerEntry0('input', dag.ok, dag.nf ?? dag.witness));
  if (!dag.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, dag, ledger);
  }

  if (dag.nodes.length > MAX_PROOF_NODES) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.bounds`,
      path: ['nodes'],
      witness: {
        reason: 'Hall-extended semantic proof DAG exceeds maxNodes',
        maxNodes: MAX_PROOF_NODES,
        actual: dag.nodes.length,
      },
      ledger,
    });
  }

  const shape = validateProofDAGShape0(dag.nodes);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.shape`, shape, ledger);
  }

  const baseNodes = dag.nodes.filter(
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofDPInd0',
    baseCall.ok && baseCall.record.tag === 'accept',
    baseCall.ok ? baseCall.record : baseCall.witness,
  ));

  if (!baseCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.baseProof.exception`,
      path: ['nodes'],
      witness: baseCall.witness,
      ledger,
    });
  }
  if (baseCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.baseProof`,
      path: ['nodes'],
      witness: {
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd sub-DAG rejected under the predecessor semantic checker',
        baseNodeIds: baseNodes.map((node) => node.id),
        inner: compactReject0(baseCall.record),
      },
      ledger,
    });
  }

  const accepted = new Map();
  const summaries = [];
  for (let index = 0; index < dag.nodes.length; index += 1) {
    const node = dag.nodes[index];
    const path = ['nodes', index];
    const phase = String(index).padStart(4, '0');
    const premises = node.Premises.map((premiseId) => accepted.get(premiseId));

    const semantic = node.RuleName === 'Hall'
      ? checkHallRule0(node, premises, path)
      : validationAccept0({
          kind: 'SemanticPredecessorRuleReference0NF',
          ruleName: node.RuleName,
          operation: node.Payload?.op ?? null,
          premiseCount: node.Premises.length,
        });

    ledger.push(makeLedgerEntry0(
      `node.${phase}.semantic`,
      semantic.ok,
      semantic.nf ?? semantic.witness,
    ));
    if (!semantic.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.node.${phase}.semantic`,
        semantic,
        ledger,
      );
    }

    const summary = Object.freeze({
      id: node.id,
      RuleName: node.RuleName,
      operation: semantic.nf.operation ?? node.Payload?.op ?? null,
      Conclusion: node.Conclusion,
      digest: digestCanonical0(node),
    });
    accepted.set(node.id, summary);
    summaries.push(summary);
  }

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_HALL0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0.includes(rule),
  );
  const hallNodeCount = summaries.filter((node) => node.RuleName === 'Hall').length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofHall0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofDPInd0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_HALL0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedHallOperations: [...SEMANTIC_HALL_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      hallNodeCount,
      acceptedNodeIds: summaries.map((node) => node.id),
      conclusionDigests: summaries.map((node) => ({
        id: node.id,
        digest: digestCanonical0(node.Conclusion),
      })),
    },
    ledger,
  });
}

function makeHallJudgment0(graphCheck, analysis) {
  const graph = graphCheck.graph;
  const terminalJudgment = Object.freeze({
    kind: 'SemanticHallResultJudgment0',
    version: CHECKER_VERSION,
    graphId: graph.graphId,
    outcome: analysis.outcome,
  });

  return Object.freeze({
    kind: 'SemanticHallJudgment0',
    version: CHECKER_VERSION,
    graphId: graph.graphId,
    outcome: analysis.outcome,
    leftVertexIds: Object.freeze([...graph.leftVertexIds]),
    rightVertexIds: Object.freeze([...graph.rightVertexIds]),
    leftCardinality: graph.leftVertexIds.length,
    rightCardinality: graph.rightVertexIds.length,
    edgeCount: graph.edges.length,
    matching: Object.freeze(analysis.matching.map((edge) => Object.freeze({ ...edge }))),
    matchingSize: analysis.matching.length,
    unmatchedLeftVertexIds: Object.freeze([...analysis.unmatchedLeftVertexIds]),
    deficientLeftVertexIds: Object.freeze([...analysis.deficientLeftVertexIds]),
    neighbourhoodRightVertexIds: Object.freeze([
      ...analysis.neighbourhoodRightVertexIds,
    ]),
    deficiency: analysis.deficiency,
    terminalJudgment,
    graphCanonical: true,
    maximumMatchingComputed: true,
    matchingEdgesValid: true,
    matchingInjective: true,
    exactNeighbourhoodComputed: true,
    leftComplete: analysis.outcome === 'complete-matching',
    hallDeficiencyVerified: analysis.outcome === 'hall-deficient',
    decisionComputed: true,
  });
}

function normalizeProofDAG0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      { kind: 'SemanticHallProofInput0NF', form: 'array', nodeCount: input.length },
      { nodes: input },
    );
  }
  if (!isPlainObject0(input)) {
    return validationReject0([], 'semantic proof input must be an array or object', {
      actual: typeof input,
    });
  }
  if (input.kind !== undefined && input.kind !== 'SemanticProofDAG0') {
    return validationReject0(
      ['kind'],
      'semantic proof DAG kind must be SemanticProofDAG0 when present',
      { actual: input.kind },
    );
  }
  if (input.version !== undefined && input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic proof DAG version must be ${CHECKER_VERSION} when present`,
      { actual: input.version },
    );
  }
  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['nodes'],
      'semantic proof DAG must provide a nodes array',
      { actual: typeof nodes },
    );
  }
  return validationAcceptWith0(
    { kind: 'SemanticHallProofInput0NF', form: 'object', nodeCount: nodes.length },
    { nodes },
  );
}

function validateProofDAGShape0(nodes) {
  const seenIds = new Set();
  for (let index = 0; index < nodes.length; index += 1) {
    const node = nodes[index];
    const path = ['nodes', index];
    if (!isPlainObject0(node)) {
      return validationReject0(path, 'semantic proof node must be an object', {
        actual: typeof node,
      });
    }

    const allowedNodeKeys = new Set([
      'kind', 'version', 'id', 'RuleName', 'Mode',
      'Premises', 'Conclusion', 'Payload',
    ]);
    const unexpectedNodeKeys = Object.keys(node)
      .filter((key) => !allowedNodeKeys.has(key));
    if (unexpectedNodeKeys.length !== 0) {
      return validationReject0(
        [...path, unexpectedNodeKeys[0]],
        'Hall-extended semantic proof node rejects undeclared fields',
        { unexpectedFields: unexpectedNodeKeys.sort() },
      );
    }
    if (node.kind !== 'SemanticProofNode0') {
      return validationReject0(
        [...path, 'kind'],
        'semantic proof node kind must be SemanticProofNode0',
        { actual: node.kind },
      );
    }
    if (node.version !== undefined && node.version !== CHECKER_VERSION) {
      return validationReject0(
        [...path, 'version'],
        `semantic proof node version must be ${CHECKER_VERSION}`,
        { actual: node.version },
      );
    }
    if (!isIdentifier0(node.id)) {
      return validationReject0(
        [...path, 'id'],
        'semantic proof node id must be a canonical identifier',
        { actual: node.id },
      );
    }
    if (seenIds.has(node.id)) {
      return validationReject0(
        [...path, 'id'],
        'semantic proof node ids must be unique',
        { id: node.id },
      );
    }
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'Hall-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'Hall-extended semantic kernel accepts Full mode only',
        { actual: node.Mode },
      );
    }
    if (!Array.isArray(node.Premises)) {
      return validationReject0(
        [...path, 'Premises'],
        'semantic proof node Premises must be an array',
        { actual: typeof node.Premises },
      );
    }
    const premiseIds = new Set();
    for (let premiseIndex = 0; premiseIndex < node.Premises.length; premiseIndex += 1) {
      const premiseId = node.Premises[premiseIndex];
      if (!isIdentifier0(premiseId)) {
        return validationReject0(
          [...path, 'Premises', premiseIndex],
          'semantic proof premise id must be a canonical identifier',
          { actual: premiseId },
        );
      }
      if (premiseIds.has(premiseId)) {
        return validationReject0(
          [...path, 'Premises', premiseIndex],
          'semantic proof node cannot repeat a premise id',
          { premiseId },
        );
      }
      if (!seenIds.has(premiseId)) {
        return validationReject0(
          [...path, 'Premises', premiseIndex],
          'semantic proof premise must reference an earlier node',
          { nodeId: node.id, premiseId },
        );
      }
      premiseIds.add(premiseId);
    }
    if (!isPlainObject0(node.Payload)) {
      return validationReject0(
        [...path, 'Payload'],
        'semantic proof node Payload must be an object',
        { actual: typeof node.Payload },
      );
    }
    if (node.RuleName === 'Hall') {
      const payload = validateHallPayload0(node.Payload, [...path, 'Payload']);
      if (!payload.ok) return payload;
      const conclusion = validateConclusionShape0(
        node.Conclusion,
        [...path, 'Conclusion'],
      );
      if (!conclusion.ok) return conclusion;
    }
    seenIds.add(node.id);
  }

  return validationAccept0({
    kind: 'SemanticHallProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateHallPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'graph']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Hall payload rejects caller-supplied matching, deficiency, completeness, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_HALL_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'Hall operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_HALL_OPERATIONS0],
      },
    );
  }
  return validateGraph0(payload.graph, [...path, 'graph']);
}

function validateGraph0(graph, path) {
  if (!isPlainObject0(graph)) {
    return validationReject0(path, 'Hall graph must be an object', {
      actual: typeof graph,
    });
  }
  const allowedGraphKeys = new Set([
    'kind', 'version', 'graphId',
    'leftVertexIds', 'rightVertexIds', 'edges',
  ]);
  const unexpectedGraphKeys = Object.keys(graph)
    .filter((key) => !allowedGraphKeys.has(key));
  if (unexpectedGraphKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedGraphKeys[0]],
      'Hall graph rejects undeclared matching, deficiency, completion, solver, search, or oracle assertions',
      { unexpectedFields: unexpectedGraphKeys.sort() },
    );
  }
  if (graph.kind !== 'SemanticHallGraph0') {
    return validationReject0(
      [...path, 'kind'],
      'Hall graph kind must be SemanticHallGraph0',
      { actual: graph.kind },
    );
  }
  if (graph.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Hall graph version must be ${CHECKER_VERSION}`,
      { actual: graph.version },
    );
  }
  if (!isIdentifier0(graph.graphId)) {
    return validationReject0(
      [...path, 'graphId'],
      'Hall graphId must be a canonical identifier',
      { actual: graph.graphId },
    );
  }

  const leftCheck = validateCanonicalIdentifierArray0(
    graph.leftVertexIds,
    [...path, 'leftVertexIds'],
    { allowEmpty: false, maxLength: MAX_LEFT_VERTICES, side: 'left' },
  );
  if (!leftCheck.ok) return leftCheck;
  const rightCheck = validateCanonicalIdentifierArray0(
    graph.rightVertexIds,
    [...path, 'rightVertexIds'],
    { allowEmpty: true, maxLength: MAX_RIGHT_VERTICES, side: 'right' },
  );
  if (!rightCheck.ok) return rightCheck;

  const leftSet = new Set(graph.leftVertexIds);
  const rightSet = new Set(graph.rightVertexIds);
  for (let index = 0; index < graph.leftVertexIds.length; index += 1) {
    const id = graph.leftVertexIds[index];
    if (rightSet.has(id)) {
      return validationReject0(
        [...path, 'leftVertexIds', index],
        'Hall left and right vertex ids must be disjoint',
        { id },
      );
    }
  }

  if (!Array.isArray(graph.edges)) {
    return validationReject0(
      [...path, 'edges'],
      'Hall edges must be an array',
      { actual: typeof graph.edges },
    );
  }
  if (graph.edges.length > MAX_HALL_EDGES) {
    return validationReject0(
      [...path, 'edges'],
      'Hall graph exceeds maxEdges',
      { maxEdges: MAX_HALL_EDGES, actual: graph.edges.length },
    );
  }

  const adjacency = new Map(graph.leftVertexIds.map((leftId) => [leftId, []]));
  const edgeKeySet = new Set();
  let previousEdge = null;
  for (let index = 0; index < graph.edges.length; index += 1) {
    const edge = graph.edges[index];
    const edgePath = [...path, 'edges', index];
    if (!isPlainObject0(edge)) {
      return validationReject0(edgePath, 'Hall edge must be an object', {
        actual: typeof edge,
      });
    }
    const allowedEdgeKeys = new Set(['kind', 'version', 'leftId', 'rightId']);
    const unexpectedEdgeKeys = Object.keys(edge)
      .filter((key) => !allowedEdgeKeys.has(key));
    if (unexpectedEdgeKeys.length !== 0) {
      return validationReject0(
        [...edgePath, unexpectedEdgeKeys[0]],
        'Hall edge rejects undeclared fields',
        { unexpectedFields: unexpectedEdgeKeys.sort() },
      );
    }
    if (edge.kind !== 'SemanticHallEdge0') {
      return validationReject0(
        [...edgePath, 'kind'],
        'Hall edge kind must be SemanticHallEdge0',
        { actual: edge.kind },
      );
    }
    if (edge.version !== CHECKER_VERSION) {
      return validationReject0(
        [...edgePath, 'version'],
        `Hall edge version must be ${CHECKER_VERSION}`,
        { actual: edge.version },
      );
    }
    if (!isIdentifier0(edge.leftId) || !leftSet.has(edge.leftId)) {
      return validationReject0(
        [...edgePath, 'leftId'],
        'Hall edge leftId must name a declared left vertex',
        { actual: edge.leftId },
      );
    }
    if (!isIdentifier0(edge.rightId) || !rightSet.has(edge.rightId)) {
      return validationReject0(
        [...edgePath, 'rightId'],
        'Hall edge rightId must name a declared right vertex',
        { actual: edge.rightId },
      );
    }

    if (previousEdge !== null) {
      const comparison = compareHallEdge0(previousEdge, edge);
      if (comparison === 0) {
        return validationReject0(
          edgePath,
          'Hall edges must be unique',
          { edge },
        );
      }
      if (comparison > 0) {
        return validationReject0(
          edgePath,
          'Hall edges must be in canonical left-right order',
          { previousEdge, edge },
        );
      }
    }
    previousEdge = edge;
    const key = edgeKey0(edge);
    if (edgeKeySet.has(key)) {
      return validationReject0(edgePath, 'Hall edges must be unique', { edge });
    }
    edgeKeySet.add(key);
    adjacency.get(edge.leftId).push(edge.rightId);
  }

  return validationAcceptWith0({
    kind: 'SemanticHallGraph0NF',
    graphId: graph.graphId,
    leftCardinality: graph.leftVertexIds.length,
    rightCardinality: graph.rightVertexIds.length,
    edgeCount: graph.edges.length,
    canonicalVertexOrder: true,
    canonicalEdgeOrder: true,
    sidesDisjoint: true,
  }, {
    graph,
    leftSet,
    rightSet,
    adjacency,
    edgeKeySet,
  });
}

function validateCanonicalIdentifierArray0(value, path, {
  allowEmpty,
  maxLength,
  side,
}) {
  if (!Array.isArray(value)) {
    return validationReject0(path, `Hall ${side} vertex ids must be an array`, {
      actual: typeof value,
    });
  }
  if (!allowEmpty && value.length === 0) {
    return validationReject0(path, 'Hall graph must contain at least one left vertex', null);
  }
  if (value.length > maxLength) {
    return validationReject0(path, `Hall graph exceeds max${side === 'left' ? 'Left' : 'Right'}Vertices`, {
      maxVertices: maxLength,
      actual: value.length,
    });
  }
  for (let index = 0; index < value.length; index += 1) {
    if (!isIdentifier0(value[index])) {
      return validationReject0(
        [...path, index],
        `Hall ${side} vertex id must be a canonical identifier`,
        { actual: value[index] },
      );
    }
    if (index > 0) {
      const comparison = compareText0(value[index - 1], value[index]);
      if (comparison === 0) {
        return validationReject0(
          [...path, index],
          `Hall ${side} vertex ids must be unique`,
          { id: value[index] },
        );
      }
      if (comparison > 0) {
        return validationReject0(
          [...path, index],
          `Hall ${side} vertex ids must be in canonical order`,
          { previous: value[index - 1], actual: value[index] },
        );
      }
    }
  }
  return validationAccept0({
    kind: 'SemanticHallVertexArray0NF',
    side,
    cardinality: value.length,
  });
}

function computeHallAnalysis0(graphCheck, path) {
  const { graph, adjacency, edgeKeySet } = graphCheck;
  const matchingResult = computeMaximumMatching0(graph, adjacency);
  const matching = matchingResult.matching;

  for (const edge of matching) {
    if (!edgeKeySet.has(`${edge.leftId}\u0000${edge.rightId}`)) {
      return validationReject0(
        path,
        'Hall internal matching contains an undeclared graph edge',
        { edge },
      );
    }
  }
  if (new Set(matching.map((edge) => edge.leftId)).size !== matching.length
      || new Set(matching.map((edge) => edge.rightId)).size !== matching.length) {
    return validationReject0(
      path,
      'Hall internal matching is not injective',
      { matching },
    );
  }

  const unmatchedLeftVertexIds = graph.leftVertexIds.filter(
    (leftId) => matchingResult.pairLeft.get(leftId) === null,
  );

  if (matching.length === graph.leftVertexIds.length) {
    return validationAcceptWith0({
      kind: 'SemanticHallAnalysis0NF',
      outcome: 'complete-matching',
      matchingSize: matching.length,
      deficiency: 0,
    }, {
      outcome: 'complete-matching',
      matching,
      unmatchedLeftVertexIds,
      deficientLeftVertexIds: [],
      neighbourhoodRightVertexIds: [],
      deficiency: 0,
    });
  }

  const witness = computeAlternatingDeficiency0(
    graph,
    adjacency,
    matchingResult.pairLeft,
    matchingResult.pairRight,
    unmatchedLeftVertexIds,
  );

  if (witness.reachedUnmatchedRightId !== null) {
    return validationReject0(
      path,
      'Hall maximum-matching computation left an augmenting path',
      { reachedUnmatchedRightId: witness.reachedUnmatchedRightId },
    );
  }
  if (!sameCanonical0(
    witness.reachedRightVertexIds,
    witness.neighbourhoodRightVertexIds,
  )) {
    return validationReject0(
      path,
      'Hall alternating witness does not equal the exact deficient-set neighbourhood',
      {
        alternatingRightVertexIds: witness.reachedRightVertexIds,
        exactNeighbourhoodRightVertexIds: witness.neighbourhoodRightVertexIds,
      },
    );
  }

  const deficiency = witness.deficientLeftVertexIds.length
    - witness.neighbourhoodRightVertexIds.length;
  if (witness.deficientLeftVertexIds.length === 0 || deficiency <= 0) {
    return validationReject0(
      path,
      'Hall computed deficient set must be nonempty with strictly smaller neighbourhood',
      {
        deficientLeftVertexIds: witness.deficientLeftVertexIds,
        neighbourhoodRightVertexIds: witness.neighbourhoodRightVertexIds,
        deficiency,
      },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticHallAnalysis0NF',
    outcome: 'hall-deficient',
    matchingSize: matching.length,
    deficiency,
  }, {
    outcome: 'hall-deficient',
    matching,
    unmatchedLeftVertexIds,
    deficientLeftVertexIds: witness.deficientLeftVertexIds,
    neighbourhoodRightVertexIds: witness.neighbourhoodRightVertexIds,
    deficiency,
  });
}

function computeMaximumMatching0(graph, adjacency) {
  const pairLeft = new Map(graph.leftVertexIds.map((leftId) => [leftId, null]));
  const pairRight = new Map(graph.rightVertexIds.map((rightId) => [rightId, null]));
  const distance = new Map();
  const infinity = Number.POSITIVE_INFINITY;

  function bfs0() {
    const queue = [];
    for (const leftId of graph.leftVertexIds) {
      if (pairLeft.get(leftId) === null) {
        distance.set(leftId, 0);
        queue.push(leftId);
      } else {
        distance.set(leftId, infinity);
      }
    }

    let foundFreeRight = false;
    for (let head = 0; head < queue.length; head += 1) {
      const leftId = queue[head];
      const nextDistance = distance.get(leftId) + 1;
      for (const rightId of adjacency.get(leftId)) {
        const pairedLeft = pairRight.get(rightId);
        if (pairedLeft === null) {
          foundFreeRight = true;
        } else if (distance.get(pairedLeft) === infinity) {
          distance.set(pairedLeft, nextDistance);
          queue.push(pairedLeft);
        }
      }
    }
    return foundFreeRight;
  }

  function dfs0(leftId) {
    for (const rightId of adjacency.get(leftId)) {
      const pairedLeft = pairRight.get(rightId);
      if (pairedLeft === null
          || (distance.get(pairedLeft) === distance.get(leftId) + 1
            && dfs0(pairedLeft))) {
        pairLeft.set(leftId, rightId);
        pairRight.set(rightId, leftId);
        return true;
      }
    }
    distance.set(leftId, infinity);
    return false;
  }

  while (bfs0()) {
    for (const leftId of graph.leftVertexIds) {
      if (pairLeft.get(leftId) === null) dfs0(leftId);
    }
  }

  const matching = graph.leftVertexIds
    .filter((leftId) => pairLeft.get(leftId) !== null)
    .map((leftId) => Object.freeze({
      kind: 'SemanticHallMatch0',
      version: CHECKER_VERSION,
      leftId,
      rightId: pairLeft.get(leftId),
    }));

  return { pairLeft, pairRight, matching };
}

function computeAlternatingDeficiency0(
  graph,
  adjacency,
  pairLeft,
  pairRight,
  unmatchedLeftVertexIds,
) {
  const reachedLeft = new Set(unmatchedLeftVertexIds);
  const reachedRight = new Set();
  const queue = [...unmatchedLeftVertexIds];
  let reachedUnmatchedRightId = null;

  for (let head = 0; head < queue.length; head += 1) {
    const leftId = queue[head];
    const matchedRight = pairLeft.get(leftId);
    for (const rightId of adjacency.get(leftId)) {
      if (rightId === matchedRight) continue;
      if (reachedRight.has(rightId)) continue;
      reachedRight.add(rightId);
      const pairedLeft = pairRight.get(rightId);
      if (pairedLeft === null) {
        reachedUnmatchedRightId = rightId;
        continue;
      }
      if (!reachedLeft.has(pairedLeft)) {
        reachedLeft.add(pairedLeft);
        queue.push(pairedLeft);
      }
    }
  }

  const deficientLeftVertexIds = graph.leftVertexIds.filter(
    (leftId) => reachedLeft.has(leftId),
  );
  const reachedRightVertexIds = graph.rightVertexIds.filter(
    (rightId) => reachedRight.has(rightId),
  );
  const neighbourhood = new Set();
  for (const leftId of deficientLeftVertexIds) {
    for (const rightId of adjacency.get(leftId)) neighbourhood.add(rightId);
  }
  const neighbourhoodRightVertexIds = graph.rightVertexIds.filter(
    (rightId) => neighbourhood.has(rightId),
  );

  return {
    deficientLeftVertexIds,
    reachedRightVertexIds,
    neighbourhoodRightVertexIds,
    reachedUnmatchedRightId,
  };
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'Hall conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'graphId', 'outcome',
    'leftVertexIds', 'rightVertexIds',
    'leftCardinality', 'rightCardinality', 'edgeCount',
    'matching', 'matchingSize', 'unmatchedLeftVertexIds',
    'deficientLeftVertexIds', 'neighbourhoodRightVertexIds',
    'deficiency', 'terminalJudgment',
    'graphCanonical', 'maximumMatchingComputed',
    'matchingEdgesValid', 'matchingInjective',
    'exactNeighbourhoodComputed', 'leftComplete',
    'hallDeficiencyVerified', 'decisionComputed',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Hall conclusion rejects undeclared readiness, matching, deficiency, solver, search, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticHallJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'Hall conclusion kind must be SemanticHallJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Hall conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  if (!isIdentifier0(judgment.graphId)) {
    return validationReject0(
      [...path, 'graphId'],
      'Hall conclusion graphId must be a canonical identifier',
      { actual: judgment.graphId },
    );
  }
  if (!SEMANTIC_HALL_OUTCOMES0.includes(judgment.outcome)) {
    return validationReject0(
      [...path, 'outcome'],
      'Hall conclusion outcome is unsupported',
      { actual: judgment.outcome },
    );
  }
  for (const field of [
    'leftVertexIds', 'rightVertexIds', 'matching',
    'unmatchedLeftVertexIds', 'deficientLeftVertexIds',
    'neighbourhoodRightVertexIds',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `Hall conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }
  for (const field of [
    'leftCardinality', 'rightCardinality', 'edgeCount',
    'matchingSize', 'deficiency',
  ]) {
    if (!Number.isSafeInteger(judgment[field]) || judgment[field] < 0) {
      return validationReject0(
        [...path, field],
        `Hall conclusion ${field} must be a nonnegative safe integer`,
        { actual: judgment[field] },
      );
    }
  }
  for (const field of [
    'graphCanonical', 'maximumMatchingComputed', 'matchingEdgesValid',
    'matchingInjective', 'exactNeighbourhoodComputed', 'leftComplete',
    'hallDeficiencyVerified', 'decisionComputed',
  ]) {
    if (typeof judgment[field] !== 'boolean') {
      return validationReject0(
        [...path, field],
        `Hall conclusion ${field} must be boolean`,
        { actual: judgment[field] },
      );
    }
  }
  if (!isPlainObject0(judgment.terminalJudgment)
      || judgment.terminalJudgment.kind !== 'SemanticHallResultJudgment0') {
    return validationReject0(
      [...path, 'terminalJudgment'],
      'Hall conclusion terminalJudgment must be SemanticHallResultJudgment0',
      { actual: judgment.terminalJudgment },
    );
  }
  return validationAccept0({
    kind: 'SemanticHallJudgmentShape0NF',
    graphId: judgment.graphId,
    outcome: judgment.outcome,
    matchingSize: judgment.matchingSize,
  });
}

function checkHallRule0(node, premises, path) {
  if (node.Payload.op !== 'decide') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'Hall rule supports only decide',
      { actual: node.Payload.op },
    );
  }
  if (node.Premises.length !== 0 || premises.length !== 0) {
    return validationReject0(
      [...path, 'Premises'],
      'Hall.decide computes from the explicit graph and accepts no proof premises',
      { actual: node.Premises },
    );
  }

  const graphCheck = validateGraph0(
    node.Payload.graph,
    [...path, 'Payload', 'graph'],
  );
  if (!graphCheck.ok) return graphCheck;
  const analysis = computeHallAnalysis0(graphCheck, [...path, 'Payload', 'graph']);
  if (!analysis.ok) return analysis;
  const expected = makeHallJudgment0(graphCheck, analysis);

  if (!sameCanonical0(node.Conclusion, expected)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'Hall conclusion must exactly equal the computed matching-or-deficiency decision',
      { expected, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticHallRule0NF',
    ruleName: 'Hall',
    operation: 'decide',
    graphId: graphCheck.graph.graphId,
    outcome: analysis.outcome,
    leftCardinality: graphCheck.graph.leftVertexIds.length,
    rightCardinality: graphCheck.graph.rightVertexIds.length,
    edgeCount: graphCheck.graph.edges.length,
    matchingSize: analysis.matching.length,
    deficiency: analysis.deficiency,
    deterministicMaximumMatchingComputed: true,
    exactNeighbourhoodComputed: true,
    callerCertificateAbsent: true,
  });
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0(nodes));
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofDPInd0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofDPInd0 threw instead of returning a reject record',
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    };
  }
}

function compactReject0(record) {
  return {
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: record?.Digest ?? record?.digest ?? null,
  };
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

function validationAcceptWith0(nf, extra) {
  return { ok: true, nf, ...extra };
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

function canonicalIdentifierArray0(value, label, { allowEmpty }) {
  if (!Array.isArray(value)) {
    throw new TypeError(`${label} must be an array`);
  }
  if (!allowEmpty && value.length === 0) {
    throw new TypeError(`${label} must be nonempty`);
  }
  const result = [...value];
  for (const entry of result) requireIdentifier0(entry, `${label} entry`);
  result.sort(compareText0);
  if (new Set(result).size !== result.length) {
    throw new TypeError(`${label} must contain unique identifiers`);
  }
  return result;
}

function compareHallEdge0(left, right) {
  const leftComparison = compareText0(left.leftId, right.leftId);
  return leftComparison !== 0
    ? leftComparison
    : compareText0(left.rightId, right.rightId);
}

function edgeKey0(edge) {
  return `${edge.leftId}\u0000${edge.rightId}`;
}

function compareText0(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isIdentifier0(value) {
  return typeof value === 'string' && ID_PATTERN.test(value);
}

function requireIdentifier0(value, label) {
  if (!isIdentifier0(value)) {
    throw new TypeError(`${label} must be a canonical identifier`);
  }
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
