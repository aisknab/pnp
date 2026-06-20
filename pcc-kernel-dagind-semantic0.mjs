import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofRecord0,
  SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0,
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_GRAPH_NODES = 100_000;
const MAX_GRAPH_EDGES = 1_000_000;
const MAX_PREDECESSORS = 4_096;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_DAGIND_OPERATIONS0 = Object.freeze(['close']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0,
  'DAGInd',
]);

export function makeSemanticInductionDAGNode0(id, predecessors = []) {
  requireIdentifier0(id, 'makeSemanticInductionDAGNode0 id');
  if (!Array.isArray(predecessors)) {
    throw new TypeError('makeSemanticInductionDAGNode0 predecessors must be an array');
  }

  const canonicalPredecessors = [...predecessors].sort(compareText0);
  return Object.freeze({
    kind: 'SemanticInductionDAGNode0',
    id,
    predecessors: Object.freeze(canonicalPredecessors),
  });
}

export function makeSemanticInductionDAG0(graphId, nodes = []) {
  requireIdentifier0(graphId, 'makeSemanticInductionDAG0 graphId');
  if (!Array.isArray(nodes)) {
    throw new TypeError('makeSemanticInductionDAG0 nodes must be an array');
  }

  return Object.freeze({
    kind: 'SemanticInductionDAG0',
    version: CHECKER_VERSION,
    graphId,
    nodes: Object.freeze([...nodes]),
  });
}

/**
 * A DAG-induction case is ordinary Record evidence. The current invariant and
 * every predecessor invariant must already be accepted semantic judgments.
 */
export function makeSemanticDAGIndCase0({
  graphId,
  nodeId,
  current,
  predecessorInvariants = [],
} = {}) {
  requireIdentifier0(graphId, 'makeSemanticDAGIndCase0 graphId');
  requireIdentifier0(nodeId, 'makeSemanticDAGIndCase0 nodeId');
  if (!Array.isArray(predecessorInvariants)) {
    throw new TypeError(
      'makeSemanticDAGIndCase0 predecessorInvariants must be an array',
    );
  }

  const fields = [makeSemanticRecordField0('current', current)];
  for (const entry of predecessorInvariants) {
    if (!isPlainObject0(entry)) {
      throw new TypeError('DAGInd predecessor invariant entry must be an object');
    }
    requireIdentifier0(entry.nodeId, 'DAGInd predecessor invariant nodeId');
    fields.push(makeSemanticRecordField0(
      `pred.${entry.nodeId}`,
      entry.invariant,
    ));
  }
  fields.sort((left, right) => compareText0(left.name, right.name));

  return makeSemanticRecordJudgment0(
    caseRecordType0(graphId, nodeId),
    fields,
  );
}

export function makeSemanticDAGIndJudgment0({
  graphId,
  nodeOrder,
  sourceNodeIds,
  sinkNodeIds,
  caseProofIds,
  cases,
} = {}) {
  requireIdentifier0(graphId, 'makeSemanticDAGIndJudgment0 graphId');
  for (const [name, value] of Object.entries({
    nodeOrder,
    sourceNodeIds,
    sinkNodeIds,
    caseProofIds,
    cases,
  })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticDAGIndJudgment0 ${name} must be an array`);
    }
  }

  return Object.freeze({
    kind: 'SemanticDAGIndJudgment0',
    version: CHECKER_VERSION,
    graphId,
    nodeOrder: Object.freeze([...nodeOrder]),
    sourceNodeIds: Object.freeze([...sourceNodeIds]),
    sinkNodeIds: Object.freeze([...sinkNodeIds]),
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    allNodesClosed: true,
  });
}

/**
 * Helper for generators and tests. The checker independently recomputes this
 * result and never trusts a caller-provided closure flag.
 */
export function deriveSemanticDAGIndJudgment0({
  graph,
  caseRecords,
  caseProofIds,
} = {}) {
  const graphCheck = validateInductionGraph0(graph, ['graph']);
  if (!graphCheck.ok) throw new TypeError(graphCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError('deriveSemanticDAGIndJudgment0 requires case arrays');
  }

  const derived = deriveClosure0(
    graphCheck.graph,
    caseRecords.map((Conclusion, index) => ({
      id: caseProofIds[index],
      RuleName: 'Record',
      operation: 'intro',
      Conclusion,
    })),
    caseProofIds,
    ['derive'],
  );
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.judgment;
}

export function CheckSemanticKernelReadinessDAGInd0() {
  const checker = 'CheckSemanticKernelReadinessDAGInd0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessDAGInd0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofRecord0',
    proofChecker: 'CheckSemanticKernelProofDAGInd0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    dagIndOperations: [...SEMANTIC_DAGIND_OPERATIONS0],
    localCasesMustBeAcceptedRecordEvidence: true,
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
        reason: 'DAGInd-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks Eq/Subst/Record with the merged predecessor checker and checks DAGInd
 * as a finite structural closure over accepted local case records.
 */
export function CheckSemanticKernelProofDAGInd0(input) {
  const checker = 'CheckSemanticKernelProofDAGInd0';
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
        reason: 'DAGInd-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofRecord0',
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
        reason: 'Eq/Subst/Record sub-DAG rejected under the predecessor semantic checker',
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

    let semantic;
    if (node.RuleName === 'DAGInd') {
      semantic = checkDAGIndRule0(node, premises, path);
    } else {
      semantic = validationAccept0({
        kind: 'SemanticPredecessorRuleReference0NF',
        ruleName: node.RuleName,
        operation: node.Payload?.op ?? null,
        premiseCount: node.Premises.length,
      });
    }

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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0.includes(rule),
  );
  const dagIndNodeCount = summaries.filter(
    (node) => node.RuleName === 'DAGInd',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofDAGInd0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofRecord0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedDAGIndOperations: [...SEMANTIC_DAGIND_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      dagIndNodeCount,
      acceptedNodeIds: summaries.map((node) => node.id),
      conclusionDigests: summaries.map((node) => ({
        id: node.id,
        digest: digestCanonical0(node.Conclusion),
      })),
    },
    ledger,
  });
}

function normalizeProofDAG0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      { kind: 'SemanticDAGIndProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticDAGIndProofInput0NF', form: 'object', nodeCount: nodes.length },
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
      'kind',
      'version',
      'id',
      'RuleName',
      'Mode',
      'Premises',
      'Conclusion',
      'Payload',
    ]);
    const unexpectedNodeKeys = Object.keys(node)
      .filter((key) => !allowedNodeKeys.has(key));
    if (unexpectedNodeKeys.length !== 0) {
      return validationReject0(
        [...path, unexpectedNodeKeys[0]],
        'DAGInd-extended semantic proof node rejects undeclared fields',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'DAGInd-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'DAGInd-extended semantic kernel accepts Full mode only',
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

    if (node.RuleName === 'DAGInd') {
      const payload = validateDAGIndPayload0(node.Payload, [...path, 'Payload']);
      if (!payload.ok) return payload;
      const conclusion = validateDAGIndJudgmentShape0(
        node.Conclusion,
        [...path, 'Conclusion'],
      );
      if (!conclusion.ok) return conclusion;
    }

    seenIds.add(node.id);
  }

  return validationAccept0({
    kind: 'SemanticDAGIndProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateDAGIndPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'graph']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'DAGInd payload rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (!SEMANTIC_DAGIND_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'DAGInd operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_DAGIND_OPERATIONS0],
      },
    );
  }

  return validateInductionGraph0(payload.graph, [...path, 'graph']);
}

function validateInductionGraph0(graph, path) {
  if (!isPlainObject0(graph)) {
    return validationReject0(path, 'DAGInd graph must be an object', {
      actual: typeof graph,
    });
  }

  const allowedGraphKeys = new Set(['kind', 'version', 'graphId', 'nodes']);
  const unexpectedGraphKeys = Object.keys(graph)
    .filter((key) => !allowedGraphKeys.has(key));
  if (unexpectedGraphKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedGraphKeys[0]],
      'DAGInd graph rejects undeclared fields',
      { unexpectedFields: unexpectedGraphKeys.sort() },
    );
  }

  if (graph.kind !== 'SemanticInductionDAG0') {
    return validationReject0(
      [...path, 'kind'],
      'DAGInd graph kind must be SemanticInductionDAG0',
      { actual: graph.kind },
    );
  }

  if (graph.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `DAGInd graph version must be ${CHECKER_VERSION}`,
      { actual: graph.version },
    );
  }

  if (!isIdentifier0(graph.graphId)) {
    return validationReject0(
      [...path, 'graphId'],
      'DAGInd graphId must be a canonical identifier',
      { actual: graph.graphId },
    );
  }

  if (!Array.isArray(graph.nodes) || graph.nodes.length === 0) {
    return validationReject0(
      [...path, 'nodes'],
      'DAGInd graph must contain a nonempty nodes array',
      { actual: Array.isArray(graph.nodes) ? graph.nodes.length : typeof graph.nodes },
    );
  }

  if (graph.nodes.length > MAX_GRAPH_NODES) {
    return validationReject0(
      [...path, 'nodes'],
      'DAGInd graph exceeds maxGraphNodes',
      { maxGraphNodes: MAX_GRAPH_NODES, actual: graph.nodes.length },
    );
  }

  const seen = new Set();
  let edgeCount = 0;
  let previousId = null;

  for (let index = 0; index < graph.nodes.length; index += 1) {
    const node = graph.nodes[index];
    const nodePath = [...path, 'nodes', index];

    if (!isPlainObject0(node)) {
      return validationReject0(nodePath, 'DAGInd graph node must be an object', {
        actual: typeof node,
      });
    }

    const allowedNodeKeys = new Set(['kind', 'id', 'predecessors']);
    const unexpectedNodeKeys = Object.keys(node)
      .filter((key) => !allowedNodeKeys.has(key));
    if (unexpectedNodeKeys.length !== 0) {
      return validationReject0(
        [...nodePath, unexpectedNodeKeys[0]],
        'DAGInd graph node rejects undeclared fields',
        { unexpectedFields: unexpectedNodeKeys.sort() },
      );
    }

    if (node.kind !== 'SemanticInductionDAGNode0') {
      return validationReject0(
        [...nodePath, 'kind'],
        'DAGInd graph node kind must be SemanticInductionDAGNode0',
        { actual: node.kind },
      );
    }

    if (!isIdentifier0(node.id)) {
      return validationReject0(
        [...nodePath, 'id'],
        'DAGInd graph node id must be a canonical identifier',
        { actual: node.id },
      );
    }

    if (seen.has(node.id)) {
      return validationReject0(
        [...nodePath, 'id'],
        'DAGInd graph node ids must be unique',
        { id: node.id },
      );
    }

    if (previousId !== null && compareText0(previousId, node.id) >= 0) {
      return validationReject0(
        [...path, 'nodes'],
        'DAGInd graph nodes must use canonical increasing topological order',
        { previousId, actualId: node.id },
      );
    }

    if (!Array.isArray(node.predecessors)) {
      return validationReject0(
        [...nodePath, 'predecessors'],
        'DAGInd graph node predecessors must be an array',
        { actual: typeof node.predecessors },
      );
    }

    if (node.predecessors.length > MAX_PREDECESSORS) {
      return validationReject0(
        [...nodePath, 'predecessors'],
        'DAGInd graph node exceeds maxPredecessors',
        { maxPredecessors: MAX_PREDECESSORS, actual: node.predecessors.length },
      );
    }

    const canonicalPredecessors = [...node.predecessors].sort(compareText0);
    if (!sameCanonical0(node.predecessors, canonicalPredecessors)) {
      return validationReject0(
        [...nodePath, 'predecessors'],
        'DAGInd predecessor ids must be in canonical order',
        { expected: canonicalPredecessors, actual: node.predecessors },
      );
    }

    if (new Set(node.predecessors).size !== node.predecessors.length) {
      return validationReject0(
        [...nodePath, 'predecessors'],
        'DAGInd predecessor ids must be unique',
        { predecessors: node.predecessors },
      );
    }

    for (let predecessorIndex = 0; predecessorIndex < node.predecessors.length; predecessorIndex += 1) {
      const predecessorId = node.predecessors[predecessorIndex];
      if (!isIdentifier0(predecessorId)) {
        return validationReject0(
          [...nodePath, 'predecessors', predecessorIndex],
          'DAGInd predecessor id must be a canonical identifier',
          { actual: predecessorId },
        );
      }
      if (!seen.has(predecessorId)) {
        return validationReject0(
          [...nodePath, 'predecessors', predecessorIndex],
          'DAGInd predecessor must reference an earlier graph node',
          { nodeId: node.id, predecessorId },
        );
      }
    }

    edgeCount += node.predecessors.length;
    if (edgeCount > MAX_GRAPH_EDGES) {
      return validationReject0(
        [...path, 'nodes'],
        'DAGInd graph exceeds maxGraphEdges',
        { maxGraphEdges: MAX_GRAPH_EDGES, actual: edgeCount },
      );
    }

    seen.add(node.id);
    previousId = node.id;
  }

  const outdegree = new Map(graph.nodes.map((node) => [node.id, 0]));
  for (const node of graph.nodes) {
    for (const predecessorId of node.predecessors) {
      outdegree.set(predecessorId, outdegree.get(predecessorId) + 1);
    }
  }

  const sourceNodeIds = graph.nodes
    .filter((node) => node.predecessors.length === 0)
    .map((node) => node.id);
  const sinkNodeIds = graph.nodes
    .filter((node) => outdegree.get(node.id) === 0)
    .map((node) => node.id);

  return validationAcceptWith0({
    kind: 'SemanticInductionDAG0NF',
    graphId: graph.graphId,
    nodeCount: graph.nodes.length,
    edgeCount,
    nodeOrder: graph.nodes.map((node) => node.id),
    sourceNodeIds,
    sinkNodeIds,
  }, {
    graph,
    sourceNodeIds,
    sinkNodeIds,
  });
}

function validateDAGIndJudgmentShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'DAGInd conclusion must be an object', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'graphId',
    'nodeOrder',
    'sourceNodeIds',
    'sinkNodeIds',
    'caseProofIds',
    'cases',
    'allNodesClosed',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'DAGInd conclusion rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticDAGIndJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'DAGInd conclusion kind must be SemanticDAGIndJudgment0',
      { actual: judgment.kind },
    );
  }

  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `DAGInd conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }

  if (!isIdentifier0(judgment.graphId)) {
    return validationReject0(
      [...path, 'graphId'],
      'DAGInd conclusion graphId must be a canonical identifier',
      { actual: judgment.graphId },
    );
  }

  for (const field of [
    'nodeOrder',
    'sourceNodeIds',
    'sinkNodeIds',
    'caseProofIds',
    'cases',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `DAGInd conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }

  if (judgment.allNodesClosed !== true) {
    return validationReject0(
      [...path, 'allNodesClosed'],
      'DAGInd conclusion allNodesClosed must be true',
      { actual: judgment.allNodesClosed },
    );
  }

  return validationAccept0({
    kind: 'SemanticDAGIndJudgmentShape0NF',
    graphId: judgment.graphId,
    caseCount: judgment.cases.length,
  });
}

function checkDAGIndRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'DAGInd rule supports only close',
      { actual: node.Payload.op },
    );
  }

  const graphCheck = validateInductionGraph0(
    node.Payload.graph,
    [...path, 'Payload', 'graph'],
  );
  if (!graphCheck.ok) return graphCheck;

  const derived = deriveClosure0(
    graphCheck.graph,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;

  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'DAGInd conclusion must exactly equal the computed all-node closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticDAGIndRule0NF',
    ruleName: 'DAGInd',
    operation: 'close',
    graphId: graphCheck.graph.graphId,
    nodeCount: graphCheck.graph.nodes.length,
    edgeCount: graphCheck.nf.edgeCount,
    sourceNodeIds: graphCheck.sourceNodeIds,
    sinkNodeIds: graphCheck.sinkNodeIds,
    caseProofIds: [...node.Premises],
    predecessorComplete: true,
    allNodesClosed: true,
  });
}

function deriveClosure0(graph, premises, caseProofIds, path) {
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'DAGInd closure requires premise and proof-id arrays',
      null,
    );
  }

  if (premises.length !== graph.nodes.length || caseProofIds.length !== graph.nodes.length) {
    return validationReject0(
      [...path, 'Premises'],
      'DAGInd requires exactly one local case record for every graph node',
      {
        expected: graph.nodes.length,
        actualPremises: premises.length,
        actualProofIds: caseProofIds.length,
      },
    );
  }

  const currentByNode = new Map();
  const cases = [];

  for (let index = 0; index < graph.nodes.length; index += 1) {
    const graphNode = graph.nodes[index];
    const premise = premises[index];
    const casePath = [...path, 'Premises', index];

    if (!isPlainObject0(premise)) {
      return validationReject0(
        casePath,
        'DAGInd case premise must resolve to an earlier accepted proof node',
        { actual: premise },
      );
    }

    if (premise.RuleName !== 'Record' || premise.operation !== 'intro') {
      return validationReject0(
        casePath,
        'DAGInd case premise must be accepted Record.intro evidence',
        {
          actualRuleName: premise.RuleName,
          actualOperation: premise.operation,
        },
      );
    }

    const record = premise.Conclusion;
    const recordCheck = validateCaseRecord0(
      record,
      graph.graphId,
      graphNode,
      currentByNode,
      casePath,
    );
    if (!recordCheck.ok) return recordCheck;

    currentByNode.set(graphNode.id, recordCheck.current);
    cases.push(Object.freeze({
      kind: 'SemanticDAGIndCaseResult0',
      nodeId: graphNode.id,
      predecessors: Object.freeze([...graphNode.predecessors]),
      invariant: recordCheck.current,
    }));
  }

  const outdegree = new Map(graph.nodes.map((entry) => [entry.id, 0]));
  for (const graphNode of graph.nodes) {
    for (const predecessorId of graphNode.predecessors) {
      outdegree.set(predecessorId, outdegree.get(predecessorId) + 1);
    }
  }

  const judgment = makeSemanticDAGIndJudgment0({
    graphId: graph.graphId,
    nodeOrder: graph.nodes.map((entry) => entry.id),
    sourceNodeIds: graph.nodes
      .filter((entry) => entry.predecessors.length === 0)
      .map((entry) => entry.id),
    sinkNodeIds: graph.nodes
      .filter((entry) => outdegree.get(entry.id) === 0)
      .map((entry) => entry.id),
    caseProofIds,
    cases,
  });

  return validationAcceptWith0({
    kind: 'SemanticDAGIndClosure0NF',
    graphId: graph.graphId,
    nodeCount: graph.nodes.length,
    caseProofIds: [...caseProofIds],
  }, {
    judgment,
  });
}

function validateCaseRecord0(record, graphId, graphNode, currentByNode, path) {
  if (!isPlainObject0(record)) {
    return validationReject0(path, 'DAGInd case conclusion must be a record judgment', {
      actual: typeof record,
    });
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'Conclusion', 'kind'],
      'DAGInd case conclusion must be SemanticRecordJudgment0',
      { actual: record.kind },
    );
  }

  const expectedRecordType = caseRecordType0(graphId, graphNode.id);
  if (record.recordType !== expectedRecordType) {
    return validationReject0(
      [...path, 'Conclusion', 'recordType'],
      'DAGInd case recordType must bind the graph and node id',
      { expected: expectedRecordType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DAGInd case record fields must be an array',
      { actual: typeof record.fields },
    );
  }

  const expectedNames = [
    'current',
    ...graphNode.predecessors.map((predecessorId) => `pred.${predecessorId}`),
  ].sort(compareText0);
  const actualNames = record.fields.map((field) => field?.name ?? null);
  if (!sameCanonical0(actualNames, expectedNames)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DAGInd case fields must contain current and every predecessor invariant exactly once',
      { expected: expectedNames, actual: actualNames },
    );
  }

  const fieldMap = new Map(record.fields.map((field) => [field.name, field.judgment]));
  const current = fieldMap.get('current');
  if (!isPlainObject0(current)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DAGInd current invariant must be a semantic judgment object',
      { actual: current },
    );
  }

  for (const predecessorId of graphNode.predecessors) {
    const expected = currentByNode.get(predecessorId);
    if (expected === undefined) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'DAGInd case refers to a predecessor without an earlier closed invariant',
        { nodeId: graphNode.id, predecessorId },
      );
    }

    const actual = fieldMap.get(`pred.${predecessorId}`);
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'DAGInd predecessor invariant must exactly match the earlier node invariant',
        { nodeId: graphNode.id, predecessorId, expected, actual },
      );
    }
  }

  return validationAcceptWith0({
    kind: 'SemanticDAGIndCase0NF',
    graphId,
    nodeId: graphNode.id,
    predecessorCount: graphNode.predecessors.length,
    predecessorComplete: true,
  }, {
    current,
  });
}

function caseRecordType0(graphId, nodeId) {
  return `DAGIndCase0.${graphId}.${nodeId}`;
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0(baseNodes));
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofRecord0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofRecord0 threw instead of returning a reject record',
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

function compareText0(left, right) {
  return left < right ? -1 : left > right ? 1 : 0;
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
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

function makeRejectRecord0({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

function isIdentifier0(value) {
  return typeof value === 'string' && ID_PATTERN.test(value);
}

function requireIdentifier0(value, label) {
  if (!isIdentifier0(value)) {
    throw new TypeError(`${label} must be a canonical identifier`);
  }
}
