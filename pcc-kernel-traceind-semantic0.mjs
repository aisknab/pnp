import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofOblTopoInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0,
} from './pcc-kernel-obltopoind-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticApp0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_TRACE_NODES = 100_000;
const MAX_TERM_DEPTH = 256;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_TRACE_NODE_KINDS0 = Object.freeze([
  'Source',
  'NAND',
]);

export const SEMANTIC_TRACEIND_OPERATIONS0 = Object.freeze(['close']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0,
  'TraceInd',
]);

export function makeSemanticTraceSourceNode0({
  index,
  id,
  sourceCoordinate,
  sourceTerm,
} = {}) {
  requireIndex0(index, 'makeSemanticTraceSourceNode0 index');
  requireIdentifier0(id, 'makeSemanticTraceSourceNode0 id');
  requireIdentifier0(
    sourceCoordinate,
    'makeSemanticTraceSourceNode0 sourceCoordinate',
  );

  const valueTerm = sourceTerm;
  return Object.freeze({
    kind: 'SemanticTraceNode0',
    index,
    id,
    nodeKind: 'Source',
    inputIds: Object.freeze([]),
    sourceCoordinate,
    sourceTerm,
    valueTerm,
    equation: makeSemanticEqJudgment0(valueTerm, sourceTerm),
    invariant: makeSemanticEqJudgment0(valueTerm, valueTerm),
  });
}

export function makeSemanticTraceNANDNode0({
  index,
  id,
  leftId,
  rightId,
  leftTerm,
  rightTerm,
} = {}) {
  requireIndex0(index, 'makeSemanticTraceNANDNode0 index');
  requireIdentifier0(id, 'makeSemanticTraceNANDNode0 id');
  requireIdentifier0(leftId, 'makeSemanticTraceNANDNode0 leftId');
  requireIdentifier0(rightId, 'makeSemanticTraceNANDNode0 rightId');

  const valueTerm = makeSemanticApp0('nand', [leftTerm, rightTerm], 'Bool');
  return Object.freeze({
    kind: 'SemanticTraceNode0',
    index,
    id,
    nodeKind: 'NAND',
    inputIds: Object.freeze([leftId, rightId]),
    sourceCoordinate: null,
    sourceTerm: null,
    valueTerm,
    equation: makeSemanticEqJudgment0(valueTerm, valueTerm),
    invariant: makeSemanticEqJudgment0(valueTerm, valueTerm),
  });
}

export function makeSemanticTrace0({
  traceId,
  nodes = [],
  outputNodeId,
  outputCoordinate,
  outputTerm = undefined,
} = {}) {
  requireIdentifier0(traceId, 'makeSemanticTrace0 traceId');
  if (!Array.isArray(nodes)) {
    throw new TypeError('makeSemanticTrace0 nodes must be an array');
  }
  requireIdentifier0(outputNodeId, 'makeSemanticTrace0 outputNodeId');
  requireIdentifier0(outputCoordinate, 'makeSemanticTrace0 outputCoordinate');

  const outputNode = nodes.find((node) => node?.id === outputNodeId);
  const resolvedOutputTerm = outputTerm ?? outputNode?.valueTerm;

  return Object.freeze({
    kind: 'SemanticTrace0',
    version: CHECKER_VERSION,
    traceId,
    nodes: Object.freeze([...nodes]),
    outputNodeId,
    outputCoordinate,
    outputTerm: resolvedOutputTerm,
  });
}

/**
 * A local trace case is accepted Record.intro evidence. It binds the exact
 * source/NAND equation, the current trace invariant, and every earlier input
 * invariant required by the declared trace node.
 */
export function makeSemanticTraceIndCase0({
  traceId,
  nodeId,
  equation,
  current,
  dependencyInvariants = [],
} = {}) {
  requireIdentifier0(traceId, 'makeSemanticTraceIndCase0 traceId');
  requireIdentifier0(nodeId, 'makeSemanticTraceIndCase0 nodeId');
  if (!Array.isArray(dependencyInvariants)) {
    throw new TypeError(
      'makeSemanticTraceIndCase0 dependencyInvariants must be an array',
    );
  }

  const fields = [
    makeSemanticRecordField0('current', current),
    makeSemanticRecordField0('equation', equation),
  ];

  for (const dependency of dependencyInvariants) {
    if (!isPlainObject0(dependency)) {
      throw new TypeError(
        'makeSemanticTraceIndCase0 dependency entry must be an object',
      );
    }
    requireIdentifier0(
      dependency.nodeId,
      'makeSemanticTraceIndCase0 dependency nodeId',
    );
    fields.push(makeSemanticRecordField0(
      `dep.${dependency.nodeId}`,
      dependency.invariant,
    ));
  }

  fields.sort((left, right) => compareText0(left.name, right.name));
  return makeSemanticRecordJudgment0(
    caseRecordType0(traceId, nodeId),
    fields,
  );
}

export function makeSemanticTraceIndJudgment0({
  traceId,
  nodeOrder,
  sourceNodeIds,
  nandNodeIds,
  outputNodeId,
  outputCoordinate,
  outputTerm,
  caseProofIds,
  cases,
} = {}) {
  requireIdentifier0(traceId, 'makeSemanticTraceIndJudgment0 traceId');
  for (const [name, value] of Object.entries({
    nodeOrder,
    sourceNodeIds,
    nandNodeIds,
    caseProofIds,
    cases,
  })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticTraceIndJudgment0 ${name} must be an array`);
    }
  }
  requireIdentifier0(
    outputNodeId,
    'makeSemanticTraceIndJudgment0 outputNodeId',
  );
  requireIdentifier0(
    outputCoordinate,
    'makeSemanticTraceIndJudgment0 outputCoordinate',
  );

  return Object.freeze({
    kind: 'SemanticTraceIndJudgment0',
    version: CHECKER_VERSION,
    traceId,
    nodeOrder: Object.freeze([...nodeOrder]),
    sourceNodeIds: Object.freeze([...sourceNodeIds]),
    nandNodeIds: Object.freeze([...nandNodeIds]),
    outputNodeId,
    outputCoordinate,
    outputTerm,
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    allSourceBindingsExact: true,
    allNANDEquationsExact: true,
    allNodesEvaluated: true,
    outputCoordinateBound: true,
  });
}

/**
 * Generator helper. The checker independently recomputes the complete trace
 * closure and never trusts caller-supplied completion flags.
 */
export function deriveSemanticTraceIndJudgment0({
  trace,
  caseRecords,
  caseProofIds,
} = {}) {
  const traceCheck = validateTrace0(trace, ['trace']);
  if (!traceCheck.ok) throw new TypeError(traceCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError('deriveSemanticTraceIndJudgment0 requires case arrays');
  }

  const derived = deriveClosure0(
    traceCheck,
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

export function CheckSemanticKernelReadinessTraceInd0() {
  const checker = 'CheckSemanticKernelReadinessTraceInd0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessTraceInd0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofOblTopoInd0',
    proofChecker: 'CheckSemanticKernelProofTraceInd0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    traceIndOperations: [...SEMANTIC_TRACEIND_OPERATIONS0],
    nodeKinds: [...SEMANTIC_TRACE_NODE_KINDS0],
    exactSourceBindingsRequired: true,
    exactNANDEquationsRequired: true,
    topologicalInputClosureRequired: true,
    outputCoordinateIdentityRequired: true,
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
        reason: 'TraceInd-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks predecessor rule families with the merged predecessor checker and
 * checks TraceInd as exact finite topological closure of accepted local cases.
 */
export function CheckSemanticKernelProofTraceInd0(input) {
  const checker = 'CheckSemanticKernelProofTraceInd0';
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
        reason: 'TraceInd-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofOblTopoInd0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd sub-DAG rejected under the predecessor semantic checker',
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
    if (node.RuleName === 'TraceInd') {
      semantic = checkTraceIndRule0(node, premises, path);
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0.includes(rule),
  );
  const traceIndNodeCount = summaries.filter(
    (node) => node.RuleName === 'TraceInd',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofTraceInd0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofOblTopoInd0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedTraceIndOperations: [...SEMANTIC_TRACEIND_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      traceIndNodeCount,
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
      { kind: 'SemanticTraceIndProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticTraceIndProofInput0NF', form: 'object', nodeCount: nodes.length },
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
        'TraceInd-extended semantic proof node rejects undeclared fields',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'TraceInd-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'TraceInd-extended semantic kernel accepts Full mode only',
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

    if (node.RuleName === 'TraceInd') {
      const payload = validateTraceIndPayload0(node.Payload, [...path, 'Payload']);
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
    kind: 'SemanticTraceIndProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateTraceIndPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'trace']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TraceInd payload rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (!SEMANTIC_TRACEIND_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'TraceInd operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_TRACEIND_OPERATIONS0],
      },
    );
  }

  return validateTrace0(payload.trace, [...path, 'trace']);
}

function validateTrace0(trace, path) {
  if (!isPlainObject0(trace)) {
    return validationReject0(path, 'TraceInd trace must be an object', {
      actual: typeof trace,
    });
  }

  const allowedTraceKeys = new Set([
    'kind',
    'version',
    'traceId',
    'nodes',
    'outputNodeId',
    'outputCoordinate',
    'outputTerm',
  ]);
  const unexpectedTraceKeys = Object.keys(trace)
    .filter((key) => !allowedTraceKeys.has(key));
  if (unexpectedTraceKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedTraceKeys[0]],
      'TraceInd trace rejects undeclared fields',
      { unexpectedFields: unexpectedTraceKeys.sort() },
    );
  }

  if (trace.kind !== 'SemanticTrace0') {
    return validationReject0(
      [...path, 'kind'],
      'TraceInd trace kind must be SemanticTrace0',
      { actual: trace.kind },
    );
  }

  if (trace.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TraceInd trace version must be ${CHECKER_VERSION}`,
      { actual: trace.version },
    );
  }

  if (!isIdentifier0(trace.traceId)) {
    return validationReject0(
      [...path, 'traceId'],
      'TraceInd traceId must be a canonical identifier',
      { actual: trace.traceId },
    );
  }

  if (!Array.isArray(trace.nodes) || trace.nodes.length === 0) {
    return validationReject0(
      [...path, 'nodes'],
      'TraceInd trace must contain a nonempty nodes array',
      {
        actual: Array.isArray(trace.nodes)
          ? trace.nodes.length
          : typeof trace.nodes,
      },
    );
  }

  if (trace.nodes.length > MAX_TRACE_NODES) {
    return validationReject0(
      [...path, 'nodes'],
      'TraceInd trace exceeds maxTraceNodes',
      { maxTraceNodes: MAX_TRACE_NODES, actual: trace.nodes.length },
    );
  }

  const byId = new Map();
  const sourceNodeIds = [];
  const nandNodeIds = [];

  for (let index = 0; index < trace.nodes.length; index += 1) {
    const node = trace.nodes[index];
    const nodePath = [...path, 'nodes', index];

    if (!isPlainObject0(node)) {
      return validationReject0(nodePath, 'TraceInd trace node must be an object', {
        actual: typeof node,
      });
    }

    const allowedNodeKeys = new Set([
      'kind',
      'index',
      'id',
      'nodeKind',
      'inputIds',
      'sourceCoordinate',
      'sourceTerm',
      'valueTerm',
      'equation',
      'invariant',
    ]);
    const unexpectedNodeKeys = Object.keys(node)
      .filter((key) => !allowedNodeKeys.has(key));
    if (unexpectedNodeKeys.length !== 0) {
      return validationReject0(
        [...nodePath, unexpectedNodeKeys[0]],
        'TraceInd trace node rejects undeclared fields',
        { unexpectedFields: unexpectedNodeKeys.sort() },
      );
    }

    if (node.kind !== 'SemanticTraceNode0') {
      return validationReject0(
        [...nodePath, 'kind'],
        'TraceInd trace node kind must be SemanticTraceNode0',
        { actual: node.kind },
      );
    }

    if (node.index !== index) {
      return validationReject0(
        [...nodePath, 'index'],
        'TraceInd node indices must be consecutive from zero',
        { expected: index, actual: node.index },
      );
    }

    if (!isIdentifier0(node.id)) {
      return validationReject0(
        [...nodePath, 'id'],
        'TraceInd node id must be a canonical identifier',
        { actual: node.id },
      );
    }

    if (byId.has(node.id)) {
      return validationReject0(
        [...nodePath, 'id'],
        'TraceInd node ids must be unique',
        { id: node.id },
      );
    }

    if (!SEMANTIC_TRACE_NODE_KINDS0.includes(node.nodeKind)) {
      return validationReject0(
        [...nodePath, 'nodeKind'],
        'TraceInd node kind is unsupported',
        {
          actual: node.nodeKind,
          supportedKinds: [...SEMANTIC_TRACE_NODE_KINDS0],
        },
      );
    }

    if (!Array.isArray(node.inputIds)) {
      return validationReject0(
        [...nodePath, 'inputIds'],
        'TraceInd node inputIds must be an array',
        { actual: typeof node.inputIds },
      );
    }

    const valueTerm = validateTerm0(node.valueTerm, [...nodePath, 'valueTerm'], 0);
    if (!valueTerm.ok) return valueTerm;
    if (valueTerm.sort !== 'Bool') {
      return validationReject0(
        [...nodePath, 'valueTerm', 'sort'],
        'TraceInd node values must have Bool sort',
        { actual: valueTerm.sort },
      );
    }

    let expectedEquation;
    if (node.nodeKind === 'Source') {
      if (node.inputIds.length !== 0) {
        return validationReject0(
          [...nodePath, 'inputIds'],
          'TraceInd source nodes cannot have input trace nodes',
          { actual: node.inputIds },
        );
      }
      if (!isIdentifier0(node.sourceCoordinate)) {
        return validationReject0(
          [...nodePath, 'sourceCoordinate'],
          'TraceInd source coordinate must be a canonical identifier',
          { actual: node.sourceCoordinate },
        );
      }
      const sourceTerm = validateTerm0(
        node.sourceTerm,
        [...nodePath, 'sourceTerm'],
        0,
      );
      if (!sourceTerm.ok) return sourceTerm;
      if (sourceTerm.sort !== 'Bool') {
        return validationReject0(
          [...nodePath, 'sourceTerm', 'sort'],
          'TraceInd source term must have Bool sort',
          { actual: sourceTerm.sort },
        );
      }
      if (!['SemanticVar0', 'SemanticConst0'].includes(node.sourceTerm.kind)
          || node.sourceTerm.name !== node.sourceCoordinate) {
        return validationReject0(
          [...nodePath, 'sourceTerm'],
          'TraceInd source term must be the declared source coordinate',
          {
            sourceCoordinate: node.sourceCoordinate,
            actual: node.sourceTerm,
          },
        );
      }
      if (!sameCanonical0(node.valueTerm, node.sourceTerm)) {
        return validationReject0(
          [...nodePath, 'valueTerm'],
          'TraceInd source value must exactly equal the declared source term',
          { expected: node.sourceTerm, actual: node.valueTerm },
        );
      }
      expectedEquation = makeSemanticEqJudgment0(
        node.valueTerm,
        node.sourceTerm,
      );
      sourceNodeIds.push(node.id);
    } else {
      if (node.sourceCoordinate !== null || node.sourceTerm !== null) {
        return validationReject0(
          nodePath,
          'TraceInd NAND nodes cannot declare a source coordinate or source term',
          {
            sourceCoordinate: node.sourceCoordinate,
            sourceTerm: node.sourceTerm,
          },
        );
      }
      if (node.inputIds.length !== 2) {
        return validationReject0(
          [...nodePath, 'inputIds'],
          'TraceInd NAND nodes require exactly two ordered input ids',
          { expected: 2, actual: node.inputIds.length },
        );
      }
      const inputNodes = [];
      for (let inputIndex = 0; inputIndex < node.inputIds.length; inputIndex += 1) {
        const inputId = node.inputIds[inputIndex];
        if (!isIdentifier0(inputId)) {
          return validationReject0(
            [...nodePath, 'inputIds', inputIndex],
            'TraceInd input id must be a canonical identifier',
            { actual: inputId },
          );
        }
        const inputNode = byId.get(inputId);
        if (inputNode === undefined) {
          return validationReject0(
            [...nodePath, 'inputIds', inputIndex],
            'TraceInd NAND input must reference an earlier trace node',
            { nodeId: node.id, inputId },
          );
        }
        inputNodes.push(inputNode);
      }

      const expectedValueTerm = makeSemanticApp0(
        'nand',
        [inputNodes[0].valueTerm, inputNodes[1].valueTerm],
        'Bool',
      );
      if (!sameCanonical0(node.valueTerm, expectedValueTerm)) {
        return validationReject0(
          [...nodePath, 'valueTerm'],
          'TraceInd NAND value term must equal the NAND of earlier input values',
          { expected: expectedValueTerm, actual: node.valueTerm },
        );
      }
      expectedEquation = makeSemanticEqJudgment0(
        node.valueTerm,
        expectedValueTerm,
      );
      nandNodeIds.push(node.id);
    }

    if (!sameCanonical0(node.equation, expectedEquation)) {
      return validationReject0(
        [...nodePath, 'equation'],
        'TraceInd node equation must exactly match its declared source or NAND equation',
        { expected: expectedEquation, actual: node.equation },
      );
    }

    const expectedInvariant = makeSemanticEqJudgment0(
      node.valueTerm,
      node.valueTerm,
    );
    if (!sameCanonical0(node.invariant, expectedInvariant)) {
      return validationReject0(
        [...nodePath, 'invariant'],
        'TraceInd node invariant must be the exact accepted value judgment',
        { expected: expectedInvariant, actual: node.invariant },
      );
    }

    byId.set(node.id, node);
  }

  if (!isIdentifier0(trace.outputNodeId)) {
    return validationReject0(
      [...path, 'outputNodeId'],
      'TraceInd outputNodeId must be a canonical identifier',
      { actual: trace.outputNodeId },
    );
  }
  const outputNode = byId.get(trace.outputNodeId);
  if (outputNode === undefined) {
    return validationReject0(
      [...path, 'outputNodeId'],
      'TraceInd outputNodeId must name a declared trace node',
      { actual: trace.outputNodeId },
    );
  }

  if (!isIdentifier0(trace.outputCoordinate)) {
    return validationReject0(
      [...path, 'outputCoordinate'],
      'TraceInd outputCoordinate must be a canonical identifier',
      { actual: trace.outputCoordinate },
    );
  }

  const outputTerm = validateTerm0(
    trace.outputTerm,
    [...path, 'outputTerm'],
    0,
  );
  if (!outputTerm.ok) return outputTerm;
  if (outputTerm.sort !== 'Bool') {
    return validationReject0(
      [...path, 'outputTerm', 'sort'],
      'TraceInd output term must have Bool sort',
      { actual: outputTerm.sort },
    );
  }
  if (!sameCanonical0(trace.outputTerm, outputNode.valueTerm)) {
    return validationReject0(
      [...path, 'outputTerm'],
      'TraceInd output term must exactly equal the declared output-node value',
      { expected: outputNode.valueTerm, actual: trace.outputTerm },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticTrace0NF',
    traceId: trace.traceId,
    nodeCount: trace.nodes.length,
    nodeOrder: trace.nodes.map((node) => node.id),
    sourceNodeIds,
    nandNodeIds,
    outputNodeId: trace.outputNodeId,
    outputCoordinate: trace.outputCoordinate,
    outputTerm: trace.outputTerm,
  }, {
    trace,
    byId,
    outputNode,
  });
}

function validateTerm0(term, path, depth) {
  if (depth > MAX_TERM_DEPTH) {
    return validationReject0(path, 'TraceInd term exceeds maxTermDepth', {
      maxTermDepth: MAX_TERM_DEPTH,
    });
  }
  if (!isPlainObject0(term)) {
    return validationReject0(path, 'TraceInd term must be an object', {
      actual: typeof term,
    });
  }

  if (term.kind === 'SemanticVar0' || term.kind === 'SemanticConst0') {
    if (typeof term.name !== 'string' || term.name.length === 0) {
      return validationReject0(
        [...path, 'name'],
        'TraceInd variable/constant name must be nonempty',
        { actual: term.name },
      );
    }
    if (typeof term.sort !== 'string' || term.sort.length === 0) {
      return validationReject0(
        [...path, 'sort'],
        'TraceInd variable/constant sort must be nonempty',
        { actual: term.sort },
      );
    }
    return validationAcceptWith0({
      kind: 'SemanticTraceTerm0NF',
      termKind: term.kind,
      sort: term.sort,
    }, {
      sort: term.sort,
    });
  }

  if (term.kind === 'SemanticApp0') {
    if (typeof term.symbol !== 'string' || term.symbol.length === 0) {
      return validationReject0(
        [...path, 'symbol'],
        'TraceInd application symbol must be nonempty',
        { actual: term.symbol },
      );
    }
    if (typeof term.sort !== 'string' || term.sort.length === 0) {
      return validationReject0(
        [...path, 'sort'],
        'TraceInd application sort must be nonempty',
        { actual: term.sort },
      );
    }
    if (!Array.isArray(term.args)) {
      return validationReject0(
        [...path, 'args'],
        'TraceInd application args must be an array',
        { actual: typeof term.args },
      );
    }
    for (let index = 0; index < term.args.length; index += 1) {
      const argument = validateTerm0(
        term.args[index],
        [...path, 'args', index],
        depth + 1,
      );
      if (!argument.ok) return argument;
    }
    return validationAcceptWith0({
      kind: 'SemanticTraceTerm0NF',
      termKind: term.kind,
      symbol: term.symbol,
      arity: term.args.length,
      sort: term.sort,
    }, {
      sort: term.sort,
    });
  }

  return validationReject0(
    [...path, 'kind'],
    'TraceInd term kind is unsupported',
    {
      actual: term.kind,
      supportedKinds: ['SemanticVar0', 'SemanticConst0', 'SemanticApp0'],
    },
  );
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'TraceInd conclusion must be an object', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'traceId',
    'nodeOrder',
    'sourceNodeIds',
    'nandNodeIds',
    'outputNodeId',
    'outputCoordinate',
    'outputTerm',
    'caseProofIds',
    'cases',
    'allSourceBindingsExact',
    'allNANDEquationsExact',
    'allNodesEvaluated',
    'outputCoordinateBound',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TraceInd conclusion rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticTraceIndJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'TraceInd conclusion kind must be SemanticTraceIndJudgment0',
      { actual: judgment.kind },
    );
  }

  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TraceInd conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }

  if (!isIdentifier0(judgment.traceId)) {
    return validationReject0(
      [...path, 'traceId'],
      'TraceInd conclusion traceId must be a canonical identifier',
      { actual: judgment.traceId },
    );
  }

  for (const field of [
    'nodeOrder',
    'sourceNodeIds',
    'nandNodeIds',
    'caseProofIds',
    'cases',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `TraceInd conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }

  if (!isIdentifier0(judgment.outputNodeId)) {
    return validationReject0(
      [...path, 'outputNodeId'],
      'TraceInd conclusion outputNodeId must be a canonical identifier',
      { actual: judgment.outputNodeId },
    );
  }
  if (!isIdentifier0(judgment.outputCoordinate)) {
    return validationReject0(
      [...path, 'outputCoordinate'],
      'TraceInd conclusion outputCoordinate must be a canonical identifier',
      { actual: judgment.outputCoordinate },
    );
  }

  const outputTerm = validateTerm0(
    judgment.outputTerm,
    [...path, 'outputTerm'],
    0,
  );
  if (!outputTerm.ok) return outputTerm;

  for (const field of [
    'allSourceBindingsExact',
    'allNANDEquationsExact',
    'allNodesEvaluated',
    'outputCoordinateBound',
  ]) {
    if (judgment[field] !== true) {
      return validationReject0(
        [...path, field],
        `TraceInd conclusion ${field} must be true`,
        { actual: judgment[field] },
      );
    }
  }

  return validationAccept0({
    kind: 'SemanticTraceIndJudgmentShape0NF',
    traceId: judgment.traceId,
    caseCount: judgment.cases.length,
  });
}

function checkTraceIndRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'TraceInd rule supports only close',
      { actual: node.Payload.op },
    );
  }

  const traceCheck = validateTrace0(
    node.Payload.trace,
    [...path, 'Payload', 'trace'],
  );
  if (!traceCheck.ok) return traceCheck;

  const derived = deriveClosure0(
    traceCheck,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;

  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'TraceInd conclusion must exactly equal the computed terminal trace closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticTraceIndRule0NF',
    ruleName: 'TraceInd',
    operation: 'close',
    traceId: traceCheck.trace.traceId,
    nodeCount: traceCheck.trace.nodes.length,
    sourceNodeCount: traceCheck.nf.sourceNodeIds.length,
    nandNodeCount: traceCheck.nf.nandNodeIds.length,
    outputNodeId: traceCheck.trace.outputNodeId,
    outputCoordinate: traceCheck.trace.outputCoordinate,
    caseProofIds: [...node.Premises],
    topologicalInputClosure: true,
    exactSourceBindings: true,
    exactNANDEquations: true,
    outputCoordinateBound: true,
  });
}

function deriveClosure0(traceCheck, premises, caseProofIds, path) {
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'TraceInd closure requires premise and proof-id arrays',
      null,
    );
  }

  const traceNodes = traceCheck.trace.nodes;
  if (premises.length !== traceNodes.length
      || caseProofIds.length !== traceNodes.length) {
    return validationReject0(
      [...path, 'Premises'],
      'TraceInd requires exactly one local case record for every trace node',
      {
        expected: traceNodes.length,
        actualPremises: premises.length,
        actualProofIds: caseProofIds.length,
      },
    );
  }

  const closedById = new Map();
  const cases = [];

  for (let index = 0; index < traceNodes.length; index += 1) {
    const traceNode = traceNodes[index];
    const premise = premises[index];
    const casePath = [...path, 'Premises', index];

    if (!isPlainObject0(premise)) {
      return validationReject0(
        casePath,
        'TraceInd case premise must resolve to an earlier accepted proof node',
        { actual: premise },
      );
    }

    if (premise.RuleName !== 'Record' || premise.operation !== 'intro') {
      return validationReject0(
        casePath,
        'TraceInd case premise must be accepted Record.intro evidence',
        {
          actualRuleName: premise.RuleName,
          actualOperation: premise.operation,
        },
      );
    }

    const caseCheck = validateCaseRecord0(
      premise.Conclusion,
      traceCheck.trace.traceId,
      traceNode,
      closedById,
      casePath,
    );
    if (!caseCheck.ok) return caseCheck;

    closedById.set(traceNode.id, caseCheck.current);
    cases.push(Object.freeze({
      kind: 'SemanticTraceIndCaseResult0',
      index: traceNode.index,
      nodeId: traceNode.id,
      nodeKind: traceNode.nodeKind,
      inputIds: Object.freeze([...traceNode.inputIds]),
      sourceCoordinate: traceNode.sourceCoordinate,
      valueTerm: traceNode.valueTerm,
      equation: traceNode.equation,
      invariant: caseCheck.current,
    }));
  }

  const judgment = makeSemanticTraceIndJudgment0({
    traceId: traceCheck.trace.traceId,
    nodeOrder: traceCheck.nf.nodeOrder,
    sourceNodeIds: traceCheck.nf.sourceNodeIds,
    nandNodeIds: traceCheck.nf.nandNodeIds,
    outputNodeId: traceCheck.trace.outputNodeId,
    outputCoordinate: traceCheck.trace.outputCoordinate,
    outputTerm: traceCheck.trace.outputTerm,
    caseProofIds,
    cases,
  });

  return validationAcceptWith0({
    kind: 'SemanticTraceIndClosure0NF',
    traceId: traceCheck.trace.traceId,
    nodeCount: traceNodes.length,
    outputNodeId: traceCheck.trace.outputNodeId,
    outputCoordinate: traceCheck.trace.outputCoordinate,
  }, {
    judgment,
  });
}

function validateCaseRecord0(record, traceId, traceNode, closedById, path) {
  if (!isPlainObject0(record)) {
    return validationReject0(
      path,
      'TraceInd case conclusion must be a record judgment',
      { actual: typeof record },
    );
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'Conclusion', 'kind'],
      'TraceInd case conclusion must be SemanticRecordJudgment0',
      { actual: record.kind },
    );
  }

  const expectedRecordType = caseRecordType0(traceId, traceNode.id);
  if (record.recordType !== expectedRecordType) {
    return validationReject0(
      [...path, 'Conclusion', 'recordType'],
      'TraceInd case recordType must bind the trace and node id',
      { expected: expectedRecordType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'TraceInd case record fields must be an array',
      { actual: typeof record.fields },
    );
  }

  const uniqueDependencies = [...new Set(traceNode.inputIds)].sort(compareText0);
  const expectedNames = [
    'current',
    'equation',
    ...uniqueDependencies.map((dependencyId) => `dep.${dependencyId}`),
  ].sort(compareText0);
  const actualNames = record.fields.map((field) => field?.name ?? null);
  if (!sameCanonical0(actualNames, expectedNames)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'TraceInd case fields must contain the exact equation, current invariant, and input invariants',
      { expected: expectedNames, actual: actualNames },
    );
  }

  const fieldMap = new Map(record.fields.map((field) => [field.name, field.judgment]));
  if (!sameCanonical0(fieldMap.get('equation'), traceNode.equation)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'TraceInd case equation must exactly match the declared source or NAND equation',
      {
        nodeId: traceNode.id,
        expected: traceNode.equation,
        actual: fieldMap.get('equation'),
      },
    );
  }

  const current = fieldMap.get('current');
  if (!sameCanonical0(current, traceNode.invariant)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'TraceInd case current invariant must exactly match the declared trace value',
      {
        nodeId: traceNode.id,
        expected: traceNode.invariant,
        actual: current,
      },
    );
  }

  for (const dependencyId of uniqueDependencies) {
    const expected = closedById.get(dependencyId);
    if (expected === undefined) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'TraceInd case depends on a trace node without an earlier closed invariant',
        { nodeId: traceNode.id, dependencyId },
      );
    }

    const actual = fieldMap.get(`dep.${dependencyId}`);
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'TraceInd input invariant must exactly match the earlier evaluated trace-node invariant',
        {
          nodeId: traceNode.id,
          dependencyId,
          expected,
          actual,
        },
      );
    }
  }

  return validationAcceptWith0({
    kind: 'SemanticTraceIndCase0NF',
    traceId,
    nodeId: traceNode.id,
    nodeKind: traceNode.nodeKind,
    dependencyCount: uniqueDependencies.length,
    exactEquation: true,
    topologicalInputsClosed: true,
  }, {
    current,
  });
}

function caseRecordType0(traceId, nodeId) {
  return `TraceIndCase0.${traceId}.${nodeId}`;
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProofOblTopoInd0(
      makeSemanticProofDAG0(baseNodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofOblTopoInd0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofOblTopoInd0 threw instead of returning a reject record',
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

function requireIndex0(value, label) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new TypeError(`${label} must be a nonnegative safe integer`);
  }
}
