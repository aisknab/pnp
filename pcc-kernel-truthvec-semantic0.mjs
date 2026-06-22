import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofTransport0,
  SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0,
} from './pcc-kernel-transport-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_INPUTS = 12;
const MAX_PROGRAM_NODES = 4_096;
const MAX_OUTPUTS = 256;
const MAX_VECTOR_CELLS = 1_048_576;
const MAX_EVALUATION_STEPS = 4_194_304;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_TRUTHVEC_OPERATIONS0 = Object.freeze(['evaluate']);

export const SEMANTIC_TRUTHVEC_NODE_KINDS0 = Object.freeze([
  'Input',
  'Const',
  'NAND',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0,
  'TruthVec',
]);

export function makeSemanticTruthVecInputNode0({
  index,
  id,
} = {}) {
  requireIndex0(index, 'makeSemanticTruthVecInputNode0 index');
  requireIdentifier0(id, 'makeSemanticTruthVecInputNode0 id');
  return Object.freeze({
    kind: 'SemanticTruthVecNode0',
    version: CHECKER_VERSION,
    index,
    id,
    nodeKind: 'Input',
    inputIds: Object.freeze([]),
    value: null,
  });
}

export function makeSemanticTruthVecConstNode0({
  index,
  id,
  value,
} = {}) {
  requireIndex0(index, 'makeSemanticTruthVecConstNode0 index');
  requireIdentifier0(id, 'makeSemanticTruthVecConstNode0 id');
  requireBoolean0(value, 'makeSemanticTruthVecConstNode0 value');
  return Object.freeze({
    kind: 'SemanticTruthVecNode0',
    version: CHECKER_VERSION,
    index,
    id,
    nodeKind: 'Const',
    inputIds: Object.freeze([]),
    value,
  });
}

export function makeSemanticTruthVecNANDNode0({
  index,
  id,
  leftId,
  rightId,
} = {}) {
  requireIndex0(index, 'makeSemanticTruthVecNANDNode0 index');
  requireIdentifier0(id, 'makeSemanticTruthVecNANDNode0 id');
  requireIdentifier0(leftId, 'makeSemanticTruthVecNANDNode0 leftId');
  requireIdentifier0(rightId, 'makeSemanticTruthVecNANDNode0 rightId');
  return Object.freeze({
    kind: 'SemanticTruthVecNode0',
    version: CHECKER_VERSION,
    index,
    id,
    nodeKind: 'NAND',
    inputIds: Object.freeze([leftId, rightId]),
    value: null,
  });
}

export function makeSemanticTruthVecOutput0({
  index,
  id,
  nodeId,
} = {}) {
  requireIndex0(index, 'makeSemanticTruthVecOutput0 index');
  requireIdentifier0(id, 'makeSemanticTruthVecOutput0 id');
  requireIdentifier0(nodeId, 'makeSemanticTruthVecOutput0 nodeId');
  return Object.freeze({
    kind: 'SemanticTruthVecOutput0',
    version: CHECKER_VERSION,
    index,
    id,
    nodeId,
  });
}

export function makeSemanticTruthVecAssignment0({
  index,
  bits = [],
} = {}) {
  requireIndex0(index, 'makeSemanticTruthVecAssignment0 index');
  if (!Array.isArray(bits)) {
    throw new TypeError('makeSemanticTruthVecAssignment0 bits must be an array');
  }
  for (const bit of bits) {
    requireBoolean0(bit, 'makeSemanticTruthVecAssignment0 bit');
  }
  return Object.freeze({
    kind: 'SemanticTruthVecAssignment0',
    version: CHECKER_VERSION,
    index,
    bits: Object.freeze([...bits]),
  });
}

export function makeSemanticTruthVecDomain0({
  inputIds = [],
} = {}) {
  const inputCheck = validateInputIds0(inputIds, ['inputIds']);
  if (!inputCheck.ok) throw new TypeError(inputCheck.witness.reason);
  const assignmentCount = 2 ** inputIds.length;
  const assignments = [];
  for (let index = 0; index < assignmentCount; index += 1) {
    assignments.push(makeSemanticTruthVecAssignment0({
      index,
      bits: bitsForIndex0(index, inputIds.length),
    }));
  }
  return Object.freeze({
    kind: 'SemanticTruthVecDomain0',
    version: CHECKER_VERSION,
    inputIds: Object.freeze([...inputIds]),
    assignments: Object.freeze(assignments),
  });
}

export function makeSemanticTruthVecProgram0({
  programId,
  nodes = [],
  outputs = [],
} = {}) {
  requireIdentifier0(programId, 'makeSemanticTruthVecProgram0 programId');
  if (!Array.isArray(nodes)) {
    throw new TypeError('makeSemanticTruthVecProgram0 nodes must be an array');
  }
  if (!Array.isArray(outputs)) {
    throw new TypeError('makeSemanticTruthVecProgram0 outputs must be an array');
  }
  const program = Object.freeze({
    kind: 'SemanticTruthVecProgram0',
    version: CHECKER_VERSION,
    programId,
    nodes: Object.freeze([...nodes]),
    outputs: Object.freeze([...outputs]),
  });
  const checked = validateProgram0(program, ['program']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return program;
}

export function makeSemanticTruthVecSpec0({
  evaluationId,
  program,
  domain = undefined,
} = {}) {
  requireIdentifier0(evaluationId, 'makeSemanticTruthVecSpec0 evaluationId');
  const programCheck = validateProgram0(program, ['program']);
  if (!programCheck.ok) throw new TypeError(programCheck.witness.reason);
  const resolvedDomain = domain ?? makeSemanticTruthVecDomain0({
    inputIds: programCheck.inputIds,
  });
  const spec = Object.freeze({
    kind: 'SemanticTruthVecSpec0',
    version: CHECKER_VERSION,
    evaluationId,
    program,
    domain: resolvedDomain,
  });
  const checked = validateSpec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return spec;
}

export function deriveSemanticTruthVecJudgment0({
  spec,
} = {}) {
  const specCheck = validateSpec0(spec, ['spec']);
  if (!specCheck.ok) throw new TypeError(specCheck.witness.reason);
  const derived = deriveTruthVector0(specCheck, ['derive']);
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.judgment;
}

export function CheckSemanticKernelReadinessTruthVec0() {
  const checker = 'CheckSemanticKernelReadinessTruthVec0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessTruthVec0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofTransport0',
    proofChecker: 'CheckSemanticKernelProofTruthVec0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    truthVecOperations: [...SEMANTIC_TRUTHVEC_OPERATIONS0],
    truthVecNodeKinds: [...SEMANTIC_TRUTHVEC_NODE_KINDS0],
    canonicalBooleanCubeDomainRequired: true,
    exactInputArityRequired: true,
    exactAssignmentOrderRequired: true,
    topologicalNANDEvaluationRequired: true,
    everyOutputBitComputed: true,
    inputAndOutputOrderPreserved: true,
    boundedEvaluationRequired: true,
    callerVectorsEqualityAndCompletionAssertionsForbidden: true,
    hiddenSolverSearchOptimizationAndOracleForbidden: true,
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
        reason: 'TruthVec-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

export function CheckSemanticKernelProofTruthVec0(input) {
  const checker = 'CheckSemanticKernelProofTruthVec0';
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
        reason: 'TruthVec-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0.includes(
      node.RuleName,
    ),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofTransport0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample/IntArith/Transport sub-DAG rejected under the predecessor semantic checker',
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
    const semantic = node.RuleName === 'TruthVec'
      ? checkTruthVecRule0(node, premises, path)
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0.includes(rule),
  );
  const truthVecNodeCount = summaries.filter(
    (node) => node.RuleName === 'TruthVec',
  ).length;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofTruthVec0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofTransport0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedTruthVecOperations: [...SEMANTIC_TRUTHVEC_OPERATIONS0],
      supportedTruthVecNodeKinds: [...SEMANTIC_TRUTHVEC_NODE_KINDS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      truthVecNodeCount,
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
      {
        kind: 'SemanticTruthVecProofInput0NF',
        form: 'array',
        nodeCount: input.length,
      },
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
    {
      kind: 'SemanticTruthVecProofInput0NF',
      form: 'object',
      nodeCount: nodes.length,
    },
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
        'TruthVec-extended semantic proof node rejects undeclared fields',
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
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'TruthVec-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'TruthVec-extended semantic kernel accepts Full proof-node mode only',
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
    for (let premiseIndex = 0;
      premiseIndex < node.Premises.length;
      premiseIndex += 1) {
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
    if (node.RuleName === 'TruthVec') {
      const payload = validateTruthVecPayload0(
        node.Payload,
        [...path, 'Payload'],
      );
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
    kind: 'SemanticTruthVecProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateTruthVecPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'spec']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec payload rejects caller-supplied vectors, equality, completeness, normalization, result, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_TRUTHVEC_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'TruthVec operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_TRUTHVEC_OPERATIONS0],
      },
    );
  }
  const spec = validateSpec0(payload.spec, [...path, 'spec']);
  if (!spec.ok) return spec;
  return validationAccept0({
    kind: 'SemanticTruthVecPayload0NF',
    operation: payload.op,
    evaluationId: spec.spec.evaluationId,
  });
}

function validateInputIds0(inputIds, path) {
  if (!Array.isArray(inputIds)) {
    return validationReject0(path, 'TruthVec inputIds must be an array', {
      actual: typeof inputIds,
    });
  }
  if (inputIds.length > MAX_INPUTS) {
    return validationReject0(
      path,
      'TruthVec input arity exceeds maxInputs',
      { maxInputs: MAX_INPUTS, actual: inputIds.length },
    );
  }
  const seen = new Set();
  for (let index = 0; index < inputIds.length; index += 1) {
    const id = inputIds[index];
    if (!isIdentifier0(id)) {
      return validationReject0(
        [...path, index],
        'TruthVec input id must be a canonical identifier',
        { actual: id },
      );
    }
    if (seen.has(id)) {
      return validationReject0(
        [...path, index],
        'TruthVec input ids must be unique',
        { id },
      );
    }
    seen.add(id);
  }
  return validationAccept0({
    kind: 'SemanticTruthVecInputIds0NF',
    inputCount: inputIds.length,
    inputIds: [...inputIds],
  });
}

function validateProgramNode0(node, path, seenNodeIds, inputPhaseOpen) {
  if (!isPlainObject0(node)) {
    return validationReject0(path, 'TruthVec program node must be an object', {
      actual: typeof node,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'index', 'id', 'nodeKind', 'inputIds', 'value',
  ]);
  const unexpected = Object.keys(node).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec program node rejects undeclared result, vector, equality, solver, search, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (node.kind !== 'SemanticTruthVecNode0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec program node kind must be SemanticTruthVecNode0',
      { actual: node.kind },
    );
  }
  if (node.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec program node version must be ${CHECKER_VERSION}`,
      { actual: node.version },
    );
  }
  if (!Number.isSafeInteger(node.index) || node.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'TruthVec program node index must be a nonnegative safe integer',
      { actual: node.index },
    );
  }
  if (!isIdentifier0(node.id)) {
    return validationReject0(
      [...path, 'id'],
      'TruthVec program node id must be a canonical identifier',
      { actual: node.id },
    );
  }
  if (seenNodeIds.has(node.id)) {
    return validationReject0(
      [...path, 'id'],
      'TruthVec program node ids must be unique',
      { id: node.id },
    );
  }
  if (!SEMANTIC_TRUTHVEC_NODE_KINDS0.includes(node.nodeKind)) {
    return validationReject0(
      [...path, 'nodeKind'],
      'TruthVec program node kind is unsupported',
      {
        actual: node.nodeKind,
        supportedNodeKinds: [...SEMANTIC_TRUTHVEC_NODE_KINDS0],
      },
    );
  }
  if (!Array.isArray(node.inputIds)) {
    return validationReject0(
      [...path, 'inputIds'],
      'TruthVec program node inputIds must be an array',
      { actual: typeof node.inputIds },
    );
  }

  if (node.nodeKind === 'Input') {
    if (!inputPhaseOpen) {
      return validationReject0(
        [...path, 'nodeKind'],
        'TruthVec input nodes must form the initial canonical input block',
        { id: node.id },
      );
    }
    if (node.inputIds.length !== 0 || node.value !== null) {
      return validationReject0(
        path,
        'TruthVec Input nodes require empty inputIds and null value',
        { actualInputIds: node.inputIds, actualValue: node.value },
      );
    }
  } else if (node.nodeKind === 'Const') {
    if (node.inputIds.length !== 0 || typeof node.value !== 'boolean') {
      return validationReject0(
        path,
        'TruthVec Const nodes require empty inputIds and a Boolean value',
        { actualInputIds: node.inputIds, actualValue: node.value },
      );
    }
  } else {
    if (node.inputIds.length !== 2 || node.value !== null) {
      return validationReject0(
        path,
        'TruthVec NAND nodes require exactly two inputIds and null value',
        { actualInputIds: node.inputIds, actualValue: node.value },
      );
    }
    for (let index = 0; index < node.inputIds.length; index += 1) {
      const inputId = node.inputIds[index];
      if (!isIdentifier0(inputId)) {
        return validationReject0(
          [...path, 'inputIds', index],
          'TruthVec NAND input id must be a canonical identifier',
          { actual: inputId },
        );
      }
      if (!seenNodeIds.has(inputId)) {
        return validationReject0(
          [...path, 'inputIds', index],
          'TruthVec NAND input must reference an earlier program node',
          { nodeId: node.id, inputId },
        );
      }
    }
  }

  return validationAcceptWith0({
    kind: 'SemanticTruthVecProgramNode0NF',
    index: node.index,
    id: node.id,
    nodeKind: node.nodeKind,
  }, { node });
}

function validateOutput0(output, path, nodeById, seenOutputIds) {
  if (!isPlainObject0(output)) {
    return validationReject0(path, 'TruthVec output must be an object', {
      actual: typeof output,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'index', 'id', 'nodeId']);
  const unexpected = Object.keys(output).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec output rejects undeclared vector, equality, or result fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (output.kind !== 'SemanticTruthVecOutput0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec output kind must be SemanticTruthVecOutput0',
      { actual: output.kind },
    );
  }
  if (output.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec output version must be ${CHECKER_VERSION}`,
      { actual: output.version },
    );
  }
  if (!Number.isSafeInteger(output.index) || output.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'TruthVec output index must be a nonnegative safe integer',
      { actual: output.index },
    );
  }
  if (!isIdentifier0(output.id) || !isIdentifier0(output.nodeId)) {
    return validationReject0(
      path,
      'TruthVec output id and nodeId must be canonical identifiers',
      { id: output.id, nodeId: output.nodeId },
    );
  }
  if (seenOutputIds.has(output.id)) {
    return validationReject0(
      [...path, 'id'],
      'TruthVec output ids must be unique',
      { id: output.id },
    );
  }
  if (!nodeById.has(output.nodeId)) {
    return validationReject0(
      [...path, 'nodeId'],
      'TruthVec output must reference a declared program node',
      { nodeId: output.nodeId },
    );
  }
  return validationAcceptWith0({
    kind: 'SemanticTruthVecOutput0NF',
    index: output.index,
    id: output.id,
    nodeId: output.nodeId,
  }, { output });
}

function validateProgram0(program, path) {
  if (!isPlainObject0(program)) {
    return validationReject0(path, 'TruthVec program must be an object', {
      actual: typeof program,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'programId', 'nodes', 'outputs',
  ]);
  const unexpected = Object.keys(program).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec program rejects caller-supplied vectors, domain completeness, equality, normalization, solver, search, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (program.kind !== 'SemanticTruthVecProgram0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec program kind must be SemanticTruthVecProgram0',
      { actual: program.kind },
    );
  }
  if (program.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec program version must be ${CHECKER_VERSION}`,
      { actual: program.version },
    );
  }
  if (!isIdentifier0(program.programId)) {
    return validationReject0(
      [...path, 'programId'],
      'TruthVec programId must be a canonical identifier',
      { actual: program.programId },
    );
  }
  if (!Array.isArray(program.nodes)
      || program.nodes.length === 0
      || program.nodes.length > MAX_PROGRAM_NODES) {
    return validationReject0(
      [...path, 'nodes'],
      'TruthVec program nodes must be a nonempty bounded array',
      {
        maxProgramNodes: MAX_PROGRAM_NODES,
        actual: Array.isArray(program.nodes) ? program.nodes.length : typeof program.nodes,
      },
    );
  }
  if (!Array.isArray(program.outputs)
      || program.outputs.length === 0
      || program.outputs.length > MAX_OUTPUTS) {
    return validationReject0(
      [...path, 'outputs'],
      'TruthVec program outputs must be a nonempty bounded array',
      {
        maxOutputs: MAX_OUTPUTS,
        actual: Array.isArray(program.outputs) ? program.outputs.length : typeof program.outputs,
      },
    );
  }

  const seenNodeIds = new Set();
  const nodeById = new Map();
  const inputIds = [];
  let inputPhaseOpen = true;
  for (let index = 0; index < program.nodes.length; index += 1) {
    const nodeCheck = validateProgramNode0(
      program.nodes[index],
      [...path, 'nodes', index],
      seenNodeIds,
      inputPhaseOpen,
    );
    if (!nodeCheck.ok) return nodeCheck;
    if (nodeCheck.node.index !== index) {
      return validationReject0(
        [...path, 'nodes', index, 'index'],
        'TruthVec program node indices must be exact consecutive coordinates',
        { expected: index, actual: nodeCheck.node.index },
      );
    }
    if (nodeCheck.node.nodeKind === 'Input') {
      inputIds.push(nodeCheck.node.id);
    } else {
      inputPhaseOpen = false;
    }
    seenNodeIds.add(nodeCheck.node.id);
    nodeById.set(nodeCheck.node.id, nodeCheck.node);
  }
  const inputCheck = validateInputIds0(inputIds, [...path, 'inputIds']);
  if (!inputCheck.ok) return inputCheck;

  const seenOutputIds = new Set();
  for (let index = 0; index < program.outputs.length; index += 1) {
    const outputCheck = validateOutput0(
      program.outputs[index],
      [...path, 'outputs', index],
      nodeById,
      seenOutputIds,
    );
    if (!outputCheck.ok) return outputCheck;
    if (outputCheck.output.index !== index) {
      return validationReject0(
        [...path, 'outputs', index, 'index'],
        'TruthVec output indices must be exact consecutive coordinates',
        { expected: index, actual: outputCheck.output.index },
      );
    }
    seenOutputIds.add(outputCheck.output.id);
  }

  return validationAcceptWith0({
    kind: 'SemanticTruthVecProgram0NF',
    programId: program.programId,
    nodeCount: program.nodes.length,
    inputCount: inputIds.length,
    inputIds,
    outputCount: program.outputs.length,
    outputIds: program.outputs.map((output) => output.id),
    topologicalNANDProgram: true,
    inputBlockCanonical: true,
    outputOrderCanonical: true,
  }, {
    program,
    nodeById,
    inputIds,
  });
}

function validateAssignment0(assignment, path, inputCount) {
  if (!isPlainObject0(assignment)) {
    return validationReject0(path, 'TruthVec assignment must be an object', {
      actual: typeof assignment,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'index', 'bits']);
  const unexpected = Object.keys(assignment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec assignment rejects undeclared value, result, vector, or completion fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (assignment.kind !== 'SemanticTruthVecAssignment0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec assignment kind must be SemanticTruthVecAssignment0',
      { actual: assignment.kind },
    );
  }
  if (assignment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec assignment version must be ${CHECKER_VERSION}`,
      { actual: assignment.version },
    );
  }
  if (!Number.isSafeInteger(assignment.index) || assignment.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'TruthVec assignment index must be a nonnegative safe integer',
      { actual: assignment.index },
    );
  }
  if (!Array.isArray(assignment.bits)
      || assignment.bits.length !== inputCount) {
    return validationReject0(
      [...path, 'bits'],
      'TruthVec assignment bits must exactly match the input arity',
      {
        expectedArity: inputCount,
        actual: Array.isArray(assignment.bits)
          ? assignment.bits.length
          : typeof assignment.bits,
      },
    );
  }
  for (let index = 0; index < assignment.bits.length; index += 1) {
    if (typeof assignment.bits[index] !== 'boolean') {
      return validationReject0(
        [...path, 'bits', index],
        'TruthVec assignment bits must be Boolean',
        { actual: assignment.bits[index] },
      );
    }
  }
  return validationAcceptWith0({
    kind: 'SemanticTruthVecAssignment0NF',
    index: assignment.index,
    bits: [...assignment.bits],
  }, { assignment });
}

function validateDomain0(domain, path, expectedInputIds) {
  if (!isPlainObject0(domain)) {
    return validationReject0(path, 'TruthVec domain must be an object', {
      actual: typeof domain,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'inputIds', 'assignments']);
  const unexpected = Object.keys(domain).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec domain rejects caller-supplied completeness, count, vector, equality, solver, search, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (domain.kind !== 'SemanticTruthVecDomain0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec domain kind must be SemanticTruthVecDomain0',
      { actual: domain.kind },
    );
  }
  if (domain.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec domain version must be ${CHECKER_VERSION}`,
      { actual: domain.version },
    );
  }
  const inputCheck = validateInputIds0(domain.inputIds, [...path, 'inputIds']);
  if (!inputCheck.ok) return inputCheck;
  if (!sameCanonical0(domain.inputIds, expectedInputIds)) {
    return validationReject0(
      [...path, 'inputIds'],
      'TruthVec domain input order must exactly match the program input block',
      { expected: expectedInputIds, actual: domain.inputIds },
    );
  }
  if (!Array.isArray(domain.assignments)) {
    return validationReject0(
      [...path, 'assignments'],
      'TruthVec domain assignments must be an array',
      { actual: typeof domain.assignments },
    );
  }
  const expectedCount = 2 ** expectedInputIds.length;
  if (domain.assignments.length !== expectedCount) {
    return validationReject0(
      [...path, 'assignments'],
      'TruthVec domain must contain the complete Boolean cube',
      { expectedCount, actual: domain.assignments.length },
    );
  }
  for (let index = 0; index < domain.assignments.length; index += 1) {
    const assignmentCheck = validateAssignment0(
      domain.assignments[index],
      [...path, 'assignments', index],
      expectedInputIds.length,
    );
    if (!assignmentCheck.ok) return assignmentCheck;
    if (assignmentCheck.assignment.index !== index) {
      return validationReject0(
        [...path, 'assignments', index, 'index'],
        'TruthVec assignment indices must be exact consecutive domain coordinates',
        { expected: index, actual: assignmentCheck.assignment.index },
      );
    }
    const expectedBits = bitsForIndex0(index, expectedInputIds.length);
    if (!sameCanonical0(assignmentCheck.assignment.bits, expectedBits)) {
      return validationReject0(
        [...path, 'assignments', index, 'bits'],
        'TruthVec assignments must be in canonical binary lexicographic order',
        { expected: expectedBits, actual: assignmentCheck.assignment.bits },
      );
    }
  }
  return validationAcceptWith0({
    kind: 'SemanticTruthVecDomain0NF',
    inputIds: [...expectedInputIds],
    inputCount: expectedInputIds.length,
    assignmentCount: expectedCount,
    completeBooleanCube: true,
    canonicalAssignmentOrder: true,
  }, { domain });
}

function validateSpec0(spec, path) {
  if (!isPlainObject0(spec)) {
    return validationReject0(path, 'TruthVec specification must be an object', {
      actual: typeof spec,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'evaluationId', 'program', 'domain',
  ]);
  const unexpected = Object.keys(spec).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec specification rejects caller-supplied vectors, equality, completeness, normalization, result, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (spec.kind !== 'SemanticTruthVecSpec0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec specification kind must be SemanticTruthVecSpec0',
      { actual: spec.kind },
    );
  }
  if (spec.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec specification version must be ${CHECKER_VERSION}`,
      { actual: spec.version },
    );
  }
  if (!isIdentifier0(spec.evaluationId)) {
    return validationReject0(
      [...path, 'evaluationId'],
      'TruthVec evaluationId must be a canonical identifier',
      { actual: spec.evaluationId },
    );
  }
  const program = validateProgram0(spec.program, [...path, 'program']);
  if (!program.ok) return program;
  const domain = validateDomain0(
    spec.domain,
    [...path, 'domain'],
    program.inputIds,
  );
  if (!domain.ok) return domain;

  const vectorCells = domain.nf.assignmentCount * program.nf.outputCount;
  if (vectorCells > MAX_VECTOR_CELLS) {
    return validationReject0(
      path,
      'TruthVec output-vector cell count exceeds maxVectorCells',
      { maxVectorCells: MAX_VECTOR_CELLS, actual: vectorCells },
    );
  }
  const evaluationSteps = domain.nf.assignmentCount * program.nf.nodeCount;
  if (evaluationSteps > MAX_EVALUATION_STEPS) {
    return validationReject0(
      path,
      'TruthVec evaluation exceeds maxEvaluationSteps',
      { maxEvaluationSteps: MAX_EVALUATION_STEPS, actual: evaluationSteps },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticTruthVecSpec0NF',
    evaluationId: spec.evaluationId,
    programId: program.program.programId,
    inputIds: [...program.inputIds],
    inputCount: program.inputIds.length,
    outputIds: program.program.outputs.map((output) => output.id),
    outputCount: program.program.outputs.length,
    assignmentCount: domain.nf.assignmentCount,
    vectorCells,
    evaluationSteps,
    boundedEvaluation: true,
  }, {
    spec,
    program,
    domain,
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'TruthVec conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'evaluationId', 'program', 'domain',
    'inputIds', 'outputIds', 'assignmentCount', 'outputCount',
    'rows', 'vectors', 'programDigest', 'domainDigest', 'vectorDigest',
    'exactBooleanCubeDomain', 'exactInputArity', 'exactAssignmentOrder',
    'topologicalNANDEvaluation', 'allAssignmentsEvaluated',
    'everyOutputBitComputed', 'inputOrderPreserved', 'outputOrderPreserved',
    'boundedEvaluation', 'noSolverSearchOptimizationOrOracleUsed',
    'terminalJudgmentComputed',
  ]);
  const unexpected = Object.keys(judgment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'TruthVec conclusion rejects undeclared equality, completeness, normalization, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticTruthVecJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'TruthVec conclusion kind must be SemanticTruthVecJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `TruthVec conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  for (const field of ['inputIds', 'outputIds', 'rows', 'vectors']) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `TruthVec conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }
  for (let index = 0; index < judgment.rows.length; index += 1) {
    const row = judgment.rows[index];
    const rowPath = [...path, 'rows', index];
    if (!isPlainObject0(row)) {
      return validationReject0(rowPath, 'TruthVec row must be an object', {
        actual: typeof row,
      });
    }
    const allowedRowKeys = new Set([
      'kind', 'version', 'index', 'assignment', 'outputValues',
    ]);
    const unexpectedRow = Object.keys(row)
      .filter((key) => !allowedRowKeys.has(key));
    if (unexpectedRow.length !== 0) {
      return validationReject0(
        [...rowPath, unexpectedRow[0]],
        'TruthVec row rejects undeclared result or completion fields',
        { unexpectedFields: unexpectedRow.sort() },
      );
    }
    if (row.kind !== 'SemanticTruthVecRow0'
        || row.version !== CHECKER_VERSION
        || row.index !== index
        || !Array.isArray(row.outputValues)) {
      return validationReject0(
        rowPath,
        'TruthVec row has invalid canonical fields',
        { actual: row },
      );
    }
    const assignment = validateAssignment0(
      row.assignment,
      [...rowPath, 'assignment'],
      judgment.inputIds.length,
    );
    if (!assignment.ok) return assignment;
    for (let bitIndex = 0; bitIndex < row.outputValues.length; bitIndex += 1) {
      if (typeof row.outputValues[bitIndex] !== 'boolean') {
        return validationReject0(
          [...rowPath, 'outputValues', bitIndex],
          'TruthVec row output values must be Boolean',
          { actual: row.outputValues[bitIndex] },
        );
      }
    }
  }
  for (let index = 0; index < judgment.vectors.length; index += 1) {
    const vector = judgment.vectors[index];
    const vectorPath = [...path, 'vectors', index];
    if (!isPlainObject0(vector)) {
      return validationReject0(vectorPath, 'TruthVec vector must be an object', {
        actual: typeof vector,
      });
    }
    const allowedVectorKeys = new Set([
      'kind', 'version', 'index', 'outputId', 'nodeId', 'bits',
    ]);
    const unexpectedVector = Object.keys(vector)
      .filter((key) => !allowedVectorKeys.has(key));
    if (unexpectedVector.length !== 0) {
      return validationReject0(
        [...vectorPath, unexpectedVector[0]],
        'TruthVec vector rejects undeclared equality or completeness fields',
        { unexpectedFields: unexpectedVector.sort() },
      );
    }
    if (vector.kind !== 'SemanticTruthVector0'
        || vector.version !== CHECKER_VERSION
        || vector.index !== index
        || !isIdentifier0(vector.outputId)
        || !isIdentifier0(vector.nodeId)
        || !Array.isArray(vector.bits)) {
      return validationReject0(
        vectorPath,
        'TruthVec vector has invalid canonical fields',
        { actual: vector },
      );
    }
    for (let bitIndex = 0; bitIndex < vector.bits.length; bitIndex += 1) {
      if (typeof vector.bits[bitIndex] !== 'boolean') {
        return validationReject0(
          [...vectorPath, 'bits', bitIndex],
          'TruthVec vector bits must be Boolean',
          { actual: vector.bits[bitIndex] },
        );
      }
    }
  }
  return validationAccept0({
    kind: 'SemanticTruthVecJudgmentShape0NF',
    evaluationId: judgment.evaluationId,
    assignmentCount: judgment.assignmentCount,
    outputCount: judgment.outputCount,
  });
}

function checkTruthVecRule0(node, premises, path) {
  if (node.Payload.op !== 'evaluate') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'TruthVec rule supports only evaluate',
      { actual: node.Payload.op },
    );
  }
  if (premises.length !== 0 || node.Premises.length !== 0) {
    return validationReject0(
      [...path, 'Premises'],
      'TruthVec evaluate is a closed exact finite computation and must not consume premises',
      { actualPremiseIds: node.Premises },
    );
  }
  const specCheck = validateSpec0(
    node.Payload.spec,
    [...path, 'Payload', 'spec'],
  );
  if (!specCheck.ok) return specCheck;
  const derived = deriveTruthVector0(specCheck, path);
  if (!derived.ok) return derived;
  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'TruthVec conclusion must exactly equal the computed ordered Boolean vectors',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }
  return validationAccept0({
    kind: 'SemanticTruthVecRule0NF',
    ruleName: 'TruthVec',
    operation: 'evaluate',
    evaluationId: specCheck.spec.evaluationId,
    programId: specCheck.program.program.programId,
    inputCount: specCheck.program.inputIds.length,
    outputCount: specCheck.program.program.outputs.length,
    assignmentCount: specCheck.domain.nf.assignmentCount,
    vectorCells: specCheck.nf.vectorCells,
    everyOutputBitComputed: true,
  });
}

function deriveTruthVector0(specCheck, path) {
  const program = specCheck.program.program;
  const inputIds = specCheck.program.inputIds;
  const inputIndexById = new Map(
    inputIds.map((id, index) => [id, index]),
  );
  const rows = [];
  const vectorBits = program.outputs.map(() => []);

  for (let assignmentIndex = 0;
    assignmentIndex < specCheck.domain.domain.assignments.length;
    assignmentIndex += 1) {
    const assignment = specCheck.domain.domain.assignments[assignmentIndex];
    const valueByNodeId = new Map();
    for (const node of program.nodes) {
      let value;
      if (node.nodeKind === 'Input') {
        const inputIndex = inputIndexById.get(node.id);
        if (inputIndex === undefined) {
          return validationReject0(
            [...path, 'program', 'nodes', node.index],
            'TruthVec internal input index resolution failed',
            { nodeId: node.id },
          );
        }
        value = assignment.bits[inputIndex];
      } else if (node.nodeKind === 'Const') {
        value = node.value;
      } else {
        const left = valueByNodeId.get(node.inputIds[0]);
        const right = valueByNodeId.get(node.inputIds[1]);
        if (typeof left !== 'boolean' || typeof right !== 'boolean') {
          return validationReject0(
            [...path, 'program', 'nodes', node.index, 'inputIds'],
            'TruthVec NAND inputs must have earlier computed Boolean values',
            { nodeId: node.id, inputIds: node.inputIds },
          );
        }
        value = !(left && right);
      }
      valueByNodeId.set(node.id, value);
    }

    const outputValues = [];
    for (let outputIndex = 0;
      outputIndex < program.outputs.length;
      outputIndex += 1) {
      const output = program.outputs[outputIndex];
      const value = valueByNodeId.get(output.nodeId);
      if (typeof value !== 'boolean') {
        return validationReject0(
          [...path, 'program', 'outputs', outputIndex, 'nodeId'],
          'TruthVec output node must have a computed Boolean value',
          { outputId: output.id, nodeId: output.nodeId },
        );
      }
      outputValues.push(value);
      vectorBits[outputIndex].push(value);
    }
    rows.push(Object.freeze({
      kind: 'SemanticTruthVecRow0',
      version: CHECKER_VERSION,
      index: assignmentIndex,
      assignment,
      outputValues: Object.freeze(outputValues),
    }));
  }

  const vectors = program.outputs.map((output, index) => Object.freeze({
    kind: 'SemanticTruthVector0',
    version: CHECKER_VERSION,
    index,
    outputId: output.id,
    nodeId: output.nodeId,
    bits: Object.freeze(vectorBits[index]),
  }));

  const judgment = Object.freeze({
    kind: 'SemanticTruthVecJudgment0',
    version: CHECKER_VERSION,
    evaluationId: specCheck.spec.evaluationId,
    program,
    domain: specCheck.domain.domain,
    inputIds: Object.freeze([...inputIds]),
    outputIds: Object.freeze(program.outputs.map((output) => output.id)),
    assignmentCount: specCheck.domain.nf.assignmentCount,
    outputCount: program.outputs.length,
    rows: Object.freeze(rows),
    vectors: Object.freeze(vectors),
    programDigest: digestCanonical0(program),
    domainDigest: digestCanonical0(specCheck.domain.domain),
    vectorDigest: digestCanonical0(vectors),
    exactBooleanCubeDomain: true,
    exactInputArity: true,
    exactAssignmentOrder: true,
    topologicalNANDEvaluation: true,
    allAssignmentsEvaluated: true,
    everyOutputBitComputed: true,
    inputOrderPreserved: true,
    outputOrderPreserved: true,
    boundedEvaluation: true,
    noSolverSearchOptimizationOrOracleUsed: true,
    terminalJudgmentComputed: true,
  });
  return validationAcceptWith0({
    kind: 'SemanticTruthVecEvaluation0NF',
    evaluationId: specCheck.spec.evaluationId,
    programId: program.programId,
    inputCount: inputIds.length,
    outputCount: program.outputs.length,
    assignmentCount: specCheck.domain.nf.assignmentCount,
    vectorCells: specCheck.nf.vectorCells,
  }, { judgment });
}

function bitsForIndex0(index, width) {
  const bits = [];
  for (let position = 0; position < width; position += 1) {
    const shift = width - position - 1;
    bits.push(((index >> shift) & 1) === 1);
  }
  return bits;
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofTransport0(
      makeSemanticProofDAG0(nodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofTransport0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofTransport0 threw instead of returning a reject record',
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

function requireIndex0(value, label) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new TypeError(`${label} must be a nonnegative safe integer`);
  }
}

function requireBoolean0(value, label) {
  if (typeof value !== 'boolean') {
    throw new TypeError(`${label} must be Boolean`);
  }
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
