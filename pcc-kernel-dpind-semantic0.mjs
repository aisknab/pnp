import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofFiniteExhaust0,
  SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0,
} from './pcc-kernel-finiteexhaust-semantic0.mjs';

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
const MAX_DP_STATES = 100_000;
const MAX_TERM_DEPTH = 256;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_DPIND_OPERATIONS0 = Object.freeze(['close']);
export const SEMANTIC_DP_STATE_KINDS0 = Object.freeze(['base', 'step']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0,
  'DPInd',
]);

/**
 * Constructs a base state. The value defaults to the explicit base term, so a
 * generator can use an Eq.refl proof. The checker independently verifies the
 * exact base equation and closed value sort.
 */
export function makeSemanticDPBaseState0({
  index,
  id,
  baseTerm,
  value = null,
} = {}) {
  requireIndex0(index, 'makeSemanticDPBaseState0 index');
  requireIdentifier0(id, 'makeSemanticDPBaseState0 id');
  if (!isPlainObject0(baseTerm)) {
    throw new TypeError(
      'makeSemanticDPBaseState0 baseTerm must be a semantic term object',
    );
  }

  const actualValue = value ?? baseTerm;
  if (!isPlainObject0(actualValue)) {
    throw new TypeError(
      'makeSemanticDPBaseState0 value must be a semantic term object',
    );
  }

  const baseCheck = validateClosedTerm0(baseTerm, ['baseTerm'], 0);
  if (!baseCheck.ok) throw new TypeError(baseCheck.witness.reason);
  const valueCheck = validateClosedTerm0(actualValue, ['value'], 0);
  if (!valueCheck.ok) throw new TypeError(valueCheck.witness.reason);
  if (baseCheck.sort !== valueCheck.sort) {
    throw new TypeError(
      'makeSemanticDPBaseState0 value sort must equal baseTerm sort',
    );
  }

  return Object.freeze({
    kind: 'SemanticDPState0',
    version: CHECKER_VERSION,
    stateKind: 'base',
    index,
    id,
    predecessorIds: Object.freeze([]),
    operator: null,
    baseTerm,
    recurrenceTerm: null,
    value: actualValue,
    equation: makeSemanticEqJudgment0(actualValue, baseTerm),
  });
}

/**
 * Constructs a recurrence state. Its recurrence term is the explicit operator
 * application to predecessor values in predecessor order. Operators whose
 * names encode minimization, maximization, search, or an oracle are rejected.
 */
export function makeSemanticDPStepState0({
  index,
  id,
  predecessorIds = [],
  predecessorValues = [],
  operator,
  valueSort,
  value = null,
} = {}) {
  requireIndex0(index, 'makeSemanticDPStepState0 index');
  requireIdentifier0(id, 'makeSemanticDPStepState0 id');
  requireSafeOperator0(operator, 'makeSemanticDPStepState0 operator');
  requireText0(valueSort, 'makeSemanticDPStepState0 valueSort');

  if (!Array.isArray(predecessorIds) || predecessorIds.length === 0) {
    throw new TypeError(
      'makeSemanticDPStepState0 predecessorIds must be a nonempty array',
    );
  }
  if (!Array.isArray(predecessorValues)
      || predecessorValues.length !== predecessorIds.length) {
    throw new TypeError(
      'makeSemanticDPStepState0 predecessorValues must match predecessorIds',
    );
  }

  const seen = new Set();
  for (let position = 0; position < predecessorIds.length; position += 1) {
    requireIdentifier0(
      predecessorIds[position],
      'makeSemanticDPStepState0 predecessor id',
    );
    if (seen.has(predecessorIds[position])) {
      throw new TypeError(
        'makeSemanticDPStepState0 predecessorIds must be unique',
      );
    }
    seen.add(predecessorIds[position]);

    const checked = validateClosedTerm0(
      predecessorValues[position],
      ['predecessorValues', position],
      0,
    );
    if (!checked.ok) throw new TypeError(checked.witness.reason);
    if (checked.sort !== valueSort) {
      throw new TypeError(
        'makeSemanticDPStepState0 predecessor value sort must equal valueSort',
      );
    }
  }

  const recurrenceTerm = makeSemanticApp0(
    operator,
    predecessorValues,
    valueSort,
  );
  const actualValue = value ?? recurrenceTerm;
  const valueCheck = validateClosedTerm0(actualValue, ['value'], 0);
  if (!valueCheck.ok) throw new TypeError(valueCheck.witness.reason);
  if (valueCheck.sort !== valueSort) {
    throw new TypeError(
      'makeSemanticDPStepState0 value sort must equal valueSort',
    );
  }

  return Object.freeze({
    kind: 'SemanticDPState0',
    version: CHECKER_VERSION,
    stateKind: 'step',
    index,
    id,
    predecessorIds: Object.freeze([...predecessorIds]),
    operator,
    baseTerm: null,
    recurrenceTerm,
    value: actualValue,
    equation: makeSemanticEqJudgment0(actualValue, recurrenceTerm),
  });
}

/**
 * Constructs the explicit finite state graph used by DPInd. The constructor
 * sorts by declared index for generator convenience; the checker revalidates
 * consecutive indices, the base prefix, all predecessor edges, recurrence
 * terms, terminal reachability, and the absence of hidden optimization fields.
 */
export function makeSemanticDPProgram0({
  programId,
  valueSort,
  states = [],
  terminalStateId,
  terminalCoordinate,
} = {}) {
  requireIdentifier0(programId, 'makeSemanticDPProgram0 programId');
  requireText0(valueSort, 'makeSemanticDPProgram0 valueSort');
  requireIdentifier0(
    terminalStateId,
    'makeSemanticDPProgram0 terminalStateId',
  );
  requireIdentifier0(
    terminalCoordinate,
    'makeSemanticDPProgram0 terminalCoordinate',
  );
  if (!Array.isArray(states) || states.length === 0) {
    throw new TypeError('makeSemanticDPProgram0 states must be a nonempty array');
  }

  const orderedStates = [...states].sort((left, right) => left.index - right.index);
  const program = Object.freeze({
    kind: 'SemanticDPProgram0',
    version: CHECKER_VERSION,
    programId,
    valueSort,
    states: Object.freeze(orderedStates),
    terminalStateId,
    terminalCoordinate,
  });

  const checked = validateProgram0(program, ['program']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return program;
}

/**
 * A local DP state case is accepted Record.intro evidence. It binds the exact
 * state equation and value, plus the exact previously evaluated value of every
 * declared predecessor.
 */
export function makeSemanticDPIndCase0({
  programId,
  stateId,
  equation,
  value,
  dependencyValues = [],
} = {}) {
  requireIdentifier0(programId, 'makeSemanticDPIndCase0 programId');
  requireIdentifier0(stateId, 'makeSemanticDPIndCase0 stateId');
  if (!isPlainObject0(equation)) {
    throw new TypeError(
      'makeSemanticDPIndCase0 equation must be a semantic judgment object',
    );
  }
  if (!isPlainObject0(value)) {
    throw new TypeError(
      'makeSemanticDPIndCase0 value must be a semantic term object',
    );
  }
  if (!Array.isArray(dependencyValues)) {
    throw new TypeError(
      'makeSemanticDPIndCase0 dependencyValues must be an array',
    );
  }

  const fields = [
    makeSemanticRecordField0('equation', equation),
    makeSemanticRecordField0(
      'value',
      makeSemanticEqJudgment0(value, value),
    ),
  ];

  const dependencyIds = new Set();
  for (const entry of dependencyValues) {
    if (!isPlainObject0(entry)) {
      throw new TypeError(
        'makeSemanticDPIndCase0 dependency entry must be an object',
      );
    }
    requireIdentifier0(
      entry.stateId,
      'makeSemanticDPIndCase0 dependency stateId',
    );
    if (dependencyIds.has(entry.stateId)) {
      throw new TypeError(
        'makeSemanticDPIndCase0 dependency stateIds must be unique',
      );
    }
    dependencyIds.add(entry.stateId);
    fields.push(makeSemanticRecordField0(
      `dep.${entry.stateId}`,
      makeSemanticEqJudgment0(entry.value, entry.value),
    ));
  }
  fields.sort((left, right) => compareText0(left.name, right.name));

  return makeSemanticRecordJudgment0(
    caseRecordType0(programId, stateId),
    fields,
  );
}

export function makeSemanticDPIndJudgment0({
  programId,
  valueSort,
  stateOrder,
  baseStateIds,
  stepStateIds,
  terminalStateId,
  terminalCoordinate,
  terminalValue,
  caseProofIds,
  cases,
} = {}) {
  requireIdentifier0(programId, 'makeSemanticDPIndJudgment0 programId');
  requireText0(valueSort, 'makeSemanticDPIndJudgment0 valueSort');
  requireIdentifier0(
    terminalStateId,
    'makeSemanticDPIndJudgment0 terminalStateId',
  );
  requireIdentifier0(
    terminalCoordinate,
    'makeSemanticDPIndJudgment0 terminalCoordinate',
  );
  for (const [name, value] of Object.entries({
    stateOrder,
    baseStateIds,
    stepStateIds,
    caseProofIds,
    cases,
  })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticDPIndJudgment0 ${name} must be an array`);
    }
  }

  const terminalJudgment = Object.freeze({
    kind: 'SemanticDPResultJudgment0',
    version: CHECKER_VERSION,
    programId,
    stateId: terminalStateId,
    coordinate: terminalCoordinate,
    value: terminalValue,
  });

  return Object.freeze({
    kind: 'SemanticDPIndJudgment0',
    version: CHECKER_VERSION,
    programId,
    valueSort,
    stateOrder: Object.freeze([...stateOrder]),
    baseStateIds: Object.freeze([...baseStateIds]),
    stepStateIds: Object.freeze([...stepStateIds]),
    stateCount: stateOrder.length,
    baseStateCount: baseStateIds.length,
    stepStateCount: stepStateIds.length,
    terminalStateId,
    terminalCoordinate,
    terminalValue,
    terminalJudgment,
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    canonicalBasePrefix: true,
    evaluationOrderWellFounded: true,
    predecessorCoverageComplete: true,
    recurrenceEvidenceExact: true,
    allStatesEvaluated: true,
    allStatesContributeToTerminal: true,
    hiddenOptimizationAbsent: true,
    terminalStateComputed: true,
  });
}

/**
 * Generator helper. The checker recomputes the same terminal closure and never
 * trusts caller-supplied optimum, completeness, or evaluation-order flags.
 */
export function deriveSemanticDPIndJudgment0({
  program,
  caseRecords,
  caseProofIds,
} = {}) {
  const programCheck = validateProgram0(program, ['program']);
  if (!programCheck.ok) throw new TypeError(programCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError('deriveSemanticDPIndJudgment0 requires case arrays');
  }

  const derived = deriveClosure0(
    programCheck,
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

export function CheckSemanticKernelReadinessDPInd0() {
  const checker = 'CheckSemanticKernelReadinessDPInd0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessDPInd0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofFiniteExhaust0',
    proofChecker: 'CheckSemanticKernelProofDPInd0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    dpIndOperations: [...SEMANTIC_DPIND_OPERATIONS0],
    explicitFiniteStateGraphRequired: true,
    canonicalBasePrefixRequired: true,
    predecessorCompleteRecurrencesRequired: true,
    wellFoundedEvaluationOrderRequired: true,
    acceptedLocalCasesRequired: true,
    allStatesContributeToTerminalRequired: true,
    terminalJudgmentComputed: true,
    hiddenOptimizationForbidden: true,
    optimumAndOracleAssertionsForbidden: true,
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
        reason: 'DPInd-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks predecessor rule families with the merged FiniteExhaust checker, then
 * checks DPInd as exact induction over a finite, predecessor-complete state DAG.
 */
export function CheckSemanticKernelProofDPInd0(input) {
  const checker = 'CheckSemanticKernelProofDPInd0';
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
        reason: 'DPInd-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofFiniteExhaust0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust sub-DAG rejected under the predecessor semantic checker',
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
    if (node.RuleName === 'DPInd') {
      semantic = checkDPIndRule0(node, premises, path);
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0.includes(rule),
  );
  const dpIndNodeCount = summaries.filter(
    (node) => node.RuleName === 'DPInd',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofDPInd0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofFiniteExhaust0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_DPIND0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedDPIndOperations: [...SEMANTIC_DPIND_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      dpIndNodeCount,
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
      { kind: 'SemanticDPIndProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticDPIndProofInput0NF', form: 'object', nodeCount: nodes.length },
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
        'DPInd-extended semantic proof node rejects undeclared fields',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'DPInd-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'DPInd-extended semantic kernel accepts Full mode only',
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

    if (node.RuleName === 'DPInd') {
      const payload = validateDPIndPayload0(node.Payload, [...path, 'Payload']);
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
    kind: 'SemanticDPIndProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateDPIndPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'program']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'DPInd payload rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (!SEMANTIC_DPIND_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'DPInd operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_DPIND_OPERATIONS0],
      },
    );
  }

  return validateProgram0(payload.program, [...path, 'program']);
}

function validateProgram0(program, path) {
  if (!isPlainObject0(program)) {
    return validationReject0(path, 'DPInd program must be an object', {
      actual: typeof program,
    });
  }

  const allowedProgramKeys = new Set([
    'kind',
    'version',
    'programId',
    'valueSort',
    'states',
    'terminalStateId',
    'terminalCoordinate',
  ]);
  const unexpectedProgramKeys = Object.keys(program)
    .filter((key) => !allowedProgramKeys.has(key));
  if (unexpectedProgramKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedProgramKeys[0]],
      'DPInd program rejects undeclared completeness, optimum, minimizer, or oracle assertions',
      { unexpectedFields: unexpectedProgramKeys.sort() },
    );
  }

  if (program.kind !== 'SemanticDPProgram0') {
    return validationReject0(
      [...path, 'kind'],
      'DPInd program kind must be SemanticDPProgram0',
      { actual: program.kind },
    );
  }

  if (program.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `DPInd program version must be ${CHECKER_VERSION}`,
      { actual: program.version },
    );
  }

  if (!isIdentifier0(program.programId)) {
    return validationReject0(
      [...path, 'programId'],
      'DPInd programId must be a canonical identifier',
      { actual: program.programId },
    );
  }

  if (!isText0(program.valueSort)) {
    return validationReject0(
      [...path, 'valueSort'],
      'DPInd valueSort must be nonempty',
      { actual: program.valueSort },
    );
  }

  if (!Array.isArray(program.states) || program.states.length === 0) {
    return validationReject0(
      [...path, 'states'],
      'DPInd program must contain a nonempty explicit state array',
      {
        actual: Array.isArray(program.states)
          ? program.states.length
          : typeof program.states,
      },
    );
  }

  if (program.states.length > MAX_DP_STATES) {
    return validationReject0(
      [...path, 'states'],
      'DPInd program exceeds maxDPStates',
      { maxDPStates: MAX_DP_STATES, actual: program.states.length },
    );
  }

  if (!isIdentifier0(program.terminalStateId)) {
    return validationReject0(
      [...path, 'terminalStateId'],
      'DPInd terminalStateId must be a canonical identifier',
      { actual: program.terminalStateId },
    );
  }

  if (!isIdentifier0(program.terminalCoordinate)) {
    return validationReject0(
      [...path, 'terminalCoordinate'],
      'DPInd terminalCoordinate must be a canonical identifier',
      { actual: program.terminalCoordinate },
    );
  }

  const byId = new Map();
  const baseStateIds = [];
  const stepStateIds = [];
  let stepSeen = false;

  for (let index = 0; index < program.states.length; index += 1) {
    const state = program.states[index];
    const statePath = [...path, 'states', index];

    if (!isPlainObject0(state)) {
      return validationReject0(
        statePath,
        'DPInd state must be an object',
        { actual: typeof state },
      );
    }

    const allowedStateKeys = new Set([
      'kind',
      'version',
      'stateKind',
      'index',
      'id',
      'predecessorIds',
      'operator',
      'baseTerm',
      'recurrenceTerm',
      'value',
      'equation',
    ]);
    const unexpectedStateKeys = Object.keys(state)
      .filter((key) => !allowedStateKeys.has(key));
    if (unexpectedStateKeys.length !== 0) {
      return validationReject0(
        [...statePath, unexpectedStateKeys[0]],
        'DPInd state rejects undeclared optimum, minimizer, completion, or search fields',
        { unexpectedFields: unexpectedStateKeys.sort() },
      );
    }

    if (state.kind !== 'SemanticDPState0') {
      return validationReject0(
        [...statePath, 'kind'],
        'DPInd state kind must be SemanticDPState0',
        { actual: state.kind },
      );
    }

    if (state.version !== CHECKER_VERSION) {
      return validationReject0(
        [...statePath, 'version'],
        `DPInd state version must be ${CHECKER_VERSION}`,
        { actual: state.version },
      );
    }

    if (!SEMANTIC_DP_STATE_KINDS0.includes(state.stateKind)) {
      return validationReject0(
        [...statePath, 'stateKind'],
        'DPInd stateKind must be base or step',
        { actual: state.stateKind },
      );
    }

    if (!Number.isSafeInteger(state.index) || state.index !== index) {
      return validationReject0(
        [...statePath, 'index'],
        'DPInd state indices must be exact consecutive evaluation coordinates',
        { expected: index, actual: state.index },
      );
    }

    if (!isIdentifier0(state.id)) {
      return validationReject0(
        [...statePath, 'id'],
        'DPInd state id must be a canonical identifier',
        { actual: state.id },
      );
    }

    if (byId.has(state.id)) {
      return validationReject0(
        [...statePath, 'id'],
        'DPInd state ids must be unique',
        { id: state.id },
      );
    }

    if (!Array.isArray(state.predecessorIds)) {
      return validationReject0(
        [...statePath, 'predecessorIds'],
        'DPInd predecessorIds must be an array',
        { actual: typeof state.predecessorIds },
      );
    }

    const valueCheck = validateClosedTerm0(
      state.value,
      [...statePath, 'value'],
      0,
    );
    if (!valueCheck.ok) return valueCheck;
    if (valueCheck.sort !== program.valueSort) {
      return validationReject0(
        [...statePath, 'value', 'sort'],
        'DPInd state value sort must equal program valueSort',
        { expected: program.valueSort, actual: valueCheck.sort },
      );
    }

    const equationCheck = validateEqJudgment0(
      state.equation,
      [...statePath, 'equation'],
    );
    if (!equationCheck.ok) return equationCheck;

    if (state.stateKind === 'base') {
      if (stepSeen) {
        return validationReject0(
          [...path, 'states'],
          'DPInd base states must form one canonical prefix before recurrence states',
          { stateId: state.id, index },
        );
      }
      if (state.predecessorIds.length !== 0) {
        return validationReject0(
          [...statePath, 'predecessorIds'],
          'DPInd base states must not declare predecessors',
          { actual: state.predecessorIds },
        );
      }
      if (state.operator !== null) {
        return validationReject0(
          [...statePath, 'operator'],
          'DPInd base state operator must be null',
          { actual: state.operator },
        );
      }
      if (state.recurrenceTerm !== null) {
        return validationReject0(
          [...statePath, 'recurrenceTerm'],
          'DPInd base state recurrenceTerm must be null',
          { actual: state.recurrenceTerm },
        );
      }

      const baseCheck = validateClosedTerm0(
        state.baseTerm,
        [...statePath, 'baseTerm'],
        0,
      );
      if (!baseCheck.ok) return baseCheck;
      if (baseCheck.sort !== program.valueSort) {
        return validationReject0(
          [...statePath, 'baseTerm', 'sort'],
          'DPInd baseTerm sort must equal program valueSort',
          { expected: program.valueSort, actual: baseCheck.sort },
        );
      }

      const expectedEquation = makeSemanticEqJudgment0(
        state.value,
        state.baseTerm,
      );
      if (!sameCanonical0(state.equation, expectedEquation)) {
        return validationReject0(
          [...statePath, 'equation'],
          'DPInd base equation must exactly bind the state value to the explicit base term',
          { expected: expectedEquation, actual: state.equation },
        );
      }

      baseStateIds.push(state.id);
    } else {
      stepSeen = true;
      if (state.predecessorIds.length === 0) {
        return validationReject0(
          [...statePath, 'predecessorIds'],
          'DPInd recurrence states must declare at least one predecessor',
          { actual: state.predecessorIds },
        );
      }
      if (!isSafeOperator0(state.operator)) {
        return validationReject0(
          [...statePath, 'operator'],
          'DPInd recurrence operator must be canonical and must not encode minimization, maximization, search, or an oracle',
          { actual: state.operator },
        );
      }
      if (state.baseTerm !== null) {
        return validationReject0(
          [...statePath, 'baseTerm'],
          'DPInd recurrence state baseTerm must be null',
          { actual: state.baseTerm },
        );
      }

      const predecessorIds = new Set();
      const predecessorStates = [];
      for (let predecessorIndex = 0;
        predecessorIndex < state.predecessorIds.length;
        predecessorIndex += 1) {
        const predecessorId = state.predecessorIds[predecessorIndex];
        if (!isIdentifier0(predecessorId)) {
          return validationReject0(
            [...statePath, 'predecessorIds', predecessorIndex],
            'DPInd predecessor id must be a canonical identifier',
            { actual: predecessorId },
          );
        }
        if (predecessorIds.has(predecessorId)) {
          return validationReject0(
            [...statePath, 'predecessorIds', predecessorIndex],
            'DPInd recurrence predecessor ids must be unique',
            { predecessorId },
          );
        }
        const predecessor = byId.get(predecessorId);
        if (predecessor === undefined) {
          return validationReject0(
            [...statePath, 'predecessorIds', predecessorIndex],
            'DPInd recurrence predecessor must reference an earlier state',
            { stateId: state.id, predecessorId },
          );
        }
        predecessorIds.add(predecessorId);
        predecessorStates.push(predecessor);
      }

      const expectedPredecessorIds = [...predecessorStates]
        .sort((left, right) => left.index - right.index)
        .map((predecessor) => predecessor.id);
      if (!sameCanonical0(state.predecessorIds, expectedPredecessorIds)) {
        return validationReject0(
          [...statePath, 'predecessorIds'],
          'DPInd recurrence predecessors must be in canonical evaluation order',
          { expected: expectedPredecessorIds, actual: state.predecessorIds },
        );
      }

      const recurrenceCheck = validateClosedTerm0(
        state.recurrenceTerm,
        [...statePath, 'recurrenceTerm'],
        0,
      );
      if (!recurrenceCheck.ok) return recurrenceCheck;
      if (recurrenceCheck.sort !== program.valueSort) {
        return validationReject0(
          [...statePath, 'recurrenceTerm', 'sort'],
          'DPInd recurrenceTerm sort must equal program valueSort',
          { expected: program.valueSort, actual: recurrenceCheck.sort },
        );
      }

      const expectedRecurrence = makeSemanticApp0(
        state.operator,
        predecessorStates.map((predecessor) => predecessor.value),
        program.valueSort,
      );
      if (!sameCanonical0(state.recurrenceTerm, expectedRecurrence)) {
        return validationReject0(
          [...statePath, 'recurrenceTerm'],
          'DPInd recurrence term must exactly apply the declared operator to all predecessor values',
          { expected: expectedRecurrence, actual: state.recurrenceTerm },
        );
      }

      const expectedEquation = makeSemanticEqJudgment0(
        state.value,
        expectedRecurrence,
      );
      if (!sameCanonical0(state.equation, expectedEquation)) {
        return validationReject0(
          [...statePath, 'equation'],
          'DPInd recurrence equation must exactly bind the state value to the computed recurrence term',
          { expected: expectedEquation, actual: state.equation },
        );
      }

      stepStateIds.push(state.id);
    }

    byId.set(state.id, state);
  }

  if (baseStateIds.length === 0) {
    return validationReject0(
      [...path, 'states'],
      'DPInd program must contain at least one explicit base state',
      null,
    );
  }

  const canonicalBaseStateIds = [...baseStateIds].sort(compareText0);
  if (!sameCanonical0(baseStateIds, canonicalBaseStateIds)) {
    return validationReject0(
      [...path, 'states'],
      'DPInd base-state prefix must be in canonical identifier order',
      { expected: canonicalBaseStateIds, actual: baseStateIds },
    );
  }

  const terminalState = byId.get(program.terminalStateId);
  if (terminalState === undefined) {
    return validationReject0(
      [...path, 'terminalStateId'],
      'DPInd terminalStateId must name a declared state',
      { actual: program.terminalStateId },
    );
  }

  if (program.states.at(-1).id !== program.terminalStateId) {
    return validationReject0(
      [...path, 'terminalStateId'],
      'DPInd terminal state must be the final evaluation coordinate',
      {
        expected: program.states.at(-1).id,
        actual: program.terminalStateId,
      },
    );
  }

  const contributing = new Set();
  const stack = [program.terminalStateId];
  while (stack.length !== 0) {
    const stateId = stack.pop();
    if (contributing.has(stateId)) continue;
    contributing.add(stateId);
    const state = byId.get(stateId);
    for (const predecessorId of state.predecessorIds) {
      stack.push(predecessorId);
    }
  }

  if (contributing.size !== program.states.length) {
    const deadStateIds = program.states
      .map((state) => state.id)
      .filter((stateId) => !contributing.has(stateId));
    return validationReject0(
      [...path, 'states'],
      'DPInd every declared state must contribute to the terminal state',
      { deadStateIds },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticDPProgram0NF',
    programId: program.programId,
    valueSort: program.valueSort,
    stateCount: program.states.length,
    stateOrder: program.states.map((state) => state.id),
    baseStateIds,
    stepStateIds,
    terminalStateId: program.terminalStateId,
    terminalCoordinate: program.terminalCoordinate,
    terminalValueDigest: digestCanonical0(terminalState.value),
    canonicalBasePrefix: true,
    evaluationOrderWellFounded: true,
    predecessorCoverageComplete: true,
    allStatesContributeToTerminal: true,
    hiddenOptimizationAbsent: true,
  }, {
    program,
    byId,
    terminalState,
    baseStateIds,
    stepStateIds,
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'DPInd conclusion must be an object', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'programId',
    'valueSort',
    'stateOrder',
    'baseStateIds',
    'stepStateIds',
    'stateCount',
    'baseStateCount',
    'stepStateCount',
    'terminalStateId',
    'terminalCoordinate',
    'terminalValue',
    'terminalJudgment',
    'caseProofIds',
    'cases',
    'canonicalBasePrefix',
    'evaluationOrderWellFounded',
    'predecessorCoverageComplete',
    'recurrenceEvidenceExact',
    'allStatesEvaluated',
    'allStatesContributeToTerminal',
    'hiddenOptimizationAbsent',
    'terminalStateComputed',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'DPInd conclusion rejects undeclared readiness, optimum, minimizer, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticDPIndJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'DPInd conclusion kind must be SemanticDPIndJudgment0',
      { actual: judgment.kind },
    );
  }

  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `DPInd conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }

  if (!isIdentifier0(judgment.programId)) {
    return validationReject0(
      [...path, 'programId'],
      'DPInd conclusion programId must be a canonical identifier',
      { actual: judgment.programId },
    );
  }

  if (!isText0(judgment.valueSort)) {
    return validationReject0(
      [...path, 'valueSort'],
      'DPInd conclusion valueSort must be nonempty',
      { actual: judgment.valueSort },
    );
  }

  for (const field of [
    'stateOrder',
    'baseStateIds',
    'stepStateIds',
    'caseProofIds',
    'cases',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `DPInd conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }

  for (const field of ['stateCount', 'baseStateCount', 'stepStateCount']) {
    if (!Number.isSafeInteger(judgment[field]) || judgment[field] < 0) {
      return validationReject0(
        [...path, field],
        `DPInd conclusion ${field} must be a nonnegative safe integer`,
        { actual: judgment[field] },
      );
    }
  }

  for (const field of [
    'canonicalBasePrefix',
    'evaluationOrderWellFounded',
    'predecessorCoverageComplete',
    'recurrenceEvidenceExact',
    'allStatesEvaluated',
    'allStatesContributeToTerminal',
    'hiddenOptimizationAbsent',
    'terminalStateComputed',
  ]) {
    if (judgment[field] !== true) {
      return validationReject0(
        [...path, field],
        `DPInd conclusion ${field} must be true`,
        { actual: judgment[field] },
      );
    }
  }

  if (!isPlainObject0(judgment.terminalJudgment)
      || judgment.terminalJudgment.kind !== 'SemanticDPResultJudgment0') {
    return validationReject0(
      [...path, 'terminalJudgment'],
      'DPInd conclusion terminalJudgment must be SemanticDPResultJudgment0',
      { actual: judgment.terminalJudgment },
    );
  }

  return validationAccept0({
    kind: 'SemanticDPIndJudgmentShape0NF',
    programId: judgment.programId,
    stateCount: judgment.stateCount,
    caseCount: judgment.cases.length,
  });
}

function checkDPIndRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'DPInd rule supports only close',
      { actual: node.Payload.op },
    );
  }

  const programCheck = validateProgram0(
    node.Payload.program,
    [...path, 'Payload', 'program'],
  );
  if (!programCheck.ok) return programCheck;

  const derived = deriveClosure0(
    programCheck,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;

  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'DPInd conclusion must exactly equal the computed terminal dynamic-programming closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticDPIndRule0NF',
    ruleName: 'DPInd',
    operation: 'close',
    programId: programCheck.program.programId,
    stateCount: programCheck.program.states.length,
    baseStateCount: programCheck.baseStateIds.length,
    stepStateCount: programCheck.stepStateIds.length,
    terminalStateId: programCheck.program.terminalStateId,
    terminalCoordinate: programCheck.program.terminalCoordinate,
    caseProofIds: [...node.Premises],
    canonicalBasePrefix: true,
    evaluationOrderWellFounded: true,
    predecessorCoverageComplete: true,
    allStatesContributeToTerminal: true,
    hiddenOptimizationAbsent: true,
    terminalStateComputed: true,
  });
}

function deriveClosure0(programCheck, premises, caseProofIds, path) {
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'DPInd closure requires premise and proof-id arrays',
      null,
    );
  }

  const states = programCheck.program.states;
  if (premises.length !== states.length || caseProofIds.length !== states.length) {
    return validationReject0(
      [...path, 'Premises'],
      'DPInd requires exactly one local case record for every declared state',
      {
        expected: states.length,
        actualPremises: premises.length,
        actualProofIds: caseProofIds.length,
      },
    );
  }

  const valueBindings = new Map();
  const cases = [];

  for (let index = 0; index < states.length; index += 1) {
    const state = states[index];
    const premise = premises[index];
    const casePath = [...path, 'Premises', index];

    if (!isPlainObject0(premise)) {
      return validationReject0(
        casePath,
        'DPInd case premise must resolve to an earlier accepted proof node',
        { actual: premise },
      );
    }

    if (premise.RuleName !== 'Record' || premise.operation !== 'intro') {
      return validationReject0(
        casePath,
        'DPInd case premise must be accepted Record.intro evidence',
        {
          actualRuleName: premise.RuleName,
          actualOperation: premise.operation,
        },
      );
    }

    const caseCheck = validateCaseRecord0(
      premise.Conclusion,
      programCheck.program.programId,
      state,
      valueBindings,
      casePath,
    );
    if (!caseCheck.ok) return caseCheck;

    valueBindings.set(state.id, caseCheck.valueBinding);
    cases.push(Object.freeze({
      kind: 'SemanticDPIndCaseResult0',
      index: state.index,
      stateId: state.id,
      stateKind: state.stateKind,
      predecessorIds: Object.freeze([...state.predecessorIds]),
      operator: state.operator,
      value: state.value,
      equation: state.equation,
    }));
  }

  const judgment = makeSemanticDPIndJudgment0({
    programId: programCheck.program.programId,
    valueSort: programCheck.program.valueSort,
    stateOrder: programCheck.nf.stateOrder,
    baseStateIds: programCheck.baseStateIds,
    stepStateIds: programCheck.stepStateIds,
    terminalStateId: programCheck.program.terminalStateId,
    terminalCoordinate: programCheck.program.terminalCoordinate,
    terminalValue: programCheck.terminalState.value,
    caseProofIds,
    cases,
  });

  return validationAcceptWith0({
    kind: 'SemanticDPIndClosure0NF',
    programId: programCheck.program.programId,
    stateCount: states.length,
    terminalStateId: programCheck.program.terminalStateId,
    terminalCoordinate: programCheck.program.terminalCoordinate,
  }, {
    judgment,
  });
}

function validateCaseRecord0(record, programId, state, valueBindings, path) {
  if (!isPlainObject0(record)) {
    return validationReject0(
      path,
      'DPInd case conclusion must be a record judgment',
      { actual: typeof record },
    );
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'Conclusion', 'kind'],
      'DPInd case conclusion must be SemanticRecordJudgment0',
      { actual: record.kind },
    );
  }

  if (record.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'Conclusion', 'version'],
      `DPInd case conclusion version must be ${CHECKER_VERSION}`,
      { actual: record.version },
    );
  }

  const expectedRecordType = caseRecordType0(programId, state.id);
  if (record.recordType !== expectedRecordType) {
    return validationReject0(
      [...path, 'Conclusion', 'recordType'],
      'DPInd case recordType must bind the program and state id',
      { expected: expectedRecordType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DPInd case record fields must be an array',
      { actual: typeof record.fields },
    );
  }

  const expectedNames = [
    'equation',
    'value',
    ...state.predecessorIds.map((predecessorId) => `dep.${predecessorId}`),
  ].sort(compareText0);
  const actualNames = record.fields.map((field) => field?.name ?? null);
  if (!sameCanonical0(actualNames, expectedNames)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DPInd case fields must contain the exact equation, value, and predecessor values',
      { expected: expectedNames, actual: actualNames },
    );
  }

  const fieldMap = new Map();
  for (let index = 0; index < record.fields.length; index += 1) {
    const field = record.fields[index];
    if (!isPlainObject0(field)
        || field.kind !== 'SemanticRecordField0'
        || typeof field.name !== 'string'
        || !isPlainObject0(field.judgment)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields', index],
        'DPInd case fields must contain semantic judgment objects',
        { actual: field },
      );
    }
    fieldMap.set(field.name, field.judgment);
  }

  if (!sameCanonical0(fieldMap.get('equation'), state.equation)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DPInd case equation must exactly match the declared base or recurrence equation',
      {
        stateId: state.id,
        expected: state.equation,
        actual: fieldMap.get('equation'),
      },
    );
  }

  const valueBinding = makeSemanticEqJudgment0(state.value, state.value);
  if (!sameCanonical0(fieldMap.get('value'), valueBinding)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'DPInd case value must exactly bind the declared state value',
      {
        stateId: state.id,
        expected: valueBinding,
        actual: fieldMap.get('value'),
      },
    );
  }

  for (const predecessorId of state.predecessorIds) {
    const expected = valueBindings.get(predecessorId);
    if (expected === undefined) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'DPInd case depends on a predecessor without an earlier evaluated value',
        { stateId: state.id, predecessorId },
      );
    }

    const actual = fieldMap.get(`dep.${predecessorId}`);
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'DPInd predecessor value must exactly match the earlier evaluated state value',
        {
          stateId: state.id,
          predecessorId,
          expected,
          actual,
        },
      );
    }
  }

  return validationAcceptWith0({
    kind: 'SemanticDPIndCase0NF',
    programId,
    stateId: state.id,
    stateKind: state.stateKind,
    predecessorCount: state.predecessorIds.length,
    operator: state.operator,
  }, {
    valueBinding,
  });
}

function validateEqJudgment0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'DPInd equation must be an equality judgment', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set(['kind', 'left', 'right']);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'DPInd equation rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticEqJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'DPInd equation kind must be SemanticEqJudgment0',
      { actual: judgment.kind },
    );
  }

  const left = validateClosedTerm0(judgment.left, [...path, 'left'], 0);
  if (!left.ok) return left;
  const right = validateClosedTerm0(judgment.right, [...path, 'right'], 0);
  if (!right.ok) return right;
  if (left.sort !== right.sort) {
    return validationReject0(
      path,
      'DPInd equation terms must have the same sort',
      { leftSort: left.sort, rightSort: right.sort },
    );
  }

  return validationAccept0({
    kind: 'SemanticDPEquation0NF',
    sort: left.sort,
  });
}

function validateClosedTerm0(term, path, depth) {
  if (depth > MAX_TERM_DEPTH) {
    return validationReject0(
      path,
      'DPInd term exceeds maxTermDepth',
      { maxTermDepth: MAX_TERM_DEPTH },
    );
  }

  if (!isPlainObject0(term)) {
    return validationReject0(path, 'DPInd term must be an object', {
      actual: typeof term,
    });
  }

  if (term.kind === 'SemanticVar0') {
    return validationReject0(
      path,
      'DPInd state values and recurrence terms must be closed',
      { variable: term.name ?? null },
    );
  }

  if (term.kind === 'SemanticConst0') {
    const allowed = new Set(['kind', 'name', 'sort']);
    const unexpected = Object.keys(term).filter((key) => !allowed.has(key));
    if (unexpected.length !== 0) {
      return validationReject0(
        [...path, unexpected[0]],
        'DPInd constant term rejects undeclared fields',
        { unexpectedFields: unexpected.sort() },
      );
    }
    if (!isText0(term.name) || !isText0(term.sort)) {
      return validationReject0(
        path,
        'DPInd constant term requires nonempty name and sort',
        { actual: term },
      );
    }
    return validationAcceptWith0({
      kind: 'SemanticDPClosedTerm0NF',
      termKind: term.kind,
      sort: term.sort,
    }, {
      sort: term.sort,
    });
  }

  if (term.kind === 'SemanticApp0') {
    const allowed = new Set(['kind', 'symbol', 'args', 'sort']);
    const unexpected = Object.keys(term).filter((key) => !allowed.has(key));
    if (unexpected.length !== 0) {
      return validationReject0(
        [...path, unexpected[0]],
        'DPInd application term rejects undeclared fields',
        { unexpectedFields: unexpected.sort() },
      );
    }
    if (!isText0(term.symbol) || !isText0(term.sort)) {
      return validationReject0(
        path,
        'DPInd application term requires nonempty symbol and sort',
        { actual: term },
      );
    }
    if (!Array.isArray(term.args)) {
      return validationReject0(
        [...path, 'args'],
        'DPInd application args must be an array',
        { actual: typeof term.args },
      );
    }
    for (let index = 0; index < term.args.length; index += 1) {
      const child = validateClosedTerm0(
        term.args[index],
        [...path, 'args', index],
        depth + 1,
      );
      if (!child.ok) return child;
    }
    return validationAcceptWith0({
      kind: 'SemanticDPClosedTerm0NF',
      termKind: term.kind,
      sort: term.sort,
      arity: term.args.length,
    }, {
      sort: term.sort,
    });
  }

  return validationReject0(
    [...path, 'kind'],
    'DPInd term kind is unsupported',
    { actual: term.kind },
  );
}

function caseRecordType0(programId, stateId) {
  return `DPIndCase0.${programId}.${stateId}`;
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProofFiniteExhaust0(
      makeSemanticProofDAG0(baseNodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofFiniteExhaust0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofFiniteExhaust0 threw instead of returning a reject record',
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

function compareCanonical0(left, right) {
  return compareText0(stableStringify0(left), stableStringify0(right));
}

function compareText0(left, right) {
  return left < right ? -1 : left > right ? 1 : 0;
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isSafeOperator0(value) {
  if (!isIdentifier0(value)) return false;
  const lower = value.toLowerCase();
  const forbidden = [
    'argmin',
    'argmax',
    'minimum',
    'maximum',
    'minimize',
    'maximize',
    'optimum',
    'optimal',
    'oracle',
    'search',
    'solver',
    'exactmin',
    'canonicalminimizer',
  ];
  if (forbidden.some((token) => lower.includes(token))) return false;
  if (lower.includes('min') || lower.includes('max')) return false;
  return true;
}

function requireSafeOperator0(value, label) {
  if (!isSafeOperator0(value)) {
    throw new TypeError(
      `${label} must be canonical and must not encode minimization, maximization, search, or an oracle`,
    );
  }
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

function isText0(value) {
  return typeof value === 'string' && value.length > 0;
}

function isIdentifier0(value) {
  return typeof value === 'string' && ID_PATTERN.test(value);
}

function requireText0(value, label) {
  if (!isText0(value)) {
    throw new TypeError(`${label} must be a nonempty string`);
  }
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
