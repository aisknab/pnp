import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofLedgerInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0,
} from './pcc-kernel-ledgerind-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_OBLIGATIONS = 100_000;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_OBLIGATION_MODES0 = Object.freeze(['Full', 'Quot']);
export const SEMANTIC_OBLIGATION_CREATION_RULES0 = Object.freeze(['R5']);
export const SEMANTIC_OBLIGATION_DISCHARGE_RULES0 = Object.freeze([
  'R6',
  'R7',
  'R8',
]);
export const SEMANTIC_OBLTOPOIND_OPERATIONS0 = Object.freeze(['close']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0,
  'OblTopoInd',
]);

export function makeSemanticObligationCreationEvidence0({
  planId,
  obligationId,
  mode = 'Full',
  source,
  target,
  frontier,
  projection,
} = {}) {
  requireIdentifier0(planId, 'makeSemanticObligationCreationEvidence0 planId');
  requireIdentifier0(
    obligationId,
    'makeSemanticObligationCreationEvidence0 obligationId',
  );
  requireMode0(mode, 'makeSemanticObligationCreationEvidence0 mode');
  for (const [name, value] of Object.entries({
    source,
    target,
    frontier,
    projection,
  })) {
    if (!isPlainObject0(value)) {
      throw new TypeError(
        `makeSemanticObligationCreationEvidence0 ${name} must be a semantic judgment object`,
      );
    }
  }

  const fields = [
    makeSemanticRecordField0('frontier', frontier),
    makeSemanticRecordField0('projection', projection),
    makeSemanticRecordField0('source', source),
    makeSemanticRecordField0('target', target),
  ];

  return makeSemanticRecordJudgment0(
    creationRecordType0(planId, obligationId, mode),
    fields,
  );
}

export function makeSemanticObligationDischargeEvidence0({
  planId,
  obligationId,
  mode = 'Full',
  rule,
  result,
  fullWitness = null,
} = {}) {
  requireIdentifier0(planId, 'makeSemanticObligationDischargeEvidence0 planId');
  requireIdentifier0(
    obligationId,
    'makeSemanticObligationDischargeEvidence0 obligationId',
  );
  requireMode0(mode, 'makeSemanticObligationDischargeEvidence0 mode');
  requireDischargeRule0(
    rule,
    'makeSemanticObligationDischargeEvidence0 rule',
  );
  if (!isPlainObject0(result)) {
    throw new TypeError(
      'makeSemanticObligationDischargeEvidence0 result must be a semantic judgment object',
    );
  }
  if (rule === 'R6' && mode !== 'Full') {
    throw new TypeError('R6 discharge is permitted only in Full mode');
  }
  if (mode === 'Full' && !isPlainObject0(fullWitness)) {
    throw new TypeError(
      'Full-mode obligation discharge requires a semantic fullWitness judgment',
    );
  }
  if (mode === 'Quot' && fullWitness !== null) {
    throw new TypeError(
      'Quot-mode obligation discharge must not claim a Full-mode witness',
    );
  }

  const fields = [makeSemanticRecordField0('result', result)];
  if (mode === 'Full') {
    fields.push(makeSemanticRecordField0('fullWitness', fullWitness));
    fields.sort((left, right) => compareText0(left.name, right.name));
  }

  return makeSemanticRecordJudgment0(
    dischargeRecordType0(planId, obligationId, rule, mode),
    fields,
  );
}

export function makeSemanticObligation0({
  id,
  mode = 'Full',
  dependencies = [],
  createIndex,
  dischargeIndex,
  creationRule = 'R5',
  dischargeRule,
  creationEvidence,
  dischargeEvidence,
} = {}) {
  requireIdentifier0(id, 'makeSemanticObligation0 id');
  requireMode0(mode, 'makeSemanticObligation0 mode');
  if (!Array.isArray(dependencies)) {
    throw new TypeError('makeSemanticObligation0 dependencies must be an array');
  }
  for (const dependencyId of dependencies) {
    requireIdentifier0(
      dependencyId,
      'makeSemanticObligation0 dependency id',
    );
  }
  if (!Number.isSafeInteger(createIndex) || createIndex < 0) {
    throw new TypeError(
      'makeSemanticObligation0 createIndex must be a nonnegative safe integer',
    );
  }
  if (!Number.isSafeInteger(dischargeIndex) || dischargeIndex < 0) {
    throw new TypeError(
      'makeSemanticObligation0 dischargeIndex must be a nonnegative safe integer',
    );
  }
  if (!SEMANTIC_OBLIGATION_CREATION_RULES0.includes(creationRule)) {
    throw new TypeError('makeSemanticObligation0 creationRule must be R5');
  }
  requireDischargeRule0(dischargeRule, 'makeSemanticObligation0 dischargeRule');
  if (!isPlainObject0(creationEvidence)) {
    throw new TypeError(
      'makeSemanticObligation0 creationEvidence must be a semantic record judgment',
    );
  }
  if (!isPlainObject0(dischargeEvidence)) {
    throw new TypeError(
      'makeSemanticObligation0 dischargeEvidence must be a semantic record judgment',
    );
  }

  return Object.freeze({
    kind: 'SemanticObligation0',
    id,
    mode,
    dependencies: Object.freeze([...dependencies].sort(compareText0)),
    createIndex,
    dischargeIndex,
    creationRule,
    dischargeRule,
    creationEvidence,
    dischargeEvidence,
  });
}

export function makeSemanticObligationPlan0(planId, obligations = []) {
  requireIdentifier0(planId, 'makeSemanticObligationPlan0 planId');
  if (!Array.isArray(obligations)) {
    throw new TypeError('makeSemanticObligationPlan0 obligations must be an array');
  }

  return Object.freeze({
    kind: 'SemanticObligationPlan0',
    version: CHECKER_VERSION,
    planId,
    obligations: Object.freeze([...obligations]),
  });
}

/**
 * A local obligation case is accepted Record.intro evidence. It binds exact
 * creation and discharge evidence to a closed invariant and to every already
 * closed dependency invariant.
 */
export function makeSemanticOblTopoIndCase0({
  planId,
  obligationId,
  creation,
  discharge,
  closed,
  dependencyInvariants = [],
} = {}) {
  requireIdentifier0(planId, 'makeSemanticOblTopoIndCase0 planId');
  requireIdentifier0(
    obligationId,
    'makeSemanticOblTopoIndCase0 obligationId',
  );
  if (!Array.isArray(dependencyInvariants)) {
    throw new TypeError(
      'makeSemanticOblTopoIndCase0 dependencyInvariants must be an array',
    );
  }

  const fields = [
    makeSemanticRecordField0('closed', closed),
    makeSemanticRecordField0('creation', creation),
    makeSemanticRecordField0('discharge', discharge),
  ];
  for (const entry of dependencyInvariants) {
    if (!isPlainObject0(entry)) {
      throw new TypeError(
        'makeSemanticOblTopoIndCase0 dependency entry must be an object',
      );
    }
    requireIdentifier0(
      entry.obligationId,
      'makeSemanticOblTopoIndCase0 dependency obligationId',
    );
    fields.push(makeSemanticRecordField0(
      `dep.${entry.obligationId}`,
      entry.invariant,
    ));
  }
  fields.sort((left, right) => compareText0(left.name, right.name));

  return makeSemanticRecordJudgment0(
    caseRecordType0(planId, obligationId),
    fields,
  );
}

export function makeSemanticOblTopoIndJudgment0({
  planId,
  obligationOrder,
  dischargeOrder,
  eventOrder,
  sourceObligationIds,
  terminalObligationIds,
  fullModeObligationIds,
  quotientModeObligationIds,
  caseProofIds,
  cases,
  dischargedObligationIds,
} = {}) {
  requireIdentifier0(planId, 'makeSemanticOblTopoIndJudgment0 planId');
  for (const [name, value] of Object.entries({
    obligationOrder,
    dischargeOrder,
    eventOrder,
    sourceObligationIds,
    terminalObligationIds,
    fullModeObligationIds,
    quotientModeObligationIds,
    caseProofIds,
    cases,
    dischargedObligationIds,
  })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticOblTopoIndJudgment0 ${name} must be an array`);
    }
  }

  return Object.freeze({
    kind: 'SemanticOblTopoIndJudgment0',
    version: CHECKER_VERSION,
    planId,
    obligationOrder: Object.freeze([...obligationOrder]),
    dischargeOrder: Object.freeze([...dischargeOrder]),
    eventOrder: Object.freeze([...eventOrder]),
    sourceObligationIds: Object.freeze([...sourceObligationIds]),
    terminalObligationIds: Object.freeze([...terminalObligationIds]),
    fullModeObligationIds: Object.freeze([...fullModeObligationIds]),
    quotientModeObligationIds: Object.freeze([...quotientModeObligationIds]),
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    dischargedObligationIds: Object.freeze([...dischargedObligationIds]),
    openObligationIds: Object.freeze([]),
    allDependenciesClosed: true,
    fullModeDischargesVerified: true,
    allObligationsDischarged: true,
    noOpenObligations: true,
  });
}

/**
 * Generator helper. The checker independently recomputes this conclusion and
 * never trusts caller-supplied closure flags.
 */
export function deriveSemanticOblTopoIndJudgment0({
  plan,
  caseRecords,
  caseProofIds,
} = {}) {
  const planCheck = validatePlan0(plan, ['plan']);
  if (!planCheck.ok) throw new TypeError(planCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError('deriveSemanticOblTopoIndJudgment0 requires case arrays');
  }

  const derived = deriveClosure0(
    planCheck,
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

export function CheckSemanticKernelReadinessOblTopoInd0() {
  const checker = 'CheckSemanticKernelReadinessOblTopoInd0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessOblTopoInd0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofLedgerInd0',
    proofChecker: 'CheckSemanticKernelProofOblTopoInd0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    oblTopoIndOperations: [...SEMANTIC_OBLTOPOIND_OPERATIONS0],
    creationRules: [...SEMANTIC_OBLIGATION_CREATION_RULES0],
    dischargeRules: [...SEMANTIC_OBLIGATION_DISCHARGE_RULES0],
    exactLifecycleEventsRequired: true,
    fullModeWitnessRequired: true,
    terminalNoOpenObligationsRequired: true,
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
        reason: 'OblTopoInd-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks predecessor rule families with the merged predecessor checker and
 * checks OblTopoInd as exact creation/discharge closure of accepted local cases.
 */
export function CheckSemanticKernelProofOblTopoInd0(input) {
  const checker = 'CheckSemanticKernelProofOblTopoInd0';
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
        reason: 'OblTopoInd-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofLedgerInd0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd sub-DAG rejected under the predecessor semantic checker',
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
    if (node.RuleName === 'OblTopoInd') {
      semantic = checkOblTopoIndRule0(node, premises, path);
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0.includes(rule),
  );
  const oblTopoIndNodeCount = summaries.filter(
    (node) => node.RuleName === 'OblTopoInd',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofOblTopoInd0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofLedgerInd0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_OBLTOPOIND0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedOblTopoIndOperations: [...SEMANTIC_OBLTOPOIND_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      oblTopoIndNodeCount,
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
      { kind: 'SemanticOblTopoIndProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticOblTopoIndProofInput0NF', form: 'object', nodeCount: nodes.length },
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
        'OblTopoInd-extended semantic proof node rejects undeclared fields',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'OblTopoInd-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'OblTopoInd-extended semantic kernel accepts Full proof-node mode only',
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

    if (node.RuleName === 'OblTopoInd') {
      const payload = validateOblTopoIndPayload0(node.Payload, [...path, 'Payload']);
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
    kind: 'SemanticOblTopoIndProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateOblTopoIndPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'plan']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'OblTopoInd payload rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (!SEMANTIC_OBLTOPOIND_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'OblTopoInd operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_OBLTOPOIND_OPERATIONS0],
      },
    );
  }

  return validatePlan0(payload.plan, [...path, 'plan']);
}

function validatePlan0(plan, path) {
  if (!isPlainObject0(plan)) {
    return validationReject0(path, 'OblTopoInd plan must be an object', {
      actual: typeof plan,
    });
  }

  const allowedPlanKeys = new Set(['kind', 'version', 'planId', 'obligations']);
  const unexpectedPlanKeys = Object.keys(plan)
    .filter((key) => !allowedPlanKeys.has(key));
  if (unexpectedPlanKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedPlanKeys[0]],
      'OblTopoInd plan rejects undeclared fields',
      { unexpectedFields: unexpectedPlanKeys.sort() },
    );
  }

  if (plan.kind !== 'SemanticObligationPlan0') {
    return validationReject0(
      [...path, 'kind'],
      'OblTopoInd plan kind must be SemanticObligationPlan0',
      { actual: plan.kind },
    );
  }

  if (plan.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `OblTopoInd plan version must be ${CHECKER_VERSION}`,
      { actual: plan.version },
    );
  }

  if (!isIdentifier0(plan.planId)) {
    return validationReject0(
      [...path, 'planId'],
      'OblTopoInd planId must be a canonical identifier',
      { actual: plan.planId },
    );
  }

  if (!Array.isArray(plan.obligations) || plan.obligations.length === 0) {
    return validationReject0(
      [...path, 'obligations'],
      'OblTopoInd plan must contain a nonempty obligations array',
      {
        actual: Array.isArray(plan.obligations)
          ? plan.obligations.length
          : typeof plan.obligations,
      },
    );
  }

  if (plan.obligations.length > MAX_OBLIGATIONS) {
    return validationReject0(
      [...path, 'obligations'],
      'OblTopoInd plan exceeds maxObligations',
      { maxObligations: MAX_OBLIGATIONS, actual: plan.obligations.length },
    );
  }

  const byId = new Map();
  const eventIndexes = [];
  let previousCreateIndex = -1;

  for (let index = 0; index < plan.obligations.length; index += 1) {
    const obligation = plan.obligations[index];
    const obligationPath = [...path, 'obligations', index];

    if (!isPlainObject0(obligation)) {
      return validationReject0(
        obligationPath,
        'OblTopoInd obligation must be an object',
        { actual: typeof obligation },
      );
    }

    const allowedObligationKeys = new Set([
      'kind',
      'id',
      'mode',
      'dependencies',
      'createIndex',
      'dischargeIndex',
      'creationRule',
      'dischargeRule',
      'creationEvidence',
      'dischargeEvidence',
    ]);
    const unexpectedObligationKeys = Object.keys(obligation)
      .filter((key) => !allowedObligationKeys.has(key));
    if (unexpectedObligationKeys.length !== 0) {
      return validationReject0(
        [...obligationPath, unexpectedObligationKeys[0]],
        'OblTopoInd obligation rejects undeclared fields',
        { unexpectedFields: unexpectedObligationKeys.sort() },
      );
    }

    if (obligation.kind !== 'SemanticObligation0') {
      return validationReject0(
        [...obligationPath, 'kind'],
        'OblTopoInd obligation kind must be SemanticObligation0',
        { actual: obligation.kind },
      );
    }

    if (!isIdentifier0(obligation.id)) {
      return validationReject0(
        [...obligationPath, 'id'],
        'OblTopoInd obligation id must be a canonical identifier',
        { actual: obligation.id },
      );
    }

    if (byId.has(obligation.id)) {
      return validationReject0(
        [...obligationPath, 'id'],
        'OblTopoInd obligation ids must be unique',
        { id: obligation.id },
      );
    }

    if (!SEMANTIC_OBLIGATION_MODES0.includes(obligation.mode)) {
      return validationReject0(
        [...obligationPath, 'mode'],
        'OblTopoInd obligation mode is unsupported',
        {
          actual: obligation.mode,
          supportedModes: [...SEMANTIC_OBLIGATION_MODES0],
        },
      );
    }

    if (!Array.isArray(obligation.dependencies)) {
      return validationReject0(
        [...obligationPath, 'dependencies'],
        'OblTopoInd dependencies must be an array',
        { actual: typeof obligation.dependencies },
      );
    }

    const canonicalDependencies = [...obligation.dependencies].sort(compareText0);
    if (!sameCanonical0(obligation.dependencies, canonicalDependencies)) {
      return validationReject0(
        [...obligationPath, 'dependencies'],
        'OblTopoInd dependency ids must be in canonical order',
        { expected: canonicalDependencies, actual: obligation.dependencies },
      );
    }

    if (new Set(obligation.dependencies).size !== obligation.dependencies.length) {
      return validationReject0(
        [...obligationPath, 'dependencies'],
        'OblTopoInd dependency ids must be unique',
        { dependencies: obligation.dependencies },
      );
    }

    for (let dependencyIndex = 0;
      dependencyIndex < obligation.dependencies.length;
      dependencyIndex += 1) {
      if (!isIdentifier0(obligation.dependencies[dependencyIndex])) {
        return validationReject0(
          [...obligationPath, 'dependencies', dependencyIndex],
          'OblTopoInd dependency id must be a canonical identifier',
          { actual: obligation.dependencies[dependencyIndex] },
        );
      }
    }

    if (!Number.isSafeInteger(obligation.createIndex)
        || obligation.createIndex < 0) {
      return validationReject0(
        [...obligationPath, 'createIndex'],
        'OblTopoInd createIndex must be a nonnegative safe integer',
        { actual: obligation.createIndex },
      );
    }

    if (!Number.isSafeInteger(obligation.dischargeIndex)
        || obligation.dischargeIndex < 0) {
      return validationReject0(
        [...obligationPath, 'dischargeIndex'],
        'OblTopoInd dischargeIndex must be a nonnegative safe integer',
        { actual: obligation.dischargeIndex },
      );
    }

    if (obligation.createIndex <= previousCreateIndex) {
      return validationReject0(
        [...path, 'obligations'],
        'OblTopoInd obligations must be in strictly increasing creation order',
        {
          previousCreateIndex,
          actualCreateIndex: obligation.createIndex,
          obligationId: obligation.id,
        },
      );
    }

    if (obligation.createIndex >= obligation.dischargeIndex) {
      return validationReject0(
        obligationPath,
        'OblTopoInd obligation must be created before it is discharged',
        {
          createIndex: obligation.createIndex,
          dischargeIndex: obligation.dischargeIndex,
        },
      );
    }

    if (!SEMANTIC_OBLIGATION_CREATION_RULES0.includes(obligation.creationRule)) {
      return validationReject0(
        [...obligationPath, 'creationRule'],
        'OblTopoInd obligations may be created only by R5',
        { actual: obligation.creationRule },
      );
    }

    if (!SEMANTIC_OBLIGATION_DISCHARGE_RULES0.includes(obligation.dischargeRule)) {
      return validationReject0(
        [...obligationPath, 'dischargeRule'],
        'OblTopoInd discharge rule is unsupported',
        {
          actual: obligation.dischargeRule,
          supportedRules: [...SEMANTIC_OBLIGATION_DISCHARGE_RULES0],
        },
      );
    }

    if (obligation.dischargeRule === 'R6' && obligation.mode !== 'Full') {
      return validationReject0(
        [...obligationPath, 'dischargeRule'],
        'R6 may discharge only a Full-mode obligation',
        { mode: obligation.mode },
      );
    }

    const creationEvidence = validateCreationEvidence0(
      obligation.creationEvidence,
      plan.planId,
      obligation,
      [...obligationPath, 'creationEvidence'],
    );
    if (!creationEvidence.ok) return creationEvidence;

    const dischargeEvidence = validateDischargeEvidence0(
      obligation.dischargeEvidence,
      plan.planId,
      obligation,
      [...obligationPath, 'dischargeEvidence'],
    );
    if (!dischargeEvidence.ok) return dischargeEvidence;

    byId.set(obligation.id, obligation);
    eventIndexes.push(obligation.createIndex, obligation.dischargeIndex);
    previousCreateIndex = obligation.createIndex;
  }

  const sortedEventIndexes = [...eventIndexes].sort((left, right) => left - right);
  const expectedEventIndexes = Array.from(
    { length: plan.obligations.length * 2 },
    (_value, index) => index,
  );
  if (!sameCanonical0(sortedEventIndexes, expectedEventIndexes)) {
    return validationReject0(
      [...path, 'obligations'],
      'OblTopoInd creation and discharge events must form one exact consecutive schedule',
      { expected: expectedEventIndexes, actual: sortedEventIndexes },
    );
  }

  for (let index = 0; index < plan.obligations.length; index += 1) {
    const obligation = plan.obligations[index];
    const obligationPath = [...path, 'obligations', index];
    for (let dependencyIndex = 0;
      dependencyIndex < obligation.dependencies.length;
      dependencyIndex += 1) {
      const dependencyId = obligation.dependencies[dependencyIndex];
      const dependency = byId.get(dependencyId);
      if (dependency === undefined) {
        return validationReject0(
          [...obligationPath, 'dependencies', dependencyIndex],
          'OblTopoInd dependency must name a declared obligation',
          { obligationId: obligation.id, dependencyId },
        );
      }

      if (dependency.createIndex >= obligation.createIndex) {
        return validationReject0(
          [...obligationPath, 'dependencies', dependencyIndex],
          'OblTopoInd dependency must be created before the dependent obligation',
          {
            obligationId: obligation.id,
            dependencyId,
            dependencyCreateIndex: dependency.createIndex,
            obligationCreateIndex: obligation.createIndex,
          },
        );
      }

      if (dependency.dischargeIndex >= obligation.dischargeIndex) {
        return validationReject0(
          [...obligationPath, 'dependencies', dependencyIndex],
          'OblTopoInd dependency must be discharged before the dependent obligation',
          {
            obligationId: obligation.id,
            dependencyId,
            dependencyDischargeIndex: dependency.dischargeIndex,
            obligationDischargeIndex: obligation.dischargeIndex,
          },
        );
      }

      if (dependency.mode !== obligation.mode) {
        return validationReject0(
          [...obligationPath, 'dependencies', dependencyIndex],
          'OblTopoInd dependencies must remain in the same mode unless an explicit Transport rule is used',
          {
            obligationId: obligation.id,
            obligationMode: obligation.mode,
            dependencyId,
            dependencyMode: dependency.mode,
          },
        );
      }
    }
  }

  const dischargeObligations = [...plan.obligations]
    .sort((left, right) => left.dischargeIndex - right.dischargeIndex);
  const outdegree = new Map(plan.obligations.map((obligation) => [obligation.id, 0]));
  for (const obligation of plan.obligations) {
    for (const dependencyId of obligation.dependencies) {
      outdegree.set(dependencyId, outdegree.get(dependencyId) + 1);
    }
  }

  const eventOrder = Array.from(
    { length: plan.obligations.length * 2 },
    () => null,
  );
  for (const obligation of plan.obligations) {
    eventOrder[obligation.createIndex] = Object.freeze({
      kind: 'SemanticObligationLifecycleEvent0',
      index: obligation.createIndex,
      action: 'create',
      obligationId: obligation.id,
      rule: obligation.creationRule,
      mode: obligation.mode,
    });
    eventOrder[obligation.dischargeIndex] = Object.freeze({
      kind: 'SemanticObligationLifecycleEvent0',
      index: obligation.dischargeIndex,
      action: 'discharge',
      obligationId: obligation.id,
      rule: obligation.dischargeRule,
      mode: obligation.mode,
    });
  }

  return validationAcceptWith0({
    kind: 'SemanticObligationPlan0NF',
    planId: plan.planId,
    obligationCount: plan.obligations.length,
    obligationOrder: plan.obligations.map((obligation) => obligation.id),
    dischargeOrder: dischargeObligations.map((obligation) => obligation.id),
    eventOrder,
    sourceObligationIds: plan.obligations
      .filter((obligation) => obligation.dependencies.length === 0)
      .map((obligation) => obligation.id),
    terminalObligationIds: plan.obligations
      .filter((obligation) => outdegree.get(obligation.id) === 0)
      .map((obligation) => obligation.id),
    fullModeObligationIds: plan.obligations
      .filter((obligation) => obligation.mode === 'Full')
      .map((obligation) => obligation.id),
    quotientModeObligationIds: plan.obligations
      .filter((obligation) => obligation.mode === 'Quot')
      .map((obligation) => obligation.id),
  }, {
    plan,
    byId,
    dischargeObligations,
  });
}

function validateCreationEvidence0(record, planId, obligation, path) {
  const expectedType = creationRecordType0(
    planId,
    obligation.id,
    obligation.mode,
  );
  return validateEvidenceRecord0(
    record,
    expectedType,
    ['frontier', 'projection', 'source', 'target'],
    path,
    'OblTopoInd creation evidence',
  );
}

function validateDischargeEvidence0(record, planId, obligation, path) {
  const expectedType = dischargeRecordType0(
    planId,
    obligation.id,
    obligation.dischargeRule,
    obligation.mode,
  );
  const expectedFields = obligation.mode === 'Full'
    ? ['fullWitness', 'result']
    : ['result'];
  return validateEvidenceRecord0(
    record,
    expectedType,
    expectedFields,
    path,
    'OblTopoInd discharge evidence',
  );
}

function validateEvidenceRecord0(
  record,
  expectedType,
  expectedFields,
  path,
  label,
) {
  if (!isPlainObject0(record)) {
    return validationReject0(path, `${label} must be a record judgment`, {
      actual: typeof record,
    });
  }

  const allowedKeys = new Set(['kind', 'version', 'recordType', 'fields']);
  const unexpected = Object.keys(record).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      `${label} rejects undeclared fields`,
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      `${label} kind must be SemanticRecordJudgment0`,
      { actual: record.kind },
    );
  }

  if (record.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `${label} version must be ${CHECKER_VERSION}`,
      { actual: record.version },
    );
  }

  if (record.recordType !== expectedType) {
    return validationReject0(
      [...path, 'recordType'],
      `${label} recordType must bind the exact plan, obligation, rule, and mode`,
      { expected: expectedType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'fields'],
      `${label} fields must be an array`,
      { actual: typeof record.fields },
    );
  }

  const names = record.fields.map((field) => field?.name ?? null);
  if (!sameCanonical0(names, expectedFields)) {
    return validationReject0(
      [...path, 'fields'],
      `${label} must contain the exact canonical evidence fields`,
      { expected: expectedFields, actual: names },
    );
  }

  for (let index = 0; index < record.fields.length; index += 1) {
    const field = record.fields[index];
    if (!isPlainObject0(field)
        || field.kind !== 'SemanticRecordField0'
        || !isPlainObject0(field.judgment)) {
      return validationReject0(
        [...path, 'fields', index],
        `${label} fields must contain semantic judgment objects`,
        { actual: field },
      );
    }
  }

  return validationAccept0({
    kind: 'SemanticObligationEvidence0NF',
    recordType: expectedType,
    fieldNames: expectedFields,
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'OblTopoInd conclusion must be an object', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'planId',
    'obligationOrder',
    'dischargeOrder',
    'eventOrder',
    'sourceObligationIds',
    'terminalObligationIds',
    'fullModeObligationIds',
    'quotientModeObligationIds',
    'caseProofIds',
    'cases',
    'dischargedObligationIds',
    'openObligationIds',
    'allDependenciesClosed',
    'fullModeDischargesVerified',
    'allObligationsDischarged',
    'noOpenObligations',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'OblTopoInd conclusion rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticOblTopoIndJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'OblTopoInd conclusion kind must be SemanticOblTopoIndJudgment0',
      { actual: judgment.kind },
    );
  }

  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `OblTopoInd conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }

  if (!isIdentifier0(judgment.planId)) {
    return validationReject0(
      [...path, 'planId'],
      'OblTopoInd conclusion planId must be a canonical identifier',
      { actual: judgment.planId },
    );
  }

  for (const field of [
    'obligationOrder',
    'dischargeOrder',
    'eventOrder',
    'sourceObligationIds',
    'terminalObligationIds',
    'fullModeObligationIds',
    'quotientModeObligationIds',
    'caseProofIds',
    'cases',
    'dischargedObligationIds',
    'openObligationIds',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `OblTopoInd conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }

  for (const field of [
    'allDependenciesClosed',
    'fullModeDischargesVerified',
    'allObligationsDischarged',
    'noOpenObligations',
  ]) {
    if (judgment[field] !== true) {
      return validationReject0(
        [...path, field],
        `OblTopoInd conclusion ${field} must be true`,
        { actual: judgment[field] },
      );
    }
  }

  if (judgment.openObligationIds.length !== 0) {
    return validationReject0(
      [...path, 'openObligationIds'],
      'OblTopoInd conclusion must contain no open obligations',
      { actual: judgment.openObligationIds },
    );
  }

  return validationAccept0({
    kind: 'SemanticOblTopoIndJudgmentShape0NF',
    planId: judgment.planId,
    caseCount: judgment.cases.length,
  });
}

function checkOblTopoIndRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'OblTopoInd rule supports only close',
      { actual: node.Payload.op },
    );
  }

  const planCheck = validatePlan0(
    node.Payload.plan,
    [...path, 'Payload', 'plan'],
  );
  if (!planCheck.ok) return planCheck;

  const derived = deriveClosure0(
    planCheck,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;

  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'OblTopoInd conclusion must exactly equal the computed terminal obligation closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticOblTopoIndRule0NF',
    ruleName: 'OblTopoInd',
    operation: 'close',
    planId: planCheck.plan.planId,
    obligationCount: planCheck.plan.obligations.length,
    fullModeObligationCount: planCheck.nf.fullModeObligationIds.length,
    quotientModeObligationCount: planCheck.nf.quotientModeObligationIds.length,
    caseProofIds: [...node.Premises],
    exactLifecycleSchedule: true,
    allDependenciesClosed: true,
    fullModeDischargesVerified: true,
    noOpenObligations: true,
  });
}

function deriveClosure0(planCheck, premises, caseProofIds, path) {
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'OblTopoInd closure requires premise and proof-id arrays',
      null,
    );
  }

  const dischargeObligations = planCheck.dischargeObligations;
  if (premises.length !== dischargeObligations.length
      || caseProofIds.length !== dischargeObligations.length) {
    return validationReject0(
      [...path, 'Premises'],
      'OblTopoInd requires exactly one local case record for every obligation',
      {
        expected: dischargeObligations.length,
        actualPremises: premises.length,
        actualProofIds: caseProofIds.length,
      },
    );
  }

  const closedById = new Map();
  const cases = [];

  for (let index = 0; index < dischargeObligations.length; index += 1) {
    const obligation = dischargeObligations[index];
    const premise = premises[index];
    const casePath = [...path, 'Premises', index];

    if (!isPlainObject0(premise)) {
      return validationReject0(
        casePath,
        'OblTopoInd case premise must resolve to an earlier accepted proof node',
        { actual: premise },
      );
    }

    if (premise.RuleName !== 'Record' || premise.operation !== 'intro') {
      return validationReject0(
        casePath,
        'OblTopoInd case premise must be accepted Record.intro evidence',
        {
          actualRuleName: premise.RuleName,
          actualOperation: premise.operation,
        },
      );
    }

    const caseCheck = validateCaseRecord0(
      premise.Conclusion,
      planCheck.plan.planId,
      obligation,
      closedById,
      casePath,
    );
    if (!caseCheck.ok) return caseCheck;

    closedById.set(obligation.id, caseCheck.closed);
    cases.push(Object.freeze({
      kind: 'SemanticOblTopoIndCaseResult0',
      obligationId: obligation.id,
      mode: obligation.mode,
      dependencies: Object.freeze([...obligation.dependencies]),
      createIndex: obligation.createIndex,
      dischargeIndex: obligation.dischargeIndex,
      creationRule: obligation.creationRule,
      dischargeRule: obligation.dischargeRule,
      invariant: caseCheck.closed,
    }));
  }

  const dischargedObligationIds = dischargeObligations.map(
    (obligation) => obligation.id,
  );
  const judgment = makeSemanticOblTopoIndJudgment0({
    planId: planCheck.plan.planId,
    obligationOrder: planCheck.nf.obligationOrder,
    dischargeOrder: planCheck.nf.dischargeOrder,
    eventOrder: planCheck.nf.eventOrder,
    sourceObligationIds: planCheck.nf.sourceObligationIds,
    terminalObligationIds: planCheck.nf.terminalObligationIds,
    fullModeObligationIds: planCheck.nf.fullModeObligationIds,
    quotientModeObligationIds: planCheck.nf.quotientModeObligationIds,
    caseProofIds,
    cases,
    dischargedObligationIds,
  });

  return validationAcceptWith0({
    kind: 'SemanticOblTopoIndClosure0NF',
    planId: planCheck.plan.planId,
    obligationCount: dischargeObligations.length,
    dischargedObligationIds,
    openObligationIds: [],
  }, {
    judgment,
  });
}

function validateCaseRecord0(record, planId, obligation, closedById, path) {
  if (!isPlainObject0(record)) {
    return validationReject0(
      path,
      'OblTopoInd case conclusion must be a record judgment',
      { actual: typeof record },
    );
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'Conclusion', 'kind'],
      'OblTopoInd case conclusion must be SemanticRecordJudgment0',
      { actual: record.kind },
    );
  }

  const expectedRecordType = caseRecordType0(planId, obligation.id);
  if (record.recordType !== expectedRecordType) {
    return validationReject0(
      [...path, 'Conclusion', 'recordType'],
      'OblTopoInd case recordType must bind the plan and obligation id',
      { expected: expectedRecordType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'OblTopoInd case record fields must be an array',
      { actual: typeof record.fields },
    );
  }

  const expectedNames = [
    'closed',
    'creation',
    'discharge',
    ...obligation.dependencies.map((dependencyId) => `dep.${dependencyId}`),
  ].sort(compareText0);
  const actualNames = record.fields.map((field) => field?.name ?? null);
  if (!sameCanonical0(actualNames, expectedNames)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'OblTopoInd case fields must contain exact creation, discharge, closure, and dependency evidence',
      { expected: expectedNames, actual: actualNames },
    );
  }

  const fieldMap = new Map(record.fields.map((field) => [field.name, field.judgment]));
  if (!sameCanonical0(fieldMap.get('creation'), obligation.creationEvidence)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'OblTopoInd case creation evidence must exactly match the declared R5 creation',
      {
        obligationId: obligation.id,
        expected: obligation.creationEvidence,
        actual: fieldMap.get('creation'),
      },
    );
  }

  if (!sameCanonical0(fieldMap.get('discharge'), obligation.dischargeEvidence)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'OblTopoInd case discharge evidence must exactly match the declared permitted discharge',
      {
        obligationId: obligation.id,
        expected: obligation.dischargeEvidence,
        actual: fieldMap.get('discharge'),
      },
    );
  }

  const closed = fieldMap.get('closed');
  if (!isPlainObject0(closed)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'OblTopoInd closed invariant must be a semantic judgment object',
      { actual: closed },
    );
  }

  for (const dependencyId of obligation.dependencies) {
    const expected = closedById.get(dependencyId);
    if (expected === undefined) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'OblTopoInd case depends on an obligation without an earlier closed invariant',
        { obligationId: obligation.id, dependencyId },
      );
    }

    const actual = fieldMap.get(`dep.${dependencyId}`);
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'OblTopoInd dependency invariant must exactly match the earlier discharged obligation invariant',
        {
          obligationId: obligation.id,
          dependencyId,
          expected,
          actual,
        },
      );
    }
  }

  return validationAcceptWith0({
    kind: 'SemanticOblTopoIndCase0NF',
    planId,
    obligationId: obligation.id,
    mode: obligation.mode,
    dependencyCount: obligation.dependencies.length,
    creationRule: obligation.creationRule,
    dischargeRule: obligation.dischargeRule,
    fullModeWitnessVerified: obligation.mode === 'Full',
  }, {
    closed,
  });
}

function creationRecordType0(planId, obligationId, mode) {
  return `ObligationCreation0.${planId}.${obligationId}.${mode}`;
}

function dischargeRecordType0(planId, obligationId, rule, mode) {
  return `ObligationDischarge0.${planId}.${obligationId}.${rule}.${mode}`;
}

function caseRecordType0(planId, obligationId) {
  return `OblTopoIndCase0.${planId}.${obligationId}`;
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProofLedgerInd0(
      makeSemanticProofDAG0(baseNodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofLedgerInd0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofLedgerInd0 threw instead of returning a reject record',
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

function requireMode0(value, label) {
  if (!SEMANTIC_OBLIGATION_MODES0.includes(value)) {
    throw new TypeError(`${label} must be Full or Quot`);
  }
}

function requireDischargeRule0(value, label) {
  if (!SEMANTIC_OBLIGATION_DISCHARGE_RULES0.includes(value)) {
    throw new TypeError(`${label} must be R6, R7, or R8`);
  }
}
