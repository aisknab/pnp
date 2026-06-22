import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofMinCounterexample0,
  SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0,
} from './pcc-kernel-mincounterexample-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_LINEAR_TERMS = 4_096;
const MAX_ENV_BINDINGS = MAX_LINEAR_TERMS * 2;
const MAX_NORMALIZED_TERMS = MAX_LINEAR_TERMS * 2;
const MAX_DECIMAL_DIGITS = 2_048;
const MAX_RESULT_DECIMAL_DIGITS = 8_192;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;
const DECIMAL_PATTERN = /^(?:0|-?[1-9][0-9]*)$/;

export const SEMANTIC_INTARITH_OPERATIONS0 = Object.freeze(['prove']);

export const SEMANTIC_INTARITH_RELATIONS0 = Object.freeze([
  'eq',
  'ne',
  'lt',
  'le',
  'gt',
  'ge',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0,
  'IntArith',
]);

export function makeSemanticIntLinearTerm0({
  variable,
  coefficient,
} = {}) {
  requireIdentifier0(variable, 'makeSemanticIntLinearTerm0 variable');
  const coefficientCheck = validateDecimal0(
    coefficient,
    ['coefficient'],
    { nonzero: true },
  );
  if (!coefficientCheck.ok) {
    throw new TypeError(coefficientCheck.witness.reason);
  }

  return Object.freeze({
    kind: 'SemanticIntLinearTerm0',
    version: CHECKER_VERSION,
    variable,
    coefficient,
  });
}

export function makeSemanticIntLinearExpr0({
  constant = '0',
  terms = [],
} = {}) {
  const constantCheck = validateDecimal0(constant, ['constant']);
  if (!constantCheck.ok) {
    throw new TypeError(constantCheck.witness.reason);
  }
  if (!Array.isArray(terms)) {
    throw new TypeError('makeSemanticIntLinearExpr0 terms must be an array');
  }

  const orderedTerms = [...terms].sort((left, right) =>
    compareText0(left?.variable ?? '', right?.variable ?? ''));
  const expression = Object.freeze({
    kind: 'SemanticIntLinearExpr0',
    version: CHECKER_VERSION,
    constant,
    terms: Object.freeze(orderedTerms),
  });
  const checked = validateLinearExpr0(expression, ['expression']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return expression;
}

export function makeSemanticIntBinding0({
  variable,
  value,
} = {}) {
  requireIdentifier0(variable, 'makeSemanticIntBinding0 variable');
  const valueCheck = validateDecimal0(value, ['value']);
  if (!valueCheck.ok) throw new TypeError(valueCheck.witness.reason);

  return Object.freeze({
    kind: 'SemanticIntBinding0',
    version: CHECKER_VERSION,
    variable,
    value,
  });
}

export function makeSemanticIntEnvironment0({
  bindings = [],
} = {}) {
  if (!Array.isArray(bindings)) {
    throw new TypeError('makeSemanticIntEnvironment0 bindings must be an array');
  }

  const orderedBindings = [...bindings].sort((left, right) =>
    compareText0(left?.variable ?? '', right?.variable ?? ''));
  const environment = Object.freeze({
    kind: 'SemanticIntEnvironment0',
    version: CHECKER_VERSION,
    bindings: Object.freeze(orderedBindings),
  });
  const checked = validateEnvironment0(environment, ['environment']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return environment;
}

export function makeSemanticIntClaim0({
  claimId,
  relation,
  left,
  right,
} = {}) {
  requireIdentifier0(claimId, 'makeSemanticIntClaim0 claimId');
  if (!SEMANTIC_INTARITH_RELATIONS0.includes(relation)) {
    throw new TypeError(
      `makeSemanticIntClaim0 relation must be one of ${SEMANTIC_INTARITH_RELATIONS0.join(', ')}`,
    );
  }

  const claim = Object.freeze({
    kind: 'SemanticIntClaim0',
    version: CHECKER_VERSION,
    claimId,
    relation,
    left,
    right,
  });
  const checked = validateClaim0(claim, ['claim']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return claim;
}

export function deriveSemanticIntArithJudgment0({
  environment,
  claim,
} = {}) {
  const environmentCheck = validateEnvironment0(environment, ['environment']);
  if (!environmentCheck.ok) {
    throw new TypeError(environmentCheck.witness.reason);
  }
  const claimCheck = validateClaim0(claim, ['claim']);
  if (!claimCheck.ok) throw new TypeError(claimCheck.witness.reason);

  const derived = deriveArithmetic0(
    environmentCheck,
    claimCheck,
    ['derive'],
  );
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.judgment;
}

export function CheckSemanticKernelReadinessIntArith0() {
  const checker = 'CheckSemanticKernelReadinessIntArith0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessIntArith0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofMinCounterexample0',
    proofChecker: 'CheckSemanticKernelProofIntArith0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    intArithOperations: [...SEMANTIC_INTARITH_OPERATIONS0],
    supportedRelations: [...SEMANTIC_INTARITH_RELATIONS0],
    canonicalAffineFormsRequired: true,
    exactEnvironmentCoverageRequired: true,
    canonicalDecimalEncodingRequired: true,
    exactBigIntEvaluationRequired: true,
    boundedInputDigitsRequired: true,
    groundClaimMustEvaluateTrue: true,
    hiddenSolverSearchOptimizationAndOracleForbidden: true,
    callerTruthAndCertificateAssertionsForbidden: true,
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
        reason: 'IntArith-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

export function CheckSemanticKernelProofIntArith0(input) {
  const checker = 'CheckSemanticKernelProofIntArith0';
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
        reason: 'IntArith-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0.includes(
      node.RuleName,
    ),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofMinCounterexample0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample sub-DAG rejected under the predecessor semantic checker',
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

    const semantic = node.RuleName === 'IntArith'
      ? checkIntArithRule0(node, premises, path)
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0.includes(rule),
  );
  const intArithNodeCount = summaries.filter(
    (node) => node.RuleName === 'IntArith',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofIntArith0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofMinCounterexample0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedIntArithOperations: [...SEMANTIC_INTARITH_OPERATIONS0],
      supportedIntArithRelations: [...SEMANTIC_INTARITH_RELATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      intArithNodeCount,
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
        kind: 'SemanticIntArithProofInput0NF',
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
      kind: 'SemanticIntArithProofInput0NF',
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
        'IntArith-extended semantic proof node rejects undeclared fields',
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
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'IntArith-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'IntArith-extended semantic kernel accepts Full mode only',
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
    if (node.RuleName === 'IntArith') {
      const payload = validateIntArithPayload0(
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
    kind: 'SemanticIntArithProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateIntArithPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'environment', 'claim']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith payload rejects caller-supplied truth, certificate, result, optimization, minimization, solver, search, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_INTARITH_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'IntArith operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_INTARITH_OPERATIONS0],
      },
    );
  }
  const environment = validateEnvironment0(
    payload.environment,
    [...path, 'environment'],
  );
  if (!environment.ok) return environment;
  return validateClaim0(payload.claim, [...path, 'claim']);
}

function validateLinearTerm0(term, path, {
  maxDigits = MAX_DECIMAL_DIGITS,
} = {}) {
  if (!isPlainObject0(term)) {
    return validationReject0(path, 'IntArith linear term must be an object', {
      actual: typeof term,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'variable', 'coefficient',
  ]);
  const unexpected = Object.keys(term).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith linear term rejects undeclared value, result, truth, or certificate fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (term.kind !== 'SemanticIntLinearTerm0') {
    return validationReject0(
      [...path, 'kind'],
      'IntArith linear term kind must be SemanticIntLinearTerm0',
      { actual: term.kind },
    );
  }
  if (term.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `IntArith linear term version must be ${CHECKER_VERSION}`,
      { actual: term.version },
    );
  }
  if (!isIdentifier0(term.variable)) {
    return validationReject0(
      [...path, 'variable'],
      'IntArith variable must be a canonical identifier',
      { actual: term.variable },
    );
  }
  const coefficient = validateDecimal0(
    term.coefficient,
    [...path, 'coefficient'],
    { nonzero: true, maxDigits },
  );
  if (!coefficient.ok) return coefficient;

  return validationAcceptWith0({
    kind: 'SemanticIntLinearTerm0NF',
    variable: term.variable,
    coefficient: term.coefficient,
  }, {
    term,
    coefficientValue: coefficient.value,
  });
}

function validateLinearExpr0(expression, path, {
  maxDigits = MAX_DECIMAL_DIGITS,
  maxTerms = MAX_LINEAR_TERMS,
} = {}) {
  if (!isPlainObject0(expression)) {
    return validationReject0(path, 'IntArith linear expression must be an object', {
      actual: typeof expression,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'constant', 'terms']);
  const unexpected = Object.keys(expression)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith linear expression rejects undeclared evaluation, result, solver, or certificate fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (expression.kind !== 'SemanticIntLinearExpr0') {
    return validationReject0(
      [...path, 'kind'],
      'IntArith linear expression kind must be SemanticIntLinearExpr0',
      { actual: expression.kind },
    );
  }
  if (expression.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `IntArith linear expression version must be ${CHECKER_VERSION}`,
      { actual: expression.version },
    );
  }
  const constant = validateDecimal0(
    expression.constant,
    [...path, 'constant'],
    { maxDigits },
  );
  if (!constant.ok) return constant;
  if (!Array.isArray(expression.terms)) {
    return validationReject0(
      [...path, 'terms'],
      'IntArith linear expression terms must be an array',
      { actual: typeof expression.terms },
    );
  }
  if (expression.terms.length > maxTerms) {
    return validationReject0(
      [...path, 'terms'],
      'IntArith linear expression exceeds maxTerms',
      { maxTerms, actual: expression.terms.length },
    );
  }

  const variables = [];
  const coefficientByVariable = new Map();
  let previousVariable = null;
  for (let index = 0; index < expression.terms.length; index += 1) {
    const termCheck = validateLinearTerm0(
      expression.terms[index],
      [...path, 'terms', index],
      { maxDigits },
    );
    if (!termCheck.ok) return termCheck;
    const variable = termCheck.term.variable;
    if (previousVariable !== null
        && compareText0(previousVariable, variable) >= 0) {
      return validationReject0(
        [...path, 'terms'],
        'IntArith linear terms must be strictly ordered by unique variable id',
        {
          previousVariable,
          variable,
          index,
        },
      );
    }
    previousVariable = variable;
    variables.push(variable);
    coefficientByVariable.set(variable, termCheck.coefficientValue);
  }

  return validationAcceptWith0({
    kind: 'SemanticIntLinearExpr0NF',
    constant: expression.constant,
    termCount: expression.terms.length,
    variables,
    canonicalAffineForm: true,
  }, {
    expression,
    constantValue: constant.value,
    coefficientByVariable,
    variables,
  });
}

function validateBinding0(binding, path) {
  if (!isPlainObject0(binding)) {
    return validationReject0(path, 'IntArith binding must be an object', {
      actual: typeof binding,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'variable', 'value']);
  const unexpected = Object.keys(binding).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith binding rejects undeclared source, proof, truth, or certificate fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (binding.kind !== 'SemanticIntBinding0') {
    return validationReject0(
      [...path, 'kind'],
      'IntArith binding kind must be SemanticIntBinding0',
      { actual: binding.kind },
    );
  }
  if (binding.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `IntArith binding version must be ${CHECKER_VERSION}`,
      { actual: binding.version },
    );
  }
  if (!isIdentifier0(binding.variable)) {
    return validationReject0(
      [...path, 'variable'],
      'IntArith binding variable must be a canonical identifier',
      { actual: binding.variable },
    );
  }
  const value = validateDecimal0(binding.value, [...path, 'value']);
  if (!value.ok) return value;

  return validationAcceptWith0({
    kind: 'SemanticIntBinding0NF',
    variable: binding.variable,
    value: binding.value,
  }, {
    binding,
    bigintValue: value.value,
  });
}

function validateEnvironment0(environment, path) {
  if (!isPlainObject0(environment)) {
    return validationReject0(path, 'IntArith environment must be an object', {
      actual: typeof environment,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'bindings']);
  const unexpected = Object.keys(environment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith environment rejects undeclared evaluation, completeness, solver, or certificate fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (environment.kind !== 'SemanticIntEnvironment0') {
    return validationReject0(
      [...path, 'kind'],
      'IntArith environment kind must be SemanticIntEnvironment0',
      { actual: environment.kind },
    );
  }
  if (environment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `IntArith environment version must be ${CHECKER_VERSION}`,
      { actual: environment.version },
    );
  }
  if (!Array.isArray(environment.bindings)) {
    return validationReject0(
      [...path, 'bindings'],
      'IntArith environment bindings must be an array',
      { actual: typeof environment.bindings },
    );
  }
  if (environment.bindings.length > MAX_ENV_BINDINGS) {
    return validationReject0(
      [...path, 'bindings'],
      'IntArith environment exceeds maxBindings',
      { maxBindings: MAX_ENV_BINDINGS, actual: environment.bindings.length },
    );
  }

  const variables = [];
  const valueByVariable = new Map();
  let previousVariable = null;
  for (let index = 0; index < environment.bindings.length; index += 1) {
    const bindingCheck = validateBinding0(
      environment.bindings[index],
      [...path, 'bindings', index],
    );
    if (!bindingCheck.ok) return bindingCheck;
    const variable = bindingCheck.binding.variable;
    if (previousVariable !== null
        && compareText0(previousVariable, variable) >= 0) {
      return validationReject0(
        [...path, 'bindings'],
        'IntArith bindings must be strictly ordered by unique variable id',
        {
          previousVariable,
          variable,
          index,
        },
      );
    }
    previousVariable = variable;
    variables.push(variable);
    valueByVariable.set(variable, bindingCheck.bigintValue);
  }

  return validationAcceptWith0({
    kind: 'SemanticIntEnvironment0NF',
    bindingCount: environment.bindings.length,
    variables,
    canonicalBindingOrder: true,
  }, {
    environment,
    variables,
    valueByVariable,
  });
}

function validateClaim0(claim, path) {
  if (!isPlainObject0(claim)) {
    return validationReject0(path, 'IntArith claim must be an object', {
      actual: typeof claim,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'claimId', 'relation', 'left', 'right',
  ]);
  const unexpected = Object.keys(claim).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith claim rejects caller-supplied truth, value, comparison, normalized form, certificate, solver, search, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (claim.kind !== 'SemanticIntClaim0') {
    return validationReject0(
      [...path, 'kind'],
      'IntArith claim kind must be SemanticIntClaim0',
      { actual: claim.kind },
    );
  }
  if (claim.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `IntArith claim version must be ${CHECKER_VERSION}`,
      { actual: claim.version },
    );
  }
  if (!isIdentifier0(claim.claimId)) {
    return validationReject0(
      [...path, 'claimId'],
      'IntArith claimId must be a canonical identifier',
      { actual: claim.claimId },
    );
  }
  if (!SEMANTIC_INTARITH_RELATIONS0.includes(claim.relation)) {
    return validationReject0(
      [...path, 'relation'],
      'IntArith relation is unsupported',
      {
        actual: claim.relation,
        supportedRelations: [...SEMANTIC_INTARITH_RELATIONS0],
      },
    );
  }
  const left = validateLinearExpr0(claim.left, [...path, 'left']);
  if (!left.ok) return left;
  const right = validateLinearExpr0(claim.right, [...path, 'right']);
  if (!right.ok) return right;

  const requiredVariables = [...new Set([
    ...left.variables,
    ...right.variables,
  ])].sort(compareText0);

  return validationAcceptWith0({
    kind: 'SemanticIntClaim0NF',
    claimId: claim.claimId,
    relation: claim.relation,
    requiredVariables,
    canonicalAffineForms: true,
  }, {
    claim,
    left,
    right,
    requiredVariables,
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'IntArith conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'claimId', 'relation', 'left', 'right',
    'environment', 'variables', 'leftValue', 'rightValue', 'difference',
    'comparison', 'normalizedDifference', 'relationVerified',
    'canonicalAffineForms', 'exactEnvironmentCoverage',
    'canonicalDecimalEncoding', 'exactBigIntEvaluation',
    'boundedInputDigits', 'noSolverSearchOptimizationOrOracleUsed',
    'terminalJudgmentComputed',
  ]);
  const unexpected = Object.keys(judgment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'IntArith conclusion rejects undeclared readiness, truth, certificate, optimization, solver, search, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticIntArithJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'IntArith conclusion kind must be SemanticIntArithJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `IntArith conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  if (!Array.isArray(judgment.variables)) {
    return validationReject0(
      [...path, 'variables'],
      'IntArith conclusion variables must be an array',
      { actual: typeof judgment.variables },
    );
  }
  for (const field of ['leftValue', 'rightValue', 'difference']) {
    const decimal = validateDecimal0(judgment[field], [...path, field], {
      maxDigits: MAX_RESULT_DECIMAL_DIGITS,
    });
    if (!decimal.ok) return decimal;
  }
  if (![-1, 0, 1].includes(judgment.comparison)) {
    return validationReject0(
      [...path, 'comparison'],
      'IntArith conclusion comparison must be -1, 0, or 1',
      { actual: judgment.comparison },
    );
  }
  const normalized = validateLinearExpr0(
    judgment.normalizedDifference,
    [...path, 'normalizedDifference'],
    {
      maxDigits: MAX_RESULT_DECIMAL_DIGITS,
      maxTerms: MAX_NORMALIZED_TERMS,
    },
  );
  if (!normalized.ok) return normalized;

  return validationAccept0({
    kind: 'SemanticIntArithJudgmentShape0NF',
    claimId: judgment.claimId,
    relation: judgment.relation,
    comparison: judgment.comparison,
  });
}

function checkIntArithRule0(node, premises, path) {
  if (node.Payload.op !== 'prove') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'IntArith rule supports only prove',
      { actual: node.Payload.op },
    );
  }
  if (premises.length !== 0 || node.Premises.length !== 0) {
    return validationReject0(
      [...path, 'Premises'],
      'IntArith prove is a closed exact evaluation and must not consume premises',
      { actualPremiseIds: node.Premises },
    );
  }
  const environmentCheck = validateEnvironment0(
    node.Payload.environment,
    [...path, 'Payload', 'environment'],
  );
  if (!environmentCheck.ok) return environmentCheck;
  const claimCheck = validateClaim0(
    node.Payload.claim,
    [...path, 'Payload', 'claim'],
  );
  if (!claimCheck.ok) return claimCheck;
  const derived = deriveArithmetic0(
    environmentCheck,
    claimCheck,
    path,
  );
  if (!derived.ok) return derived;
  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'IntArith conclusion must exactly equal the computed bounded integer decision',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticIntArithRule0NF',
    ruleName: 'IntArith',
    operation: 'prove',
    claimId: claimCheck.claim.claimId,
    relation: claimCheck.claim.relation,
    variableCount: claimCheck.requiredVariables.length,
    comparison: derived.comparison,
    exactBigIntEvaluation: true,
    relationVerified: true,
  });
}

function deriveArithmetic0(environmentCheck, claimCheck, path) {
  const expectedVariables = claimCheck.requiredVariables;
  const actualVariables = environmentCheck.variables;
  if (!sameCanonical0(actualVariables, expectedVariables)) {
    const missingVariables = expectedVariables.filter(
      (variable) => !environmentCheck.valueByVariable.has(variable),
    );
    const extraVariables = actualVariables.filter(
      (variable) => !expectedVariables.includes(variable),
    );
    return validationReject0(
      [...path, 'environment', 'bindings'],
      'IntArith environment must bind exactly the variables used by the claim',
      {
        expectedVariables,
        actualVariables,
        missingVariables,
        extraVariables,
      },
    );
  }

  const leftValue = evaluateLinearExpr0(
    claimCheck.left,
    environmentCheck.valueByVariable,
  );
  const rightValue = evaluateLinearExpr0(
    claimCheck.right,
    environmentCheck.valueByVariable,
  );
  const differenceValue = leftValue - rightValue;
  for (const [field, value] of [
    ['leftValue', leftValue],
    ['rightValue', rightValue],
    ['difference', differenceValue],
  ]) {
    const digits = decimalDigits0(value);
    if (digits > MAX_RESULT_DECIMAL_DIGITS) {
      return validationReject0(
        [...path, field],
        'IntArith computed result exceeds maxResultDigits',
        {
          field,
          maxResultDigits: MAX_RESULT_DECIMAL_DIGITS,
          actualDigits: digits,
        },
      );
    }
  }

  const comparison = leftValue < rightValue
    ? -1
    : leftValue > rightValue
      ? 1
      : 0;
  if (!relationHolds0(claimCheck.claim.relation, comparison)) {
    return validationReject0(
      [...path, 'claim'],
      'IntArith claim evaluates to false',
      {
        claimId: claimCheck.claim.claimId,
        relation: claimCheck.claim.relation,
        leftValue: leftValue.toString(),
        rightValue: rightValue.toString(),
        comparison,
      },
    );
  }

  const normalizedDifference = subtractLinearExpr0(
    claimCheck.left,
    claimCheck.right,
  );
  const judgment = Object.freeze({
    kind: 'SemanticIntArithJudgment0',
    version: CHECKER_VERSION,
    claimId: claimCheck.claim.claimId,
    relation: claimCheck.claim.relation,
    left: claimCheck.claim.left,
    right: claimCheck.claim.right,
    environment: environmentCheck.environment,
    variables: Object.freeze([...expectedVariables]),
    leftValue: leftValue.toString(),
    rightValue: rightValue.toString(),
    difference: differenceValue.toString(),
    comparison,
    normalizedDifference,
    relationVerified: true,
    canonicalAffineForms: true,
    exactEnvironmentCoverage: true,
    canonicalDecimalEncoding: true,
    exactBigIntEvaluation: true,
    boundedInputDigits: true,
    noSolverSearchOptimizationOrOracleUsed: true,
    terminalJudgmentComputed: true,
  });

  return validationAcceptWith0({
    kind: 'SemanticIntArithEvaluation0NF',
    claimId: claimCheck.claim.claimId,
    relation: claimCheck.claim.relation,
    comparison,
    variableCount: expectedVariables.length,
  }, {
    judgment,
    comparison,
  });
}

function evaluateLinearExpr0(expressionCheck, valueByVariable) {
  let value = expressionCheck.constantValue;
  for (const variable of expressionCheck.variables) {
    value += expressionCheck.coefficientByVariable.get(variable)
      * valueByVariable.get(variable);
  }
  return value;
}

function subtractLinearExpr0(leftCheck, rightCheck) {
  const coefficientByVariable = new Map();
  for (const variable of leftCheck.variables) {
    coefficientByVariable.set(
      variable,
      leftCheck.coefficientByVariable.get(variable),
    );
  }
  for (const variable of rightCheck.variables) {
    coefficientByVariable.set(
      variable,
      (coefficientByVariable.get(variable) ?? 0n)
        - rightCheck.coefficientByVariable.get(variable),
    );
  }

  const terms = [...coefficientByVariable.entries()]
    .filter(([, coefficient]) => coefficient !== 0n)
    .sort(([leftVariable], [rightVariable]) =>
      compareText0(leftVariable, rightVariable))
    .map(([variable, coefficient]) => Object.freeze({
      kind: 'SemanticIntLinearTerm0',
      version: CHECKER_VERSION,
      variable,
      coefficient: coefficient.toString(),
    }));

  return Object.freeze({
    kind: 'SemanticIntLinearExpr0',
    version: CHECKER_VERSION,
    constant: (leftCheck.constantValue - rightCheck.constantValue).toString(),
    terms: Object.freeze(terms),
  });
}

function relationHolds0(relation, comparison) {
  switch (relation) {
    case 'eq': return comparison === 0;
    case 'ne': return comparison !== 0;
    case 'lt': return comparison < 0;
    case 'le': return comparison <= 0;
    case 'gt': return comparison > 0;
    case 'ge': return comparison >= 0;
    default: return false;
  }
}

function validateDecimal0(value, path, {
  nonzero = false,
  maxDigits = MAX_DECIMAL_DIGITS,
} = {}) {
  if (typeof value !== 'string' || !DECIMAL_PATTERN.test(value)) {
    return validationReject0(
      path,
      'IntArith integers must use canonical signed decimal strings',
      { actual: value },
    );
  }
  const digits = value.startsWith('-') ? value.length - 1 : value.length;
  if (digits > maxDigits) {
    return validationReject0(
      path,
      'IntArith integer exceeds the decimal digit bound',
      { maxDigits, actualDigits: digits },
    );
  }
  const bigint = BigInt(value);
  if (nonzero && bigint === 0n) {
    return validationReject0(
      path,
      'IntArith linear coefficients must be nonzero',
      { actual: value },
    );
  }
  return validationAcceptWith0({
    kind: 'SemanticCanonicalInteger0NF',
    decimal: value,
    digits,
  }, {
    value: bigint,
  });
}

function decimalDigits0(value) {
  const text = value < 0n ? (-value).toString() : value.toString();
  return text.length;
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofMinCounterexample0(
      makeSemanticProofDAG0(nodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofMinCounterexample0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofMinCounterexample0 threw instead of returning a reject record',
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
