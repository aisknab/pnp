import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofTraceInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0,
} from './pcc-kernel-traceind-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  substituteSemanticJudgment0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_DOMAIN_SIZE = 100_000;
const MAX_TERM_DEPTH = 256;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_FINITEEXHAUST_OPERATIONS0 = Object.freeze(['close']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_TRACEIND0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0,
  'FiniteExhaust',
]);

/**
 * Constructs the explicit finite domain used by FiniteExhaust. The constructor
 * canonicalizes element order, while the checker independently revalidates
 * closedness, uniqueness, sort agreement, cardinality, and ordering.
 */
export function makeSemanticFiniteDomain0({
  domainId,
  elementSort,
  elements = [],
} = {}) {
  requireIdentifier0(domainId, 'makeSemanticFiniteDomain0 domainId');
  requireText0(elementSort, 'makeSemanticFiniteDomain0 elementSort');
  if (!Array.isArray(elements) || elements.length === 0) {
    throw new TypeError(
      'makeSemanticFiniteDomain0 elements must be a nonempty array',
    );
  }

  const canonicalElements = [...elements].sort(compareCanonical0);
  const keys = canonicalElements.map((element) => stableStringify0(element));
  if (new Set(keys).size !== keys.length) {
    throw new TypeError('makeSemanticFiniteDomain0 elements must be unique');
  }
  for (let index = 0; index < canonicalElements.length; index += 1) {
    const checked = validateClosedTerm0(
      canonicalElements[index],
      ['elements', index],
      0,
    );
    if (!checked.ok) throw new TypeError(checked.witness.reason);
    if (checked.sort !== elementSort) {
      throw new TypeError(
        'makeSemanticFiniteDomain0 element sort must match elementSort',
      );
    }
  }

  return Object.freeze({
    kind: 'SemanticFiniteDomain0',
    version: CHECKER_VERSION,
    domainId,
    elementSort,
    cardinality: canonicalElements.length,
    elements: Object.freeze(canonicalElements),
  });
}

/**
 * A local finite-exhaustion case is accepted Record.intro evidence binding the
 * exact enumerated element to the exact instantiated body judgment.
 */
export function makeSemanticFiniteExhaustCase0({
  domainId,
  index,
  element,
  instance,
} = {}) {
  requireIdentifier0(domainId, 'makeSemanticFiniteExhaustCase0 domainId');
  requireIndex0(index, 'makeSemanticFiniteExhaustCase0 index');
  if (!isPlainObject0(element)) {
    throw new TypeError(
      'makeSemanticFiniteExhaustCase0 element must be a semantic term object',
    );
  }
  if (!isPlainObject0(instance)) {
    throw new TypeError(
      'makeSemanticFiniteExhaustCase0 instance must be a semantic judgment object',
    );
  }

  return makeSemanticRecordJudgment0(
    caseRecordType0(domainId, index),
    [
      makeSemanticRecordField0(
        'element',
        makeSemanticEqJudgment0(element, element),
      ),
      makeSemanticRecordField0('instance', instance),
    ],
  );
}

export function makeSemanticFiniteExhaustJudgment0({
  domainId,
  elementSort,
  variable,
  body,
  elements,
  caseProofIds,
  cases,
} = {}) {
  requireIdentifier0(domainId, 'makeSemanticFiniteExhaustJudgment0 domainId');
  requireText0(elementSort, 'makeSemanticFiniteExhaustJudgment0 elementSort');
  for (const [name, value] of Object.entries({
    elements,
    caseProofIds,
    cases,
  })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticFiniteExhaustJudgment0 ${name} must be an array`);
    }
  }

  const frozenElements = Object.freeze([...elements]);
  const universalJudgment = Object.freeze({
    kind: 'SemanticForallFiniteJudgment0',
    version: CHECKER_VERSION,
    variable,
    domain: frozenElements,
    body,
  });

  return Object.freeze({
    kind: 'SemanticFiniteExhaustJudgment0',
    version: CHECKER_VERSION,
    domainId,
    elementSort,
    variable,
    body,
    elements: frozenElements,
    cardinality: frozenElements.length,
    universalJudgment,
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    canonicalEnumeration: true,
    allElementsCovered: true,
    noDuplicateElements: true,
    noOmittedElements: true,
    exactCardinality: true,
  });
}

/**
 * Generator helper. The checker recomputes the same universal conclusion and
 * never trusts caller-provided completeness or coverage flags.
 */
export function deriveSemanticFiniteExhaustJudgment0({
  domain,
  variable,
  body,
  caseRecords,
  caseProofIds,
} = {}) {
  const domainCheck = validateDomain0(domain, ['domain']);
  if (!domainCheck.ok) throw new TypeError(domainCheck.witness.reason);
  const templateCheck = validateTemplate0(
    variable,
    body,
    domainCheck.domain,
    ['template'],
  );
  if (!templateCheck.ok) throw new TypeError(templateCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError(
      'deriveSemanticFiniteExhaustJudgment0 requires case arrays',
    );
  }

  const derived = deriveClosure0(
    domainCheck,
    variable,
    body,
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

export function CheckSemanticKernelReadinessFiniteExhaust0() {
  const checker = 'CheckSemanticKernelReadinessFiniteExhaust0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessFiniteExhaust0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofTraceInd0',
    proofChecker: 'CheckSemanticKernelProofFiniteExhaust0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    finiteExhaustOperations: [...SEMANTIC_FINITEEXHAUST_OPERATIONS0],
    explicitFiniteDomainRequired: true,
    canonicalCompleteEnumerationRequired: true,
    exactCardinalityRequired: true,
    acceptedPerElementCasesRequired: true,
    duplicateAndOmissionRejection: true,
    universalConclusionComputed: true,
    emptyDomainNotAcceptedInVersion0: true,
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
        reason: 'FiniteExhaust-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks predecessor rule families with the merged TraceInd checker, then
 * validates FiniteExhaust as exact coverage of a canonical explicit domain.
 */
export function CheckSemanticKernelProofFiniteExhaust0(input) {
  const checker = 'CheckSemanticKernelProofFiniteExhaust0';
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
        reason: 'FiniteExhaust-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofTraceInd0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd sub-DAG rejected under the predecessor semantic checker',
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
    if (node.RuleName === 'FiniteExhaust') {
      semantic = checkFiniteExhaustRule0(node, premises, path);
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0.includes(rule),
  );
  const finiteExhaustNodeCount = summaries.filter(
    (node) => node.RuleName === 'FiniteExhaust',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofFiniteExhaust0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofTraceInd0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_FINITEEXHAUST0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedFiniteExhaustOperations: [...SEMANTIC_FINITEEXHAUST_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      finiteExhaustNodeCount,
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
      { kind: 'SemanticFiniteExhaustProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticFiniteExhaustProofInput0NF', form: 'object', nodeCount: nodes.length },
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
        'FiniteExhaust-extended semantic proof node rejects undeclared fields',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'FiniteExhaust-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'FiniteExhaust-extended semantic kernel accepts Full mode only',
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

    if (node.RuleName === 'FiniteExhaust') {
      const payload = validateFiniteExhaustPayload0(
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
    kind: 'SemanticFiniteExhaustProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateFiniteExhaustPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'domain', 'variable', 'body']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteExhaust payload rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (!SEMANTIC_FINITEEXHAUST_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'FiniteExhaust operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_FINITEEXHAUST_OPERATIONS0],
      },
    );
  }

  const domain = validateDomain0(payload.domain, [...path, 'domain']);
  if (!domain.ok) return domain;
  return validateTemplate0(
    payload.variable,
    payload.body,
    domain.domain,
    [...path, 'template'],
  );
}

function validateDomain0(domain, path) {
  if (!isPlainObject0(domain)) {
    return validationReject0(path, 'FiniteExhaust domain must be an object', {
      actual: typeof domain,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'domainId',
    'elementSort',
    'cardinality',
    'elements',
  ]);
  const unexpected = Object.keys(domain).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteExhaust domain rejects undeclared completeness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (domain.kind !== 'SemanticFiniteDomain0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteExhaust domain kind must be SemanticFiniteDomain0',
      { actual: domain.kind },
    );
  }

  if (domain.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteExhaust domain version must be ${CHECKER_VERSION}`,
      { actual: domain.version },
    );
  }

  if (!isIdentifier0(domain.domainId)) {
    return validationReject0(
      [...path, 'domainId'],
      'FiniteExhaust domainId must be a canonical identifier',
      { actual: domain.domainId },
    );
  }

  if (!isText0(domain.elementSort)) {
    return validationReject0(
      [...path, 'elementSort'],
      'FiniteExhaust elementSort must be nonempty',
      { actual: domain.elementSort },
    );
  }

  if (!Array.isArray(domain.elements) || domain.elements.length === 0) {
    return validationReject0(
      [...path, 'elements'],
      'FiniteExhaust version zero requires a nonempty explicit domain',
      {
        actual: Array.isArray(domain.elements)
          ? domain.elements.length
          : typeof domain.elements,
      },
    );
  }

  if (domain.elements.length > MAX_DOMAIN_SIZE) {
    return validationReject0(
      [...path, 'elements'],
      'FiniteExhaust domain exceeds maxDomainSize',
      { maxDomainSize: MAX_DOMAIN_SIZE, actual: domain.elements.length },
    );
  }

  if (!Number.isSafeInteger(domain.cardinality)
      || domain.cardinality !== domain.elements.length) {
    return validationReject0(
      [...path, 'cardinality'],
      'FiniteExhaust domain cardinality must exactly equal enumeration length',
      { expected: domain.elements.length, actual: domain.cardinality },
    );
  }

  const keys = [];
  for (let index = 0; index < domain.elements.length; index += 1) {
    const element = validateClosedTerm0(
      domain.elements[index],
      [...path, 'elements', index],
      0,
    );
    if (!element.ok) return element;
    if (element.sort !== domain.elementSort) {
      return validationReject0(
        [...path, 'elements', index, 'sort'],
        'FiniteExhaust domain element sort must match elementSort',
        { expected: domain.elementSort, actual: element.sort },
      );
    }
    keys.push(stableStringify0(domain.elements[index]));
  }

  if (new Set(keys).size !== keys.length) {
    return validationReject0(
      [...path, 'elements'],
      'FiniteExhaust domain enumeration must not contain duplicate elements',
      { elements: domain.elements },
    );
  }

  const sortedKeys = [...keys].sort(compareText0);
  if (!sameCanonical0(keys, sortedKeys)) {
    return validationReject0(
      [...path, 'elements'],
      'FiniteExhaust domain elements must be in canonical order',
      { expectedKeys: sortedKeys, actualKeys: keys },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticFiniteDomain0NF',
    domainId: domain.domainId,
    elementSort: domain.elementSort,
    cardinality: domain.cardinality,
    elementDigests: domain.elements.map((element) => digestCanonical0(element)),
    canonicalEnumeration: true,
    noDuplicateElements: true,
    exactCardinality: true,
  }, {
    domain,
    elements: domain.elements,
  });
}

function validateTemplate0(variable, body, domain, path) {
  const variableCheck = validateVariable0(
    variable,
    [...path, 'variable'],
  );
  if (!variableCheck.ok) return variableCheck;
  if (variable.sort !== domain.elementSort) {
    return validationReject0(
      [...path, 'variable', 'sort'],
      'FiniteExhaust variable sort must match the domain element sort',
      { expected: domain.elementSort, actual: variable.sort },
    );
  }

  if (!isPlainObject0(body)) {
    return validationReject0(
      [...path, 'body'],
      'FiniteExhaust body must be a semantic judgment object',
      { actual: typeof body },
    );
  }
  const allowedBodyKeys = body.kind === 'SemanticEqJudgment0'
    ? new Set(['kind', 'left', 'right'])
    : body.kind === 'SemanticFormulaJudgment0'
      ? new Set(['kind', 'formula'])
      : null;
  if (allowedBodyKeys === null) {
    return validationReject0(
      [...path, 'body', 'kind'],
      'FiniteExhaust body judgment kind is unsupported',
      {
        actual: body.kind,
        supportedKinds: ['SemanticEqJudgment0', 'SemanticFormulaJudgment0'],
      },
    );
  }
  const unexpectedBodyKeys = Object.keys(body)
    .filter((key) => !allowedBodyKeys.has(key));
  if (unexpectedBodyKeys.length !== 0) {
    return validationReject0(
      [...path, 'body', unexpectedBodyKeys[0]],
      'FiniteExhaust body rejects undeclared fields',
      { unexpectedFields: unexpectedBodyKeys.sort() },
    );
  }

  try {
    const firstInstance = substituteSemanticJudgment0(
      body,
      variable,
      domain.elements[0],
    );
    return validationAcceptWith0({
      kind: 'SemanticFiniteExhaustTemplate0NF',
      variable,
      bodyKind: body.kind,
      firstInstanceKind: firstInstance.kind,
    }, {
      variable,
      body,
    });
  } catch (error) {
    return validationReject0(
      [...path, 'body'],
      'FiniteExhaust body must support exact typed substitution over the domain',
      {
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    );
  }
}

function validateVariable0(variable, path) {
  if (!isPlainObject0(variable)) {
    return validationReject0(path, 'FiniteExhaust variable must be an object', {
      actual: typeof variable,
    });
  }
  const allowedKeys = new Set(['kind', 'name', 'sort']);
  const unexpected = Object.keys(variable).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteExhaust variable rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (variable.kind !== 'SemanticVar0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteExhaust variable kind must be SemanticVar0',
      { actual: variable.kind },
    );
  }
  if (!isText0(variable.name) || !isText0(variable.sort)) {
    return validationReject0(
      path,
      'FiniteExhaust variable name and sort must be nonempty',
      { actual: variable },
    );
  }
  return validationAccept0({
    kind: 'SemanticFiniteExhaustVariable0NF',
    name: variable.name,
    sort: variable.sort,
  });
}

function validateClosedTerm0(term, path, depth) {
  if (depth > MAX_TERM_DEPTH) {
    return validationReject0(path, 'FiniteExhaust term exceeds maxTermDepth', {
      maxTermDepth: MAX_TERM_DEPTH,
    });
  }
  if (!isPlainObject0(term)) {
    return validationReject0(path, 'FiniteExhaust domain term must be an object', {
      actual: typeof term,
    });
  }

  if (term.kind === 'SemanticVar0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteExhaust domain elements must be closed terms, not variables',
      { actual: term },
    );
  }

  if (term.kind === 'SemanticConst0') {
    const allowedKeys = new Set(['kind', 'name', 'sort']);
    const unexpected = Object.keys(term).filter((key) => !allowedKeys.has(key));
    if (unexpected.length !== 0) {
      return validationReject0(
        [...path, unexpected[0]],
        'FiniteExhaust constant term rejects undeclared fields',
        { unexpectedFields: unexpected.sort() },
      );
    }
    if (!isText0(term.name) || !isText0(term.sort)) {
      return validationReject0(
        path,
        'FiniteExhaust constant name and sort must be nonempty',
        { actual: term },
      );
    }
    return validationAcceptWith0({
      kind: 'SemanticFiniteExhaustClosedTerm0NF',
      termKind: term.kind,
      sort: term.sort,
    }, {
      sort: term.sort,
    });
  }

  if (term.kind === 'SemanticApp0') {
    const allowedKeys = new Set(['kind', 'symbol', 'args', 'sort']);
    const unexpected = Object.keys(term).filter((key) => !allowedKeys.has(key));
    if (unexpected.length !== 0) {
      return validationReject0(
        [...path, unexpected[0]],
        'FiniteExhaust application term rejects undeclared fields',
        { unexpectedFields: unexpected.sort() },
      );
    }
    if (!isText0(term.symbol) || !isText0(term.sort)) {
      return validationReject0(
        path,
        'FiniteExhaust application symbol and sort must be nonempty',
        { actual: term },
      );
    }
    if (!Array.isArray(term.args)) {
      return validationReject0(
        [...path, 'args'],
        'FiniteExhaust application args must be an array',
        { actual: typeof term.args },
      );
    }
    for (let index = 0; index < term.args.length; index += 1) {
      const argument = validateClosedTerm0(
        term.args[index],
        [...path, 'args', index],
        depth + 1,
      );
      if (!argument.ok) return argument;
    }
    return validationAcceptWith0({
      kind: 'SemanticFiniteExhaustClosedTerm0NF',
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
    'FiniteExhaust domain term kind is unsupported',
    {
      actual: term.kind,
      supportedKinds: ['SemanticConst0', 'SemanticApp0'],
    },
  );
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'FiniteExhaust conclusion must be an object', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'domainId',
    'elementSort',
    'variable',
    'body',
    'elements',
    'cardinality',
    'universalJudgment',
    'caseProofIds',
    'cases',
    'canonicalEnumeration',
    'allElementsCovered',
    'noDuplicateElements',
    'noOmittedElements',
    'exactCardinality',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteExhaust conclusion rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticFiniteExhaustJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteExhaust conclusion kind must be SemanticFiniteExhaustJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteExhaust conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }

  const domain = validateDomain0({
    kind: 'SemanticFiniteDomain0',
    version: CHECKER_VERSION,
    domainId: judgment.domainId,
    elementSort: judgment.elementSort,
    cardinality: judgment.cardinality,
    elements: judgment.elements,
  }, path);
  if (!domain.ok) return domain;

  const template = validateTemplate0(
    judgment.variable,
    judgment.body,
    domain.domain,
    path,
  );
  if (!template.ok) return template;

  const expectedUniversal = {
    kind: 'SemanticForallFiniteJudgment0',
    version: CHECKER_VERSION,
    variable: judgment.variable,
    domain: judgment.elements,
    body: judgment.body,
  };
  if (!sameCanonical0(judgment.universalJudgment, expectedUniversal)) {
    return validationReject0(
      [...path, 'universalJudgment'],
      'FiniteExhaust universal judgment must exactly bind the enumerated domain and body',
      { expected: expectedUniversal, actual: judgment.universalJudgment },
    );
  }

  if (!Array.isArray(judgment.caseProofIds)
      || !Array.isArray(judgment.cases)) {
    return validationReject0(
      path,
      'FiniteExhaust conclusion caseProofIds and cases must be arrays',
      {
        caseProofIds: typeof judgment.caseProofIds,
        cases: typeof judgment.cases,
      },
    );
  }
  if (judgment.caseProofIds.length !== judgment.cardinality
      || judgment.cases.length !== judgment.cardinality) {
    return validationReject0(
      path,
      'FiniteExhaust conclusion must contain exactly one case per domain element',
      {
        cardinality: judgment.cardinality,
        caseProofCount: judgment.caseProofIds.length,
        caseCount: judgment.cases.length,
      },
    );
  }
  const proofIds = new Set();
  for (let index = 0; index < judgment.caseProofIds.length; index += 1) {
    const proofId = judgment.caseProofIds[index];
    if (!isIdentifier0(proofId)) {
      return validationReject0(
        [...path, 'caseProofIds', index],
        'FiniteExhaust case proof id must be a canonical identifier',
        { actual: proofId },
      );
    }
    if (proofIds.has(proofId)) {
      return validationReject0(
        [...path, 'caseProofIds', index],
        'FiniteExhaust case proof ids must be unique',
        { proofId },
      );
    }
    proofIds.add(proofId);

    const caseResult = judgment.cases[index];
    if (!isPlainObject0(caseResult)) {
      return validationReject0(
        [...path, 'cases', index],
        'FiniteExhaust case result must be an object',
        { actual: typeof caseResult },
      );
    }
    const allowedCaseKeys = new Set(['kind', 'index', 'element', 'instance']);
    const unexpectedCaseKeys = Object.keys(caseResult)
      .filter((key) => !allowedCaseKeys.has(key));
    if (unexpectedCaseKeys.length !== 0) {
      return validationReject0(
        [...path, 'cases', index, unexpectedCaseKeys[0]],
        'FiniteExhaust case result rejects undeclared fields',
        { unexpectedFields: unexpectedCaseKeys.sort() },
      );
    }
    if (caseResult.kind !== 'SemanticFiniteExhaustCaseResult0'
        || caseResult.index !== index
        || !isPlainObject0(caseResult.element)
        || !isPlainObject0(caseResult.instance)) {
      return validationReject0(
        [...path, 'cases', index],
        'FiniteExhaust case result shape is invalid',
        { actual: caseResult },
      );
    }
  }

  for (const field of [
    'canonicalEnumeration',
    'allElementsCovered',
    'noDuplicateElements',
    'noOmittedElements',
    'exactCardinality',
  ]) {
    if (judgment[field] !== true) {
      return validationReject0(
        [...path, field],
        `FiniteExhaust conclusion ${field} must be true`,
        { actual: judgment[field] },
      );
    }
  }

  return validationAccept0({
    kind: 'SemanticFiniteExhaustJudgmentShape0NF',
    domainId: judgment.domainId,
    cardinality: judgment.cardinality,
    caseCount: judgment.cases.length,
  });
}

function checkFiniteExhaustRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'FiniteExhaust rule supports only close',
      { actual: node.Payload.op },
    );
  }

  const domainCheck = validateDomain0(
    node.Payload.domain,
    [...path, 'Payload', 'domain'],
  );
  if (!domainCheck.ok) return domainCheck;
  const templateCheck = validateTemplate0(
    node.Payload.variable,
    node.Payload.body,
    domainCheck.domain,
    [...path, 'Payload', 'template'],
  );
  if (!templateCheck.ok) return templateCheck;

  const derived = deriveClosure0(
    domainCheck,
    node.Payload.variable,
    node.Payload.body,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;

  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'FiniteExhaust conclusion must exactly equal the computed universal closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticFiniteExhaustRule0NF',
    ruleName: 'FiniteExhaust',
    operation: 'close',
    domainId: domainCheck.domain.domainId,
    elementSort: domainCheck.domain.elementSort,
    cardinality: domainCheck.domain.cardinality,
    caseProofIds: [...node.Premises],
    canonicalEnumeration: true,
    allElementsCovered: true,
    noDuplicateElements: true,
    noOmittedElements: true,
    exactCardinality: true,
    universalConclusionComputed: true,
  });
}

function deriveClosure0(
  domainCheck,
  variable,
  body,
  premises,
  caseProofIds,
  path,
) {
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'FiniteExhaust closure requires premise and proof-id arrays',
      null,
    );
  }

  const elements = domainCheck.domain.elements;
  if (premises.length !== elements.length
      || caseProofIds.length !== elements.length) {
    return validationReject0(
      [...path, 'Premises'],
      'FiniteExhaust requires exactly one accepted local case for every domain element',
      {
        expected: elements.length,
        actualPremises: premises.length,
        actualProofIds: caseProofIds.length,
      },
    );
  }

  const cases = [];
  for (let index = 0; index < elements.length; index += 1) {
    const premise = premises[index];
    const element = elements[index];
    const casePath = [...path, 'Premises', index];

    if (!isPlainObject0(premise)) {
      return validationReject0(
        casePath,
        'FiniteExhaust case premise must resolve to an earlier accepted proof node',
        { actual: premise },
      );
    }

    if (premise.RuleName !== 'Record' || premise.operation !== 'intro') {
      return validationReject0(
        casePath,
        'FiniteExhaust case premise must be accepted Record.intro evidence',
        {
          actualRuleName: premise.RuleName,
          actualOperation: premise.operation,
        },
      );
    }

    const caseCheck = validateCaseRecord0(
      premise.Conclusion,
      domainCheck.domain,
      variable,
      body,
      index,
      element,
      casePath,
    );
    if (!caseCheck.ok) return caseCheck;

    cases.push(Object.freeze({
      kind: 'SemanticFiniteExhaustCaseResult0',
      index,
      element,
      instance: caseCheck.instance,
    }));
  }

  const judgment = makeSemanticFiniteExhaustJudgment0({
    domainId: domainCheck.domain.domainId,
    elementSort: domainCheck.domain.elementSort,
    variable,
    body,
    elements,
    caseProofIds,
    cases,
  });

  return validationAcceptWith0({
    kind: 'SemanticFiniteExhaustClosure0NF',
    domainId: domainCheck.domain.domainId,
    cardinality: elements.length,
    coveredIndices: elements.map((_element, index) => index),
    noOmittedElements: true,
  }, {
    judgment,
  });
}

function validateCaseRecord0(
  record,
  domain,
  variable,
  body,
  index,
  element,
  path,
) {
  if (!isPlainObject0(record)) {
    return validationReject0(
      path,
      'FiniteExhaust case conclusion must be a record judgment',
      { actual: typeof record },
    );
  }

  const allowedRecordKeys = new Set(['kind', 'version', 'recordType', 'fields']);
  const unexpectedRecordKeys = Object.keys(record)
    .filter((key) => !allowedRecordKeys.has(key));
  if (unexpectedRecordKeys.length !== 0) {
    return validationReject0(
      [...path, 'Conclusion', unexpectedRecordKeys[0]],
      'FiniteExhaust case record rejects undeclared fields',
      { unexpectedFields: unexpectedRecordKeys.sort() },
    );
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'Conclusion', 'kind'],
      'FiniteExhaust case conclusion must be SemanticRecordJudgment0',
      { actual: record.kind },
    );
  }
  if (record.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'Conclusion', 'version'],
      `FiniteExhaust case conclusion version must be ${CHECKER_VERSION}`,
      { actual: record.version },
    );
  }

  const expectedRecordType = caseRecordType0(domain.domainId, index);
  if (record.recordType !== expectedRecordType) {
    return validationReject0(
      [...path, 'Conclusion', 'recordType'],
      'FiniteExhaust case recordType must bind the domain and canonical element index',
      { expected: expectedRecordType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'FiniteExhaust case record fields must be an array',
      { actual: typeof record.fields },
    );
  }
  const names = record.fields.map((field) => field?.name ?? null);
  const expectedNames = ['element', 'instance'];
  if (!sameCanonical0(names, expectedNames)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'FiniteExhaust case fields must contain exact element and instance evidence',
      { expected: expectedNames, actual: names },
    );
  }

  for (let fieldIndex = 0; fieldIndex < record.fields.length; fieldIndex += 1) {
    const field = record.fields[fieldIndex];
    if (!isPlainObject0(field)
        || field.kind !== 'SemanticRecordField0'
        || !isPlainObject0(field.judgment)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields', fieldIndex],
        'FiniteExhaust case fields must contain semantic judgment objects',
        { actual: field },
      );
    }
  }

  const fieldMap = new Map(record.fields.map((field) => [field.name, field.judgment]));
  const expectedElementJudgment = makeSemanticEqJudgment0(element, element);
  if (!sameCanonical0(fieldMap.get('element'), expectedElementJudgment)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'FiniteExhaust case element evidence must exactly bind the enumerated element',
      {
        domainId: domain.domainId,
        index,
        expected: expectedElementJudgment,
        actual: fieldMap.get('element'),
      },
    );
  }

  let expectedInstance;
  try {
    expectedInstance = substituteSemanticJudgment0(body, variable, element);
  } catch (error) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'FiniteExhaust could not compute the exact per-element instance',
      {
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    );
  }
  const actualInstance = fieldMap.get('instance');
  if (!sameCanonical0(actualInstance, expectedInstance)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'FiniteExhaust case instance must exactly equal body substitution at the enumerated element',
      {
        domainId: domain.domainId,
        index,
        element,
        expected: expectedInstance,
        actual: actualInstance,
      },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticFiniteExhaustCase0NF',
    domainId: domain.domainId,
    index,
    elementDigest: digestCanonical0(element),
    instanceDigest: digestCanonical0(expectedInstance),
  }, {
    instance: expectedInstance,
  });
}

function caseRecordType0(domainId, index) {
  return `FiniteExhaustCase0.${domainId}.${index}`;
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProofTraceInd0(
      makeSemanticProofDAG0(baseNodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofTraceInd0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofTraceInd0 threw instead of returning a reject record',
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

function isText0(value) {
  return typeof value === 'string' && value.length > 0;
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

function requireText0(value, label) {
  if (!isText0(value)) {
    throw new TypeError(`${label} must be a nonempty string`);
  }
}
