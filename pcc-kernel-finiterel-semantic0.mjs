import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofTruthVec0,
  SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0,
} from './pcc-kernel-truthvec-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_DOMAINS = 32;
const MAX_DOMAIN_ELEMENTS = 64;
const MAX_RELATION_ARITY = 4;
const MAX_RELATION_NODES = 1_024;
const MAX_RELATION_TUPLES = 262_144;
const MAX_TOTAL_RELATION_CELLS = 4_194_304;
const MAX_CLAIMS = 4_096;
const MAX_COMPOSITION_WORK = 4_194_304;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_FINITEREL_OPERATIONS0 = Object.freeze(['verify']);

export const SEMANTIC_FINITEREL_NODE_OPERATIONS0 = Object.freeze([
  'literal',
  'identity',
  'converse',
  'compose',
  'restrict',
  'union',
  'intersection',
  'difference',
  'transitive-closure',
  'reflexive-transitive-closure',
]);

export const SEMANTIC_FINITEREL_CLAIM_KINDS0 = Object.freeze([
  'equal',
  'included',
  'reflexive',
  'transitive',
  'reflexive-transitive-closed',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_FINITEREL0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_TRUTHVEC0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0,
  'FiniteRel',
]);

export function makeSemanticFiniteRelDomain0({
  index,
  id,
  elements = [],
} = {}) {
  requireIndex0(index, 'makeSemanticFiniteRelDomain0 index');
  requireIdentifier0(id, 'makeSemanticFiniteRelDomain0 id');
  if (!Array.isArray(elements)) {
    throw new TypeError('makeSemanticFiniteRelDomain0 elements must be an array');
  }
  for (const element of elements) {
    requireIdentifier0(element, 'makeSemanticFiniteRelDomain0 element');
  }
  const domain = Object.freeze({
    kind: 'SemanticFiniteRelDomain0',
    version: CHECKER_VERSION,
    index,
    id,
    elements: Object.freeze([...elements]),
  });
  const checked = validateDomain0(domain, ['domain']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return domain;
}

export function makeSemanticFiniteRelTuple0({
  index,
  values = [],
} = {}) {
  requireIndex0(index, 'makeSemanticFiniteRelTuple0 index');
  if (!Array.isArray(values)) {
    throw new TypeError('makeSemanticFiniteRelTuple0 values must be an array');
  }
  for (const value of values) {
    requireIdentifier0(value, 'makeSemanticFiniteRelTuple0 value');
  }
  return Object.freeze({
    kind: 'SemanticFiniteRelTuple0',
    version: CHECKER_VERSION,
    index,
    values: Object.freeze([...values]),
  });
}

export function makeSemanticFiniteRelRestriction0({
  index,
  domainId,
  allowedElements = [],
} = {}) {
  requireIndex0(index, 'makeSemanticFiniteRelRestriction0 index');
  requireIdentifier0(domainId, 'makeSemanticFiniteRelRestriction0 domainId');
  if (!Array.isArray(allowedElements)) {
    throw new TypeError(
      'makeSemanticFiniteRelRestriction0 allowedElements must be an array',
    );
  }
  for (const element of allowedElements) {
    requireIdentifier0(element, 'makeSemanticFiniteRelRestriction0 element');
  }
  return Object.freeze({
    kind: 'SemanticFiniteRelRestriction0',
    version: CHECKER_VERSION,
    index,
    domainId,
    allowedElements: Object.freeze([...allowedElements]),
  });
}

export function makeSemanticFiniteRelNode0({
  index,
  id,
  op,
  domainIds = [],
  inputIds = [],
  tuples = [],
  restrictions = [],
} = {}) {
  requireIndex0(index, 'makeSemanticFiniteRelNode0 index');
  requireIdentifier0(id, 'makeSemanticFiniteRelNode0 id');
  if (!SEMANTIC_FINITEREL_NODE_OPERATIONS0.includes(op)) {
    throw new TypeError(
      `makeSemanticFiniteRelNode0 op must be one of ${SEMANTIC_FINITEREL_NODE_OPERATIONS0.join(', ')}`,
    );
  }
  for (const [name, value] of Object.entries({
    domainIds,
    inputIds,
    tuples,
    restrictions,
  })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticFiniteRelNode0 ${name} must be an array`);
    }
  }
  for (const domainId of domainIds) {
    requireIdentifier0(domainId, 'makeSemanticFiniteRelNode0 domainId');
  }
  for (const inputId of inputIds) {
    requireIdentifier0(inputId, 'makeSemanticFiniteRelNode0 inputId');
  }
  return Object.freeze({
    kind: 'SemanticFiniteRelNode0',
    version: CHECKER_VERSION,
    index,
    id,
    op,
    domainIds: Object.freeze([...domainIds]),
    inputIds: Object.freeze([...inputIds]),
    tuples: Object.freeze([...tuples]),
    restrictions: Object.freeze([...restrictions]),
  });
}

export function makeSemanticFiniteRelClaim0({
  index,
  id,
  claimKind,
  leftId,
  rightId = null,
} = {}) {
  requireIndex0(index, 'makeSemanticFiniteRelClaim0 index');
  requireIdentifier0(id, 'makeSemanticFiniteRelClaim0 id');
  if (!SEMANTIC_FINITEREL_CLAIM_KINDS0.includes(claimKind)) {
    throw new TypeError(
      `makeSemanticFiniteRelClaim0 claimKind must be one of ${SEMANTIC_FINITEREL_CLAIM_KINDS0.join(', ')}`,
    );
  }
  requireIdentifier0(leftId, 'makeSemanticFiniteRelClaim0 leftId');
  if (!(rightId === null || isIdentifier0(rightId))) {
    throw new TypeError(
      'makeSemanticFiniteRelClaim0 rightId must be null or a canonical identifier',
    );
  }
  return Object.freeze({
    kind: 'SemanticFiniteRelClaim0',
    version: CHECKER_VERSION,
    index,
    id,
    claimKind,
    leftId,
    rightId,
  });
}

export function makeSemanticFiniteRelProgram0({
  programId,
  domains = [],
  nodes = [],
  claims = [],
} = {}) {
  requireIdentifier0(programId, 'makeSemanticFiniteRelProgram0 programId');
  for (const [name, value] of Object.entries({ domains, nodes, claims })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticFiniteRelProgram0 ${name} must be an array`);
    }
  }
  const program = Object.freeze({
    kind: 'SemanticFiniteRelProgram0',
    version: CHECKER_VERSION,
    programId,
    domains: Object.freeze([...domains]),
    nodes: Object.freeze([...nodes]),
    claims: Object.freeze([...claims]),
  });
  const checked = validateProgram0(program, ['program']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return program;
}

export function makeSemanticFiniteRelSpec0({
  evaluationId,
  program,
} = {}) {
  requireIdentifier0(evaluationId, 'makeSemanticFiniteRelSpec0 evaluationId');
  const spec = Object.freeze({
    kind: 'SemanticFiniteRelSpec0',
    version: CHECKER_VERSION,
    evaluationId,
    program,
  });
  const checked = validateSpec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return spec;
}

export function deriveSemanticFiniteRelJudgment0({
  spec,
} = {}) {
  const specCheck = validateSpec0(spec, ['spec']);
  if (!specCheck.ok) throw new TypeError(specCheck.witness.reason);
  const derived = deriveFiniteRelations0(specCheck, ['derive']);
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.judgment;
}

export function CheckSemanticKernelReadinessFiniteRel0() {
  const checker = 'CheckSemanticKernelReadinessFiniteRel0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_FINITEREL0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessFiniteRel0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofTruthVec0',
    proofChecker: 'CheckSemanticKernelProofFiniteRel0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_FINITEREL0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    relationOperations: [...SEMANTIC_FINITEREL_NODE_OPERATIONS0],
    relationClaimKinds: [...SEMANTIC_FINITEREL_CLAIM_KINDS0],
    explicitFiniteDomainsRequired: true,
    exactTupleArityRequired: true,
    exactCanonicalTupleOrderRequired: true,
    identityConverseCompositionRestrictionComputed: true,
    equalityInclusionAndClosureComputed: true,
    boundedEvaluationRequired: true,
    callerEqualityInclusionClosureAndCompletionAssertionsForbidden: true,
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
        reason: 'FiniteRel-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

export function CheckSemanticKernelProofFiniteRel0(input) {
  const checker = 'CheckSemanticKernelProofFiniteRel0';
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
        reason: 'FiniteRel-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0.includes(
      node.RuleName,
    ),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofTruthVec0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample/IntArith/Transport/TruthVec sub-DAG rejected under the predecessor semantic checker',
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
    const semantic = node.RuleName === 'FiniteRel'
      ? checkFiniteRelRule0(node, premises, path)
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_FINITEREL0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.includes(rule),
  );
  const finiteRelNodeCount = summaries.filter(
    (node) => node.RuleName === 'FiniteRel',
  ).length;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofFiniteRel0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofTruthVec0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_FINITEREL0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedFiniteRelOperations: [...SEMANTIC_FINITEREL_NODE_OPERATIONS0],
      supportedFiniteRelClaimKinds: [...SEMANTIC_FINITEREL_CLAIM_KINDS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      finiteRelNodeCount,
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
        kind: 'SemanticFiniteRelProofInput0NF',
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
      kind: 'SemanticFiniteRelProofInput0NF',
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
        'FiniteRel-extended semantic proof node rejects undeclared fields',
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
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'FiniteRel-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'FiniteRel-extended semantic kernel accepts Full proof-node mode only',
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
    if (node.RuleName === 'FiniteRel') {
      const payload = validateFiniteRelPayload0(
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
    kind: 'SemanticFiniteRelProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateFiniteRelPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'spec']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel payload rejects caller-supplied relations, equality, inclusion, closure, completeness, normalization, result, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_FINITEREL_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'FiniteRel operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_FINITEREL_OPERATIONS0],
      },
    );
  }
  const spec = validateSpec0(payload.spec, [...path, 'spec']);
  if (!spec.ok) return spec;
  return validationAccept0({
    kind: 'SemanticFiniteRelPayload0NF',
    operation: payload.op,
    evaluationId: spec.spec.evaluationId,
  });
}

function validateDomain0(domain, path) {
  if (!isPlainObject0(domain)) {
    return validationReject0(path, 'FiniteRel domain must be an object', {
      actual: typeof domain,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'index', 'id', 'elements']);
  const unexpected = Object.keys(domain).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel domain rejects undeclared equality, closure, result, solver, search, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (domain.kind !== 'SemanticFiniteRelDomain0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel domain kind must be SemanticFiniteRelDomain0',
      { actual: domain.kind },
    );
  }
  if (domain.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel domain version must be ${CHECKER_VERSION}`,
      { actual: domain.version },
    );
  }
  if (!Number.isSafeInteger(domain.index) || domain.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'FiniteRel domain index must be a nonnegative safe integer',
      { actual: domain.index },
    );
  }
  if (!isIdentifier0(domain.id)) {
    return validationReject0(
      [...path, 'id'],
      'FiniteRel domain id must be a canonical identifier',
      { actual: domain.id },
    );
  }
  if (!Array.isArray(domain.elements)
      || domain.elements.length > MAX_DOMAIN_ELEMENTS) {
    return validationReject0(
      [...path, 'elements'],
      'FiniteRel domain elements must be a bounded array',
      {
        maxDomainElements: MAX_DOMAIN_ELEMENTS,
        actual: Array.isArray(domain.elements)
          ? domain.elements.length
          : typeof domain.elements,
      },
    );
  }
  const elementIndex = new Map();
  for (let index = 0; index < domain.elements.length; index += 1) {
    const element = domain.elements[index];
    if (!isIdentifier0(element)) {
      return validationReject0(
        [...path, 'elements', index],
        'FiniteRel domain element must be a canonical identifier',
        { actual: element },
      );
    }
    if (elementIndex.has(element)) {
      return validationReject0(
        [...path, 'elements', index],
        'FiniteRel domain elements must be unique',
        { element },
      );
    }
    if (index > 0 && compareText0(domain.elements[index - 1], element) >= 0) {
      return validationReject0(
        [...path, 'elements', index],
        'FiniteRel domain elements must be in canonical order',
        { previous: domain.elements[index - 1], actual: element },
      );
    }
    elementIndex.set(element, index);
  }
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelDomain0NF',
    index: domain.index,
    id: domain.id,
    elementCount: domain.elements.length,
    elements: [...domain.elements],
  }, {
    domain,
    elementIndex,
  });
}

function validateTuple0(tuple, path, domainIds, domainById) {
  if (!isPlainObject0(tuple)) {
    return validationReject0(path, 'FiniteRel tuple must be an object', {
      actual: typeof tuple,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'index', 'values']);
  const unexpected = Object.keys(tuple).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel tuple rejects undeclared equality, result, or completion fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (tuple.kind !== 'SemanticFiniteRelTuple0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel tuple kind must be SemanticFiniteRelTuple0',
      { actual: tuple.kind },
    );
  }
  if (tuple.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel tuple version must be ${CHECKER_VERSION}`,
      { actual: tuple.version },
    );
  }
  if (!Number.isSafeInteger(tuple.index) || tuple.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'FiniteRel tuple index must be a nonnegative safe integer',
      { actual: tuple.index },
    );
  }
  if (!Array.isArray(tuple.values)
      || tuple.values.length !== domainIds.length) {
    return validationReject0(
      [...path, 'values'],
      'FiniteRel tuple values must exactly match the relation arity',
      {
        expectedArity: domainIds.length,
        actual: Array.isArray(tuple.values)
          ? tuple.values.length
          : typeof tuple.values,
      },
    );
  }
  for (let index = 0; index < tuple.values.length; index += 1) {
    const value = tuple.values[index];
    const domain = domainById.get(domainIds[index]);
    if (!isIdentifier0(value) || !domain.elementIndex.has(value)) {
      return validationReject0(
        [...path, 'values', index],
        'FiniteRel tuple value must belong to the declared coordinate domain',
        { domainId: domainIds[index], actual: value },
      );
    }
  }
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelTuple0NF',
    index: tuple.index,
    values: [...tuple.values],
  }, { tuple });
}

function validateRestriction0(
  restriction,
  path,
  expectedIndex,
  expectedDomainId,
  domainById,
) {
  if (!isPlainObject0(restriction)) {
    return validationReject0(path, 'FiniteRel restriction must be an object', {
      actual: typeof restriction,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'index', 'domainId', 'allowedElements',
  ]);
  const unexpected = Object.keys(restriction)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel restriction rejects undeclared result, completeness, or closure fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (restriction.kind !== 'SemanticFiniteRelRestriction0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel restriction kind must be SemanticFiniteRelRestriction0',
      { actual: restriction.kind },
    );
  }
  if (restriction.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel restriction version must be ${CHECKER_VERSION}`,
      { actual: restriction.version },
    );
  }
  if (restriction.index !== expectedIndex) {
    return validationReject0(
      [...path, 'index'],
      'FiniteRel restriction indices must be exact relation coordinates',
      { expected: expectedIndex, actual: restriction.index },
    );
  }
  if (restriction.domainId !== expectedDomainId) {
    return validationReject0(
      [...path, 'domainId'],
      'FiniteRel restriction domainId must match the relation coordinate domain',
      { expected: expectedDomainId, actual: restriction.domainId },
    );
  }
  if (!Array.isArray(restriction.allowedElements)) {
    return validationReject0(
      [...path, 'allowedElements'],
      'FiniteRel restriction allowedElements must be an array',
      { actual: typeof restriction.allowedElements },
    );
  }
  const domain = domainById.get(expectedDomainId);
  let previousIndex = -1;
  for (let index = 0; index < restriction.allowedElements.length; index += 1) {
    const element = restriction.allowedElements[index];
    const elementIndex = domain.elementIndex.get(element);
    if (!isIdentifier0(element) || elementIndex === undefined) {
      return validationReject0(
        [...path, 'allowedElements', index],
        'FiniteRel restricted element must belong to the coordinate domain',
        { domainId: expectedDomainId, actual: element },
      );
    }
    if (elementIndex <= previousIndex) {
      return validationReject0(
        [...path, 'allowedElements', index],
        'FiniteRel restricted elements must be unique and in canonical domain order',
        { actual: restriction.allowedElements },
      );
    }
    previousIndex = elementIndex;
  }
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelRestriction0NF',
    index: expectedIndex,
    domainId: expectedDomainId,
    allowedElements: [...restriction.allowedElements],
  }, { restriction });
}

function validateRelationNode0(node, path, nodeById, domainById) {
  if (!isPlainObject0(node)) {
    return validationReject0(path, 'FiniteRel relation node must be an object', {
      actual: typeof node,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'index', 'id', 'op',
    'domainIds', 'inputIds', 'tuples', 'restrictions',
  ]);
  const unexpected = Object.keys(node).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel relation node rejects caller-supplied relation results, equality, inclusion, closure, completeness, solver, search, optimization, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (node.kind !== 'SemanticFiniteRelNode0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel relation node kind must be SemanticFiniteRelNode0',
      { actual: node.kind },
    );
  }
  if (node.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel relation node version must be ${CHECKER_VERSION}`,
      { actual: node.version },
    );
  }
  if (!Number.isSafeInteger(node.index) || node.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'FiniteRel relation node index must be a nonnegative safe integer',
      { actual: node.index },
    );
  }
  if (!isIdentifier0(node.id)) {
    return validationReject0(
      [...path, 'id'],
      'FiniteRel relation node id must be a canonical identifier',
      { actual: node.id },
    );
  }
  if (nodeById.has(node.id)) {
    return validationReject0(
      [...path, 'id'],
      'FiniteRel relation node ids must be unique',
      { id: node.id },
    );
  }
  if (!SEMANTIC_FINITEREL_NODE_OPERATIONS0.includes(node.op)) {
    return validationReject0(
      [...path, 'op'],
      'FiniteRel relation-node operation is unsupported',
      {
        actual: node.op,
        supportedOperations: [...SEMANTIC_FINITEREL_NODE_OPERATIONS0],
      },
    );
  }
  if (!Array.isArray(node.domainIds)
      || node.domainIds.length === 0
      || node.domainIds.length > MAX_RELATION_ARITY) {
    return validationReject0(
      [...path, 'domainIds'],
      'FiniteRel relation node domainIds must define a nonempty bounded arity',
      {
        maxArity: MAX_RELATION_ARITY,
        actual: Array.isArray(node.domainIds)
          ? node.domainIds.length
          : typeof node.domainIds,
      },
    );
  }
  for (let index = 0; index < node.domainIds.length; index += 1) {
    const domainId = node.domainIds[index];
    if (!isIdentifier0(domainId) || !domainById.has(domainId)) {
      return validationReject0(
        [...path, 'domainIds', index],
        'FiniteRel relation coordinate must reference a declared finite domain',
        { actual: domainId },
      );
    }
  }
  if (!Array.isArray(node.inputIds)) {
    return validationReject0(
      [...path, 'inputIds'],
      'FiniteRel relation node inputIds must be an array',
      { actual: typeof node.inputIds },
    );
  }
  const inputNodes = [];
  for (let index = 0; index < node.inputIds.length; index += 1) {
    const inputId = node.inputIds[index];
    if (!isIdentifier0(inputId) || !nodeById.has(inputId)) {
      return validationReject0(
        [...path, 'inputIds', index],
        'FiniteRel relation input must reference an earlier relation node',
        { actual: inputId },
      );
    }
    inputNodes.push(nodeById.get(inputId));
  }
  if (!Array.isArray(node.tuples)) {
    return validationReject0(
      [...path, 'tuples'],
      'FiniteRel relation node tuples must be an array',
      { actual: typeof node.tuples },
    );
  }
  if (!Array.isArray(node.restrictions)) {
    return validationReject0(
      [...path, 'restrictions'],
      'FiniteRel relation node restrictions must be an array',
      { actual: typeof node.restrictions },
    );
  }

  const noStoredResult = () => {
    if (node.tuples.length !== 0) {
      return validationReject0(
        [...path, 'tuples'],
        'FiniteRel computed relation nodes cannot contain caller-supplied result tuples',
        { actualTupleCount: node.tuples.length },
      );
    }
    return null;
  };
  const noRestrictions = () => {
    if (node.restrictions.length !== 0) {
      return validationReject0(
        [...path, 'restrictions'],
        'FiniteRel operation does not accept coordinate restrictions',
        { actualRestrictionCount: node.restrictions.length },
      );
    }
    return null;
  };
  const requireInputs = (count) => {
    if (inputNodes.length !== count) {
      return validationReject0(
        [...path, 'inputIds'],
        `FiniteRel ${node.op} requires exactly ${count} relation input${count === 1 ? '' : 's'}`,
        { expected: count, actual: inputNodes.length },
      );
    }
    return null;
  };

  if (node.op === 'literal') {
    const inputError = requireInputs(0);
    if (inputError) return inputError;
    const restrictionError = noRestrictions();
    if (restrictionError) return restrictionError;
    if (node.tuples.length > MAX_RELATION_TUPLES) {
      return validationReject0(
        [...path, 'tuples'],
        'FiniteRel literal relation exceeds maxRelationTuples',
        { maxRelationTuples: MAX_RELATION_TUPLES, actual: node.tuples.length },
      );
    }
    let previousValues = null;
    for (let index = 0; index < node.tuples.length; index += 1) {
      const tupleCheck = validateTuple0(
        node.tuples[index],
        [...path, 'tuples', index],
        node.domainIds,
        domainById,
      );
      if (!tupleCheck.ok) return tupleCheck;
      if (tupleCheck.tuple.index !== index) {
        return validationReject0(
          [...path, 'tuples', index, 'index'],
          'FiniteRel tuple indices must be exact consecutive relation coordinates',
          { expected: index, actual: tupleCheck.tuple.index },
        );
      }
      if (previousValues !== null
          && compareTupleValues0(
            previousValues,
            tupleCheck.tuple.values,
            node.domainIds,
            domainById,
          ) >= 0) {
        return validationReject0(
          [...path, 'tuples', index, 'values'],
          'FiniteRel literal tuples must be unique and in canonical domain order',
          { previous: previousValues, actual: tupleCheck.tuple.values },
        );
      }
      previousValues = tupleCheck.tuple.values;
    }
  } else if (node.op === 'identity') {
    const inputError = requireInputs(0);
    if (inputError) return inputError;
    const tupleError = noStoredResult();
    if (tupleError) return tupleError;
    const restrictionError = noRestrictions();
    if (restrictionError) return restrictionError;
    if (node.domainIds.length !== 2 || node.domainIds[0] !== node.domainIds[1]) {
      return validationReject0(
        [...path, 'domainIds'],
        'FiniteRel identity requires a binary endorelation signature',
        { actual: node.domainIds },
      );
    }
  } else if (node.op === 'converse') {
    const inputError = requireInputs(1);
    if (inputError) return inputError;
    const tupleError = noStoredResult();
    if (tupleError) return tupleError;
    const restrictionError = noRestrictions();
    if (restrictionError) return restrictionError;
    if (inputNodes[0].domainIds.length !== 2
        || !sameCanonical0(
          node.domainIds,
          [inputNodes[0].domainIds[1], inputNodes[0].domainIds[0]],
        )) {
      return validationReject0(
        [...path, 'domainIds'],
        'FiniteRel converse requires the exact reversed binary signature',
        { inputSignature: inputNodes[0].domainIds, actual: node.domainIds },
      );
    }
  } else if (node.op === 'compose') {
    const inputError = requireInputs(2);
    if (inputError) return inputError;
    const tupleError = noStoredResult();
    if (tupleError) return tupleError;
    const restrictionError = noRestrictions();
    if (restrictionError) return restrictionError;
    const left = inputNodes[0];
    const right = inputNodes[1];
    if (left.domainIds.length !== 2 || right.domainIds.length !== 2) {
      return validationReject0(
        [...path, 'inputIds'],
        'FiniteRel composition requires two binary relations',
        { leftSignature: left.domainIds, rightSignature: right.domainIds },
      );
    }
    if (left.domainIds[1] !== right.domainIds[0]) {
      return validationReject0(
        [...path, 'inputIds'],
        'FiniteRel composition middle domains must match exactly',
        { leftCodomain: left.domainIds[1], rightDomain: right.domainIds[0] },
      );
    }
    const expected = [left.domainIds[0], right.domainIds[1]];
    if (!sameCanonical0(node.domainIds, expected)) {
      return validationReject0(
        [...path, 'domainIds'],
        'FiniteRel composition result signature must be exact',
        { expected, actual: node.domainIds },
      );
    }
  } else if (node.op === 'restrict') {
    const inputError = requireInputs(1);
    if (inputError) return inputError;
    const tupleError = noStoredResult();
    if (tupleError) return tupleError;
    if (!sameCanonical0(node.domainIds, inputNodes[0].domainIds)) {
      return validationReject0(
        [...path, 'domainIds'],
        'FiniteRel restriction must preserve the input relation signature',
        { expected: inputNodes[0].domainIds, actual: node.domainIds },
      );
    }
    if (node.restrictions.length !== node.domainIds.length) {
      return validationReject0(
        [...path, 'restrictions'],
        'FiniteRel restriction must specify every relation coordinate exactly once',
        { expected: node.domainIds.length, actual: node.restrictions.length },
      );
    }
    for (let index = 0; index < node.restrictions.length; index += 1) {
      const restrictionCheck = validateRestriction0(
        node.restrictions[index],
        [...path, 'restrictions', index],
        index,
        node.domainIds[index],
        domainById,
      );
      if (!restrictionCheck.ok) return restrictionCheck;
    }
  } else if (['union', 'intersection', 'difference'].includes(node.op)) {
    const inputError = requireInputs(2);
    if (inputError) return inputError;
    const tupleError = noStoredResult();
    if (tupleError) return tupleError;
    const restrictionError = noRestrictions();
    if (restrictionError) return restrictionError;
    if (!sameCanonical0(inputNodes[0].domainIds, inputNodes[1].domainIds)
        || !sameCanonical0(node.domainIds, inputNodes[0].domainIds)) {
      return validationReject0(
        [...path, 'domainIds'],
        `FiniteRel ${node.op} requires identical input and output signatures`,
        {
          left: inputNodes[0].domainIds,
          right: inputNodes[1].domainIds,
          actual: node.domainIds,
        },
      );
    }
  } else {
    const inputError = requireInputs(1);
    if (inputError) return inputError;
    const tupleError = noStoredResult();
    if (tupleError) return tupleError;
    const restrictionError = noRestrictions();
    if (restrictionError) return restrictionError;
    const input = inputNodes[0];
    if (input.domainIds.length !== 2
        || input.domainIds[0] !== input.domainIds[1]
        || !sameCanonical0(node.domainIds, input.domainIds)) {
      return validationReject0(
        [...path, 'domainIds'],
        'FiniteRel closure requires a binary endorelation and preserves its signature',
        { inputSignature: input.domainIds, actual: node.domainIds },
      );
    }
  }

  const universeSize = relationUniverseSize0(node.domainIds, domainById);
  if (universeSize > MAX_RELATION_TUPLES) {
    return validationReject0(
      [...path, 'domainIds'],
      'FiniteRel relation universe exceeds maxRelationTuples',
      { maxRelationTuples: MAX_RELATION_TUPLES, actual: universeSize },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticFiniteRelNode0NF',
    index: node.index,
    id: node.id,
    op: node.op,
    domainIds: [...node.domainIds],
    inputIds: [...node.inputIds],
    universeSize,
  }, {
    node,
    domainIds: [...node.domainIds],
    inputNodes,
    universeSize,
  });
}

function validateClaim0(claim, path, nodeById) {
  if (!isPlainObject0(claim)) {
    return validationReject0(path, 'FiniteRel claim must be an object', {
      actual: typeof claim,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'index', 'id', 'claimKind', 'leftId', 'rightId',
  ]);
  const unexpected = Object.keys(claim).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel claim rejects caller-supplied truth, witness, equality, inclusion, closure, completeness, solver, search, optimization, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (claim.kind !== 'SemanticFiniteRelClaim0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel claim kind must be SemanticFiniteRelClaim0',
      { actual: claim.kind },
    );
  }
  if (claim.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel claim version must be ${CHECKER_VERSION}`,
      { actual: claim.version },
    );
  }
  if (!Number.isSafeInteger(claim.index) || claim.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'FiniteRel claim index must be a nonnegative safe integer',
      { actual: claim.index },
    );
  }
  if (!isIdentifier0(claim.id)) {
    return validationReject0(
      [...path, 'id'],
      'FiniteRel claim id must be a canonical identifier',
      { actual: claim.id },
    );
  }
  if (!SEMANTIC_FINITEREL_CLAIM_KINDS0.includes(claim.claimKind)) {
    return validationReject0(
      [...path, 'claimKind'],
      'FiniteRel claim kind is unsupported',
      {
        actual: claim.claimKind,
        supportedClaimKinds: [...SEMANTIC_FINITEREL_CLAIM_KINDS0],
      },
    );
  }
  if (!isIdentifier0(claim.leftId) || !nodeById.has(claim.leftId)) {
    return validationReject0(
      [...path, 'leftId'],
      'FiniteRel claim leftId must reference a declared relation node',
      { actual: claim.leftId },
    );
  }
  const left = nodeById.get(claim.leftId);
  if (['equal', 'included'].includes(claim.claimKind)) {
    if (!isIdentifier0(claim.rightId) || !nodeById.has(claim.rightId)) {
      return validationReject0(
        [...path, 'rightId'],
        'FiniteRel binary claim rightId must reference a declared relation node',
        { actual: claim.rightId },
      );
    }
    const right = nodeById.get(claim.rightId);
    if (!sameCanonical0(left.domainIds, right.domainIds)) {
      return validationReject0(
        [...path, 'rightId'],
        'FiniteRel equality and inclusion claims require identical relation signatures',
        { left: left.domainIds, right: right.domainIds },
      );
    }
  } else {
    if (claim.rightId !== null) {
      return validationReject0(
        [...path, 'rightId'],
        'FiniteRel unary closure claim rightId must be null',
        { actual: claim.rightId },
      );
    }
    if (left.domainIds.length !== 2 || left.domainIds[0] !== left.domainIds[1]) {
      return validationReject0(
        [...path, 'leftId'],
        'FiniteRel reflexive and transitive claims require a binary endorelation',
        { actualSignature: left.domainIds },
      );
    }
  }
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelClaim0NF',
    index: claim.index,
    id: claim.id,
    claimKind: claim.claimKind,
    leftId: claim.leftId,
    rightId: claim.rightId,
  }, { claim });
}

function validateProgram0(program, path) {
  if (!isPlainObject0(program)) {
    return validationReject0(path, 'FiniteRel program must be an object', {
      actual: typeof program,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'programId', 'domains', 'nodes', 'claims',
  ]);
  const unexpected = Object.keys(program).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel program rejects caller-supplied relation results, equality, inclusion, closure, completeness, normalization, solver, search, optimization, or oracle fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (program.kind !== 'SemanticFiniteRelProgram0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel program kind must be SemanticFiniteRelProgram0',
      { actual: program.kind },
    );
  }
  if (program.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel program version must be ${CHECKER_VERSION}`,
      { actual: program.version },
    );
  }
  if (!isIdentifier0(program.programId)) {
    return validationReject0(
      [...path, 'programId'],
      'FiniteRel programId must be a canonical identifier',
      { actual: program.programId },
    );
  }
  if (!Array.isArray(program.domains)
      || program.domains.length === 0
      || program.domains.length > MAX_DOMAINS) {
    return validationReject0(
      [...path, 'domains'],
      'FiniteRel domains must be a nonempty bounded array',
      {
        maxDomains: MAX_DOMAINS,
        actual: Array.isArray(program.domains)
          ? program.domains.length
          : typeof program.domains,
      },
    );
  }
  if (!Array.isArray(program.nodes)
      || program.nodes.length === 0
      || program.nodes.length > MAX_RELATION_NODES) {
    return validationReject0(
      [...path, 'nodes'],
      'FiniteRel relation nodes must be a nonempty bounded array',
      {
        maxRelationNodes: MAX_RELATION_NODES,
        actual: Array.isArray(program.nodes)
          ? program.nodes.length
          : typeof program.nodes,
      },
    );
  }
  if (!Array.isArray(program.claims)
      || program.claims.length === 0
      || program.claims.length > MAX_CLAIMS) {
    return validationReject0(
      [...path, 'claims'],
      'FiniteRel claims must be a nonempty bounded array',
      {
        maxClaims: MAX_CLAIMS,
        actual: Array.isArray(program.claims)
          ? program.claims.length
          : typeof program.claims,
      },
    );
  }

  const domainById = new Map();
  for (let index = 0; index < program.domains.length; index += 1) {
    const domainCheck = validateDomain0(
      program.domains[index],
      [...path, 'domains', index],
    );
    if (!domainCheck.ok) return domainCheck;
    if (domainCheck.domain.index !== index) {
      return validationReject0(
        [...path, 'domains', index, 'index'],
        'FiniteRel domain indices must be exact consecutive coordinates',
        { expected: index, actual: domainCheck.domain.index },
      );
    }
    if (domainById.has(domainCheck.domain.id)) {
      return validationReject0(
        [...path, 'domains', index, 'id'],
        'FiniteRel domain ids must be unique',
        { id: domainCheck.domain.id },
      );
    }
    domainById.set(domainCheck.domain.id, domainCheck);
  }

  const nodeById = new Map();
  let totalUniverseCells = 0;
  for (let index = 0; index < program.nodes.length; index += 1) {
    const nodeCheck = validateRelationNode0(
      program.nodes[index],
      [...path, 'nodes', index],
      nodeById,
      domainById,
    );
    if (!nodeCheck.ok) return nodeCheck;
    if (nodeCheck.node.index !== index) {
      return validationReject0(
        [...path, 'nodes', index, 'index'],
        'FiniteRel relation-node indices must be exact consecutive coordinates',
        { expected: index, actual: nodeCheck.node.index },
      );
    }
    totalUniverseCells += nodeCheck.universeSize;
    if (totalUniverseCells > MAX_TOTAL_RELATION_CELLS) {
      return validationReject0(
        [...path, 'nodes', index],
        'FiniteRel total relation universe exceeds maxTotalRelationCells',
        {
          maxTotalRelationCells: MAX_TOTAL_RELATION_CELLS,
          actual: totalUniverseCells,
        },
      );
    }
    nodeById.set(nodeCheck.node.id, nodeCheck);
  }

  const seenClaimIds = new Set();
  for (let index = 0; index < program.claims.length; index += 1) {
    const claimCheck = validateClaim0(
      program.claims[index],
      [...path, 'claims', index],
      nodeById,
    );
    if (!claimCheck.ok) return claimCheck;
    if (claimCheck.claim.index !== index) {
      return validationReject0(
        [...path, 'claims', index, 'index'],
        'FiniteRel claim indices must be exact consecutive coordinates',
        { expected: index, actual: claimCheck.claim.index },
      );
    }
    if (seenClaimIds.has(claimCheck.claim.id)) {
      return validationReject0(
        [...path, 'claims', index, 'id'],
        'FiniteRel claim ids must be unique',
        { id: claimCheck.claim.id },
      );
    }
    seenClaimIds.add(claimCheck.claim.id);
  }

  return validationAcceptWith0({
    kind: 'SemanticFiniteRelProgram0NF',
    programId: program.programId,
    domainCount: program.domains.length,
    relationNodeCount: program.nodes.length,
    claimCount: program.claims.length,
    domainIds: program.domains.map((domain) => domain.id),
    relationNodeIds: program.nodes.map((node) => node.id),
    claimIds: program.claims.map((claim) => claim.id),
    totalUniverseCells,
    boundedFiniteEvaluation: true,
  }, {
    program,
    domainById,
    nodeById,
  });
}

function validateSpec0(spec, path) {
  if (!isPlainObject0(spec)) {
    return validationReject0(path, 'FiniteRel specification must be an object', {
      actual: typeof spec,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'evaluationId', 'program']);
  const unexpected = Object.keys(spec).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel specification rejects caller-supplied relations, equality, inclusion, closure, completeness, normalization, result, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (spec.kind !== 'SemanticFiniteRelSpec0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel specification kind must be SemanticFiniteRelSpec0',
      { actual: spec.kind },
    );
  }
  if (spec.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel specification version must be ${CHECKER_VERSION}`,
      { actual: spec.version },
    );
  }
  if (!isIdentifier0(spec.evaluationId)) {
    return validationReject0(
      [...path, 'evaluationId'],
      'FiniteRel evaluationId must be a canonical identifier',
      { actual: spec.evaluationId },
    );
  }
  const program = validateProgram0(spec.program, [...path, 'program']);
  if (!program.ok) return program;
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelSpec0NF',
    evaluationId: spec.evaluationId,
    programId: program.program.programId,
    domainCount: program.nf.domainCount,
    relationNodeCount: program.nf.relationNodeCount,
    claimCount: program.nf.claimCount,
    totalUniverseCells: program.nf.totalUniverseCells,
    boundedFiniteEvaluation: true,
  }, {
    spec,
    program,
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'FiniteRel conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'evaluationId', 'program',
    'relations', 'claims', 'domainCount', 'relationNodeCount', 'claimCount',
    'programDigest', 'relationDigest', 'claimDigest',
    'canonicalFiniteDomains', 'exactTupleArity', 'exactTupleOrder',
    'everyRelationComputed', 'identityConverseCompositionRestrictionComputed',
    'equalityInclusionAndClosureComputed', 'allClaimsHold',
    'boundedEvaluation', 'noSolverSearchOptimizationOrOracleUsed',
    'terminalJudgmentComputed',
  ]);
  const unexpected = Object.keys(judgment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'FiniteRel conclusion rejects undeclared equality, inclusion, closure, completeness, normalization, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticFiniteRelJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'FiniteRel conclusion kind must be SemanticFiniteRelJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `FiniteRel conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  if (!Array.isArray(judgment.relations)) {
    return validationReject0(
      [...path, 'relations'],
      'FiniteRel conclusion relations must be an array',
      { actual: typeof judgment.relations },
    );
  }
  if (!Array.isArray(judgment.claims)) {
    return validationReject0(
      [...path, 'claims'],
      'FiniteRel conclusion claims must be an array',
      { actual: typeof judgment.claims },
    );
  }
  for (let index = 0; index < judgment.relations.length; index += 1) {
    const relation = judgment.relations[index];
    const relationPath = [...path, 'relations', index];
    if (!isPlainObject0(relation)) {
      return validationReject0(
        relationPath,
        'FiniteRel computed relation must be an object',
        { actual: typeof relation },
      );
    }
    const allowedRelationKeys = new Set([
      'kind', 'version', 'index', 'nodeId', 'domainIds', 'tuples',
    ]);
    const unexpectedRelation = Object.keys(relation)
      .filter((key) => !allowedRelationKeys.has(key));
    if (unexpectedRelation.length !== 0) {
      return validationReject0(
        [...relationPath, unexpectedRelation[0]],
        'FiniteRel computed relation rejects undeclared result or completion fields',
        { unexpectedFields: unexpectedRelation.sort() },
      );
    }
    if (relation.kind !== 'SemanticFiniteRelation0'
        || relation.version !== CHECKER_VERSION
        || relation.index !== index
        || !isIdentifier0(relation.nodeId)
        || !Array.isArray(relation.domainIds)
        || !Array.isArray(relation.tuples)) {
      return validationReject0(
        relationPath,
        'FiniteRel computed relation has invalid canonical fields',
        { actual: relation },
      );
    }
    for (let tupleIndex = 0; tupleIndex < relation.tuples.length; tupleIndex += 1) {
      const tuple = relation.tuples[tupleIndex];
      if (!isPlainObject0(tuple)
          || tuple.kind !== 'SemanticFiniteRelTuple0'
          || tuple.version !== CHECKER_VERSION
          || tuple.index !== tupleIndex
          || !Array.isArray(tuple.values)) {
        return validationReject0(
          [...relationPath, 'tuples', tupleIndex],
          'FiniteRel computed tuple has invalid canonical fields',
          { actual: tuple },
        );
      }
    }
  }
  for (let index = 0; index < judgment.claims.length; index += 1) {
    const claim = judgment.claims[index];
    const claimPath = [...path, 'claims', index];
    if (!isPlainObject0(claim)) {
      return validationReject0(
        claimPath,
        'FiniteRel computed claim must be an object',
        { actual: typeof claim },
      );
    }
    const allowedClaimKeys = new Set([
      'kind', 'version', 'index', 'id', 'claimKind',
      'leftId', 'rightId', 'holds', 'witness',
    ]);
    const unexpectedClaim = Object.keys(claim)
      .filter((key) => !allowedClaimKeys.has(key));
    if (unexpectedClaim.length !== 0) {
      return validationReject0(
        [...claimPath, unexpectedClaim[0]],
        'FiniteRel computed claim rejects undeclared truth or completion fields',
        { unexpectedFields: unexpectedClaim.sort() },
      );
    }
    if (claim.kind !== 'SemanticFiniteRelClaimResult0'
        || claim.version !== CHECKER_VERSION
        || claim.index !== index
        || !isIdentifier0(claim.id)
        || !SEMANTIC_FINITEREL_CLAIM_KINDS0.includes(claim.claimKind)
        || claim.holds !== true
        || claim.witness !== null) {
      return validationReject0(
        claimPath,
        'FiniteRel computed claim has invalid canonical fields',
        { actual: claim },
      );
    }
  }
  return validationAccept0({
    kind: 'SemanticFiniteRelJudgmentShape0NF',
    evaluationId: judgment.evaluationId,
    relationCount: judgment.relations.length,
    claimCount: judgment.claims.length,
  });
}

function checkFiniteRelRule0(node, premises, path) {
  if (node.Payload.op !== 'verify') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'FiniteRel rule supports only verify',
      { actual: node.Payload.op },
    );
  }
  if (premises.length !== 0 || node.Premises.length !== 0) {
    return validationReject0(
      [...path, 'Premises'],
      'FiniteRel verify is a closed exact finite computation and must not consume premises',
      { actualPremiseIds: node.Premises },
    );
  }
  const specCheck = validateSpec0(
    node.Payload.spec,
    [...path, 'Payload', 'spec'],
  );
  if (!specCheck.ok) return specCheck;
  const derived = deriveFiniteRelations0(specCheck, path);
  if (!derived.ok) return derived;
  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'FiniteRel conclusion must exactly equal the computed relation and claim ledger',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }
  return validationAccept0({
    kind: 'SemanticFiniteRelRule0NF',
    ruleName: 'FiniteRel',
    operation: 'verify',
    evaluationId: specCheck.spec.evaluationId,
    programId: specCheck.program.program.programId,
    relationNodeCount: specCheck.program.nf.relationNodeCount,
    claimCount: specCheck.program.nf.claimCount,
    totalUniverseCells: specCheck.program.nf.totalUniverseCells,
    everyRelationComputed: true,
    allClaimsHold: true,
  });
}

function deriveFiniteRelations0(specCheck, path) {
  const program = specCheck.program.program;
  const domainById = specCheck.program.domainById;
  const computedById = new Map();
  const relationResults = [];

  for (let index = 0; index < program.nodes.length; index += 1) {
    const node = program.nodes[index];
    const inputRelations = node.inputIds.map((id) => computedById.get(id));
    const evaluated = evaluateRelationNode0(
      node,
      inputRelations,
      domainById,
      [...path, 'program', 'nodes', index],
    );
    if (!evaluated.ok) return evaluated;
    computedById.set(node.id, evaluated.relation);
    relationResults.push(evaluated.relation.record);
  }

  const claimResults = [];
  for (let index = 0; index < program.claims.length; index += 1) {
    const claim = program.claims[index];
    const checked = evaluateClaim0(
      claim,
      computedById,
      [...path, 'program', 'claims', index],
    );
    if (!checked.ok) return checked;
    claimResults.push(checked.result);
  }

  const judgment = Object.freeze({
    kind: 'SemanticFiniteRelJudgment0',
    version: CHECKER_VERSION,
    evaluationId: specCheck.spec.evaluationId,
    program,
    relations: Object.freeze(relationResults),
    claims: Object.freeze(claimResults),
    domainCount: program.domains.length,
    relationNodeCount: program.nodes.length,
    claimCount: program.claims.length,
    programDigest: digestCanonical0(program),
    relationDigest: digestCanonical0(relationResults),
    claimDigest: digestCanonical0(claimResults),
    canonicalFiniteDomains: true,
    exactTupleArity: true,
    exactTupleOrder: true,
    everyRelationComputed: true,
    identityConverseCompositionRestrictionComputed: true,
    equalityInclusionAndClosureComputed: true,
    allClaimsHold: true,
    boundedEvaluation: true,
    noSolverSearchOptimizationOrOracleUsed: true,
    terminalJudgmentComputed: true,
  });
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelEvaluation0NF',
    evaluationId: specCheck.spec.evaluationId,
    programId: program.programId,
    relationNodeCount: relationResults.length,
    claimCount: claimResults.length,
  }, { judgment });
}

function evaluateRelationNode0(node, inputRelations, domainById, path) {
  let tuples;
  if (node.op === 'literal') {
    tuples = node.tuples.map((tuple) => [...tuple.values]);
  } else if (node.op === 'identity') {
    const domain = domainById.get(node.domainIds[0]).domain;
    tuples = domain.elements.map((element) => [element, element]);
  } else if (node.op === 'converse') {
    tuples = inputRelations[0].tuples.map((tuple) => [tuple[1], tuple[0]]);
  } else if (node.op === 'compose') {
    tuples = composeRelations0(inputRelations[0], inputRelations[1], path);
    if (!Array.isArray(tuples)) return tuples;
  } else if (node.op === 'restrict') {
    tuples = restrictRelation0(node, inputRelations[0]);
  } else if (node.op === 'union') {
    tuples = setUnion0(inputRelations[0].tuples, inputRelations[1].tuples);
  } else if (node.op === 'intersection') {
    tuples = setIntersection0(inputRelations[0].tuples, inputRelations[1].tuples);
  } else if (node.op === 'difference') {
    tuples = setDifference0(inputRelations[0].tuples, inputRelations[1].tuples);
  } else if (node.op === 'transitive-closure') {
    tuples = transitiveClosure0(node, inputRelations[0], domainById, false);
  } else if (node.op === 'reflexive-transitive-closure') {
    tuples = transitiveClosure0(node, inputRelations[0], domainById, true);
  } else {
    return validationReject0(
      [...path, 'op'],
      'FiniteRel relation-node operation is unsupported',
      { actual: node.op },
    );
  }
  if (tuples.length > MAX_RELATION_TUPLES) {
    return validationReject0(
      path,
      'FiniteRel computed relation exceeds maxRelationTuples',
      { maxRelationTuples: MAX_RELATION_TUPLES, actual: tuples.length },
    );
  }
  const relation = makeComputedRelation0(node, tuples, domainById);
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelComputedRelation0NF',
    nodeId: node.id,
    op: node.op,
    tupleCount: relation.record.tuples.length,
  }, { relation });
}

function composeRelations0(left, right, path) {
  const work = left.tuples.length * right.tuples.length;
  if (work > MAX_COMPOSITION_WORK) {
    return validationReject0(
      [...path, 'inputIds'],
      'FiniteRel composition work exceeds maxCompositionWork',
      { maxCompositionWork: MAX_COMPOSITION_WORK, actual: work },
    );
  }
  const tuples = [];
  for (const l of left.tuples) {
    for (const r of right.tuples) {
      if (l[1] === r[0]) tuples.push([l[0], r[1]]);
    }
  }
  return tuples;
}

function restrictRelation0(node, relation) {
  const allowedByCoordinate = node.restrictions.map(
    (restriction) => new Set(restriction.allowedElements),
  );
  return relation.tuples.filter((tuple) => tuple.every(
    (value, index) => allowedByCoordinate[index].has(value),
  ));
}

function transitiveClosure0(node, relation, domainById, reflexive) {
  const domain = domainById.get(node.domainIds[0]).domain;
  const indexByElement = new Map(
    domain.elements.map((element, index) => [element, index]),
  );
  const reach = Array.from(
    { length: domain.elements.length },
    () => Array(domain.elements.length).fill(false),
  );
  if (reflexive) {
    for (let index = 0; index < domain.elements.length; index += 1) {
      reach[index][index] = true;
    }
  }
  for (const [left, right] of relation.tuples) {
    reach[indexByElement.get(left)][indexByElement.get(right)] = true;
  }
  for (let k = 0; k < domain.elements.length; k += 1) {
    for (let i = 0; i < domain.elements.length; i += 1) {
      if (!reach[i][k]) continue;
      for (let j = 0; j < domain.elements.length; j += 1) {
        if (reach[k][j]) reach[i][j] = true;
      }
    }
  }
  const tuples = [];
  for (let i = 0; i < domain.elements.length; i += 1) {
    for (let j = 0; j < domain.elements.length; j += 1) {
      if (reach[i][j]) tuples.push([domain.elements[i], domain.elements[j]]);
    }
  }
  return tuples;
}

function evaluateClaim0(claim, computedById, path) {
  const left = computedById.get(claim.leftId);
  const right = claim.rightId === null ? null : computedById.get(claim.rightId);
  let holds;
  if (claim.claimKind === 'equal') {
    holds = sameSet0(left.tupleKeySet, right.tupleKeySet);
  } else if (claim.claimKind === 'included') {
    holds = subset0(left.tupleKeySet, right.tupleKeySet);
  } else if (claim.claimKind === 'reflexive') {
    holds = isReflexive0(left);
  } else if (claim.claimKind === 'transitive') {
    holds = isTransitive0(left);
  } else if (claim.claimKind === 'reflexive-transitive-closed') {
    holds = isReflexive0(left) && isTransitive0(left);
  } else {
    return validationReject0(
      [...path, 'claimKind'],
      'FiniteRel claim kind is unsupported',
      { actual: claim.claimKind },
    );
  }
  if (!holds) {
    return validationReject0(
      path,
      'FiniteRel checked claim does not hold',
      {
        claimId: claim.id,
        claimKind: claim.claimKind,
        leftId: claim.leftId,
        rightId: claim.rightId,
      },
    );
  }
  return validationAcceptWith0({
    kind: 'SemanticFiniteRelClaimResult0NF',
    claimId: claim.id,
    claimKind: claim.claimKind,
    holds: true,
  }, {
    result: Object.freeze({
      kind: 'SemanticFiniteRelClaimResult0',
      version: CHECKER_VERSION,
      index: claim.index,
      id: claim.id,
      claimKind: claim.claimKind,
      leftId: claim.leftId,
      rightId: claim.rightId,
      holds: true,
      witness: null,
    }),
  });
}

function makeComputedRelation0(node, tuples, domainById) {
  const sorted = canonicalTupleList0(tuples, node.domainIds, domainById);
  const tupleObjects = sorted.map((values, index) => Object.freeze({
    kind: 'SemanticFiniteRelTuple0',
    version: CHECKER_VERSION,
    index,
    values: Object.freeze([...values]),
  }));
  const tupleKeySet = new Set(sorted.map((tuple) => tupleKey0(tuple)));
  const record = Object.freeze({
    kind: 'SemanticFiniteRelation0',
    version: CHECKER_VERSION,
    index: node.index,
    nodeId: node.id,
    domainIds: Object.freeze([...node.domainIds]),
    tuples: Object.freeze(tupleObjects),
  });
  return Object.freeze({
    nodeId: node.id,
    op: node.op,
    domainIds: Object.freeze([...node.domainIds]),
    tuples: Object.freeze(sorted),
    tupleKeySet,
    record,
  });
}

function canonicalTupleList0(tuples, domainIds, domainById) {
  const byKey = new Map();
  for (const tuple of tuples) byKey.set(tupleKey0(tuple), [...tuple]);
  const unique = [...byKey.values()];
  unique.sort((left, right) => compareTupleValues0(
    left,
    right,
    domainIds,
    domainById,
  ));
  return unique;
}

function setUnion0(left, right) {
  const byKey = new Map();
  for (const tuple of left) byKey.set(tupleKey0(tuple), [...tuple]);
  for (const tuple of right) byKey.set(tupleKey0(tuple), [...tuple]);
  return [...byKey.values()];
}

function setIntersection0(left, right) {
  const rightSet = new Set(right.map((tuple) => tupleKey0(tuple)));
  return left.filter((tuple) => rightSet.has(tupleKey0(tuple)));
}

function setDifference0(left, right) {
  const rightSet = new Set(right.map((tuple) => tupleKey0(tuple)));
  return left.filter((tuple) => !rightSet.has(tupleKey0(tuple)));
}

function sameSet0(left, right) {
  if (left.size !== right.size) return false;
  return subset0(left, right);
}

function subset0(left, right) {
  for (const key of left) if (!right.has(key)) return false;
  return true;
}

function isReflexive0(relation) {
  const domainId = relation.domainIds[0];
  if (relation.domainIds.length !== 2 || relation.domainIds[1] !== domainId) return false;
  const values = new Set();
  for (const tuple of relation.tuples) {
    values.add(tuple[0]);
    values.add(tuple[1]);
  }
  for (const value of values) {
    if (!relation.tupleKeySet.has(tupleKey0([value, value]))) return false;
  }
  return true;
}

function isTransitive0(relation) {
  if (relation.domainIds.length !== 2
      || relation.domainIds[0] !== relation.domainIds[1]) return false;
  for (const left of relation.tuples) {
    for (const right of relation.tuples) {
      if (left[1] === right[0]
          && !relation.tupleKeySet.has(tupleKey0([left[0], right[1]]))) {
        return false;
      }
    }
  }
  return true;
}

function relationUniverseSize0(domainIds, domainById) {
  let size = 1;
  for (const domainId of domainIds) {
    size *= domainById.get(domainId).domain.elements.length;
  }
  return size;
}

function compareTupleValues0(left, right, domainIds, domainById) {
  for (let index = 0; index < domainIds.length; index += 1) {
    const domain = domainById.get(domainIds[index]);
    const leftIndex = domain.elementIndex.get(left[index]);
    const rightIndex = domain.elementIndex.get(right[index]);
    if (leftIndex < rightIndex) return -1;
    if (leftIndex > rightIndex) return 1;
  }
  return 0;
}

function tupleKey0(tuple) {
  return stableStringify0(tuple);
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofTruthVec0(
      makeSemanticProofDAG0(nodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofTruthVec0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofTruthVec0 threw instead of returning a reject record',
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
