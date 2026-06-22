import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofRankInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0,
} from './pcc-kernel-rankind-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_CANDIDATES = 100_000;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;
const JUDGMENT_KIND_PATTERN = /^Semantic[A-Za-z0-9]+Judgment0$/;

export const SEMANTIC_MINCOUNTEREXAMPLE_OPERATIONS0 = Object.freeze([
  'select',
]);

export const SEMANTIC_MINCOUNTEREXAMPLE_EVIDENCE_STATUSES0 = Object.freeze([
  'holds',
  'fails',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0,
  'MinCounterexample',
]);

export function makeSemanticMinCandidate0({
  index,
  id,
  orderKey,
  holdsJudgment,
  failsJudgment,
} = {}) {
  requireIndex0(index, 'makeSemanticMinCandidate0 index');
  requireIdentifier0(id, 'makeSemanticMinCandidate0 id');
  if (!Number.isSafeInteger(orderKey) || orderKey < 0) {
    throw new TypeError(
      'makeSemanticMinCandidate0 orderKey must be a nonnegative safe integer',
    );
  }
  const holds = validateEvidenceJudgment0(
    holdsJudgment,
    ['holdsJudgment'],
  );
  if (!holds.ok) throw new TypeError(holds.witness.reason);
  const fails = validateEvidenceJudgment0(
    failsJudgment,
    ['failsJudgment'],
  );
  if (!fails.ok) throw new TypeError(fails.witness.reason);
  if (sameCanonical0(holdsJudgment, failsJudgment)) {
    throw new TypeError(
      'makeSemanticMinCandidate0 holds and fails judgments must be distinct',
    );
  }

  return Object.freeze({
    kind: 'SemanticMinCandidate0',
    version: CHECKER_VERSION,
    index,
    id,
    orderKey,
    holdsJudgment,
    failsJudgment,
  });
}

export function makeSemanticMinCounterexampleSearch0({
  searchId,
  candidates = [],
  terminalCoordinate,
} = {}) {
  requireIdentifier0(
    searchId,
    'makeSemanticMinCounterexampleSearch0 searchId',
  );
  requireIdentifier0(
    terminalCoordinate,
    'makeSemanticMinCounterexampleSearch0 terminalCoordinate',
  );
  if (!Array.isArray(candidates) || candidates.length === 0) {
    throw new TypeError(
      'makeSemanticMinCounterexampleSearch0 candidates must be a nonempty array',
    );
  }

  const orderedCandidates = [...candidates]
    .sort((left, right) => left.index - right.index);
  const search = Object.freeze({
    kind: 'SemanticMinCounterexampleSearch0',
    version: CHECKER_VERSION,
    searchId,
    candidates: Object.freeze(orderedCandidates),
    terminalCoordinate,
  });
  const checked = validateSearch0(search, ['search']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return search;
}

export function makeSemanticMinCounterexampleEvidence0({
  searchId,
  candidateId,
  status,
  judgment,
} = {}) {
  requireIdentifier0(
    searchId,
    'makeSemanticMinCounterexampleEvidence0 searchId',
  );
  requireIdentifier0(
    candidateId,
    'makeSemanticMinCounterexampleEvidence0 candidateId',
  );
  if (!SEMANTIC_MINCOUNTEREXAMPLE_EVIDENCE_STATUSES0.includes(status)) {
    throw new TypeError(
      'makeSemanticMinCounterexampleEvidence0 status must be holds or fails',
    );
  }
  const judgmentCheck = validateEvidenceJudgment0(judgment, ['judgment']);
  if (!judgmentCheck.ok) {
    throw new TypeError(judgmentCheck.witness.reason);
  }

  return makeSemanticRecordJudgment0(
    evidenceRecordType0(searchId, candidateId, status),
    [makeSemanticRecordField0(status, judgment)],
  );
}

export function deriveSemanticMinCounterexampleJudgment0({
  search,
  evidenceRecords,
  evidenceProofIds,
} = {}) {
  const searchCheck = validateSearch0(search, ['search']);
  if (!searchCheck.ok) throw new TypeError(searchCheck.witness.reason);
  if (!Array.isArray(evidenceRecords) || !Array.isArray(evidenceProofIds)) {
    throw new TypeError(
      'deriveSemanticMinCounterexampleJudgment0 requires evidenceRecords and evidenceProofIds arrays',
    );
  }

  const derived = deriveSelection0(
    searchCheck,
    evidenceRecords.map((Conclusion, index) => ({
      id: evidenceProofIds[index],
      RuleName: 'Record',
      operation: 'intro',
      Conclusion,
    })),
    evidenceProofIds,
    ['derive'],
  );
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.judgment;
}

export function CheckSemanticKernelReadinessMinCounterexample0() {
  const checker = 'CheckSemanticKernelReadinessMinCounterexample0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessMinCounterexample0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofRankInd0',
    proofChecker: 'CheckSemanticKernelProofMinCounterexample0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    minCounterexampleOperations: [...SEMANTIC_MINCOUNTEREXAMPLE_OPERATIONS0],
    explicitFiniteCandidateDomainRequired: true,
    canonicalCandidateOrderRequired: true,
    acceptedEarlierHoldEvidenceRequired: true,
    acceptedSelectedFailureEvidenceRequired: true,
    firstFailureComputedFromEvidencePrefix: true,
    terminalMinimalCounterexampleJudgmentComputed: true,
    callerMinimalityAndSelectionAssertionsForbidden: true,
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
        reason: 'MinCounterexample-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

export function CheckSemanticKernelProofMinCounterexample0(input) {
  const checker = 'CheckSemanticKernelProofMinCounterexample0';
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
        reason: 'MinCounterexample-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofRankInd0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd sub-DAG rejected under the predecessor semantic checker',
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

    const semantic = node.RuleName === 'MinCounterexample'
      ? checkMinCounterexampleRule0(node, premises, path)
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0.includes(rule),
  );
  const minCounterexampleNodeCount = summaries.filter(
    (node) => node.RuleName === 'MinCounterexample',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofMinCounterexample0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofRankInd0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_MINCOUNTEREXAMPLE0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedMinCounterexampleOperations: [
        ...SEMANTIC_MINCOUNTEREXAMPLE_OPERATIONS0,
      ],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      minCounterexampleNodeCount,
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
        kind: 'SemanticMinCounterexampleProofInput0NF',
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
      kind: 'SemanticMinCounterexampleProofInput0NF',
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
        'MinCounterexample-extended semantic proof node rejects undeclared fields',
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
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0.includes(
      node.RuleName,
    )) {
      return validationReject0(
        [...path, 'RuleName'],
        'MinCounterexample-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [
            ...SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0,
          ],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'MinCounterexample-extended semantic kernel accepts Full mode only',
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
    if (node.RuleName === 'MinCounterexample') {
      const payload = validateMinCounterexamplePayload0(
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
    kind: 'SemanticMinCounterexampleProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateMinCounterexamplePayload0(payload, path) {
  const allowedKeys = new Set(['op', 'search']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'MinCounterexample payload rejects caller-supplied selected candidate, minimality, completion, search, solver, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_MINCOUNTEREXAMPLE_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'MinCounterexample operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_MINCOUNTEREXAMPLE_OPERATIONS0],
      },
    );
  }
  return validateSearch0(payload.search, [...path, 'search']);
}

function validateSearch0(search, path) {
  if (!isPlainObject0(search)) {
    return validationReject0(path, 'MinCounterexample search must be an object', {
      actual: typeof search,
    });
  }
  const allowedSearchKeys = new Set([
    'kind', 'version', 'searchId', 'candidates', 'terminalCoordinate',
  ]);
  const unexpectedSearchKeys = Object.keys(search)
    .filter((key) => !allowedSearchKeys.has(key));
  if (unexpectedSearchKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedSearchKeys[0]],
      'MinCounterexample search rejects undeclared selected-candidate, least, minimal, complete, solver, search, or oracle assertions',
      { unexpectedFields: unexpectedSearchKeys.sort() },
    );
  }
  if (search.kind !== 'SemanticMinCounterexampleSearch0') {
    return validationReject0(
      [...path, 'kind'],
      'MinCounterexample search kind must be SemanticMinCounterexampleSearch0',
      { actual: search.kind },
    );
  }
  if (search.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `MinCounterexample search version must be ${CHECKER_VERSION}`,
      { actual: search.version },
    );
  }
  if (!isIdentifier0(search.searchId)) {
    return validationReject0(
      [...path, 'searchId'],
      'MinCounterexample searchId must be a canonical identifier',
      { actual: search.searchId },
    );
  }
  if (!isIdentifier0(search.terminalCoordinate)) {
    return validationReject0(
      [...path, 'terminalCoordinate'],
      'MinCounterexample terminalCoordinate must be a canonical identifier',
      { actual: search.terminalCoordinate },
    );
  }
  if (!Array.isArray(search.candidates) || search.candidates.length === 0) {
    return validationReject0(
      [...path, 'candidates'],
      'MinCounterexample search must contain a nonempty candidate array',
      { actual: typeof search.candidates },
    );
  }
  if (search.candidates.length > MAX_CANDIDATES) {
    return validationReject0(
      [...path, 'candidates'],
      'MinCounterexample search exceeds maxCandidates',
      {
        maxCandidates: MAX_CANDIDATES,
        actual: search.candidates.length,
      },
    );
  }

  const byId = new Map();
  let previous = null;
  for (let index = 0; index < search.candidates.length; index += 1) {
    const candidate = search.candidates[index];
    const candidatePath = [...path, 'candidates', index];
    if (!isPlainObject0(candidate)) {
      return validationReject0(
        candidatePath,
        'MinCounterexample candidate must be an object',
        { actual: typeof candidate },
      );
    }
    const allowedCandidateKeys = new Set([
      'kind', 'version', 'index', 'id', 'orderKey',
      'holdsJudgment', 'failsJudgment',
    ]);
    const unexpectedCandidateKeys = Object.keys(candidate)
      .filter((key) => !allowedCandidateKeys.has(key));
    if (unexpectedCandidateKeys.length !== 0) {
      return validationReject0(
        [...candidatePath, unexpectedCandidateKeys[0]],
        'MinCounterexample candidate rejects undeclared holds, fails, selected, least, minimal, complete, solver, search, or oracle assertions',
        { unexpectedFields: unexpectedCandidateKeys.sort() },
      );
    }
    if (candidate.kind !== 'SemanticMinCandidate0') {
      return validationReject0(
        [...candidatePath, 'kind'],
        'MinCounterexample candidate kind must be SemanticMinCandidate0',
        { actual: candidate.kind },
      );
    }
    if (candidate.version !== CHECKER_VERSION) {
      return validationReject0(
        [...candidatePath, 'version'],
        `MinCounterexample candidate version must be ${CHECKER_VERSION}`,
        { actual: candidate.version },
      );
    }
    if (!Number.isSafeInteger(candidate.index) || candidate.index !== index) {
      return validationReject0(
        [...candidatePath, 'index'],
        'MinCounterexample candidate indices must be exact consecutive evaluation coordinates',
        { expected: index, actual: candidate.index },
      );
    }
    if (!isIdentifier0(candidate.id)) {
      return validationReject0(
        [...candidatePath, 'id'],
        'MinCounterexample candidate id must be a canonical identifier',
        { actual: candidate.id },
      );
    }
    if (byId.has(candidate.id)) {
      return validationReject0(
        [...candidatePath, 'id'],
        'MinCounterexample candidate ids must be unique',
        { id: candidate.id },
      );
    }
    if (!Number.isSafeInteger(candidate.orderKey) || candidate.orderKey < 0) {
      return validationReject0(
        [...candidatePath, 'orderKey'],
        'MinCounterexample orderKey must be a nonnegative safe integer',
        { actual: candidate.orderKey },
      );
    }
    if (previous !== null
        && (previous.orderKey > candidate.orderKey
          || (previous.orderKey === candidate.orderKey
            && compareText0(previous.id, candidate.id) >= 0))) {
      return validationReject0(
        [...path, 'candidates'],
        'MinCounterexample candidates must be in canonical orderKey-then-id order',
        {
          previousCandidateId: previous.id,
          previousOrderKey: previous.orderKey,
          candidateId: candidate.id,
          orderKey: candidate.orderKey,
        },
      );
    }
    const holds = validateEvidenceJudgment0(
      candidate.holdsJudgment,
      [...candidatePath, 'holdsJudgment'],
    );
    if (!holds.ok) return holds;
    const fails = validateEvidenceJudgment0(
      candidate.failsJudgment,
      [...candidatePath, 'failsJudgment'],
    );
    if (!fails.ok) return fails;
    if (sameCanonical0(candidate.holdsJudgment, candidate.failsJudgment)) {
      return validationReject0(
        candidatePath,
        'MinCounterexample holds and fails judgments must be distinct',
        { candidateId: candidate.id },
      );
    }

    byId.set(candidate.id, candidate);
    previous = candidate;
  }

  return validationAcceptWith0({
    kind: 'SemanticMinCounterexampleSearch0NF',
    searchId: search.searchId,
    candidateCount: search.candidates.length,
    candidateOrder: search.candidates.map((candidate) => candidate.id),
    orderKeys: search.candidates.map((candidate) => candidate.orderKey),
    terminalCoordinate: search.terminalCoordinate,
    explicitFiniteCandidateDomain: true,
    canonicalCandidateOrder: true,
  }, {
    search,
    byId,
  });
}

function validateEvidenceJudgment0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(
      path,
      'MinCounterexample evidence must be a semantic judgment object',
      { actual: typeof judgment },
    );
  }
  if (typeof judgment.kind !== 'string'
      || !JUDGMENT_KIND_PATTERN.test(judgment.kind)
      || judgment.kind === 'SemanticMinCounterexampleJudgment0'
      || judgment.kind === 'SemanticMinimalCounterexampleResultJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'MinCounterexample evidence must be a predecessor semantic judgment',
      { actual: judgment.kind },
    );
  }
  return validationAccept0({
    kind: 'SemanticMinCounterexampleEvidenceJudgment0NF',
    judgmentKind: judgment.kind,
    digest: digestCanonical0(judgment),
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(
      path,
      'MinCounterexample conclusion must be an object',
      { actual: typeof judgment },
    );
  }
  const allowedKeys = new Set([
    'kind', 'version', 'searchId', 'candidateOrder', 'orderKeys',
    'candidateCount', 'selectedCandidateId', 'selectedCandidateIndex',
    'selectedOrderKey', 'terminalCoordinate', 'earlierCandidateIds',
    'holdsEvidenceProofIds', 'failureEvidenceProofId', 'evidenceProofIds',
    'evidenceRecords', 'terminalJudgment', 'explicitFiniteCandidateDomain',
    'canonicalCandidateOrder', 'earlierCandidatesSatisfy',
    'selectedCandidateFails', 'leastFailureComputed',
    'evidencePrefixComplete', 'noSearchSolverOrOracleUsed',
    'terminalJudgmentComputed',
  ]);
  const unexpected = Object.keys(judgment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'MinCounterexample conclusion rejects undeclared readiness, minimality, search, solver, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticMinCounterexampleJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'MinCounterexample conclusion kind must be SemanticMinCounterexampleJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `MinCounterexample conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  for (const field of [
    'candidateOrder', 'orderKeys', 'earlierCandidateIds',
    'holdsEvidenceProofIds', 'evidenceProofIds', 'evidenceRecords',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `MinCounterexample conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }
  return validationAccept0({
    kind: 'SemanticMinCounterexampleJudgmentShape0NF',
    searchId: judgment.searchId,
    selectedCandidateId: judgment.selectedCandidateId,
  });
}

function checkMinCounterexampleRule0(node, premises, path) {
  if (node.Payload.op !== 'select') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'MinCounterexample rule supports only select',
      { actual: node.Payload.op },
    );
  }
  const searchCheck = validateSearch0(
    node.Payload.search,
    [...path, 'Payload', 'search'],
  );
  if (!searchCheck.ok) return searchCheck;
  const derived = deriveSelection0(
    searchCheck,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;
  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'MinCounterexample conclusion must exactly equal the computed least-failing-candidate decision',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticMinCounterexampleRule0NF',
    ruleName: 'MinCounterexample',
    operation: 'select',
    searchId: searchCheck.search.searchId,
    candidateCount: searchCheck.search.candidates.length,
    selectedCandidateId: derived.selectedCandidate.id,
    selectedCandidateIndex: derived.selectedCandidate.index,
    earlierCandidateCount: derived.selectedCandidate.index,
    canonicalCandidateOrder: true,
    leastFailureComputed: true,
  });
}

function deriveSelection0(searchCheck, premises, evidenceProofIds, path) {
  const { search } = searchCheck;
  if (!Array.isArray(premises) || !Array.isArray(evidenceProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'MinCounterexample selection requires premise and evidence-proof arrays',
      null,
    );
  }
  if (premises.length === 0) {
    return validationReject0(
      [...path, 'Premises'],
      'MinCounterexample requires accepted evidence through the first failing candidate',
      { actual: 0 },
    );
  }
  if (premises.length !== evidenceProofIds.length
      || premises.length > search.candidates.length) {
    return validationReject0(
      [...path, 'Premises'],
      'MinCounterexample evidence prefix must be nonempty and no longer than the candidate domain',
      {
        candidateCount: search.candidates.length,
        actualPremises: premises.length,
        actualEvidenceProofIds: evidenceProofIds.length,
      },
    );
  }

  const evidenceRecords = [];
  const holdsEvidenceProofIds = [];
  let selectedCandidate = null;
  let failureEvidenceProofId = null;

  for (let index = 0; index < premises.length; index += 1) {
    const candidate = search.candidates[index];
    const premise = premises[index];
    if (!isPlainObject0(premise)
        || premise.RuleName !== 'Record'
        || premise.operation !== 'intro') {
      return validationReject0(
        [...path, 'Premises', index],
        'MinCounterexample evidence premise must be accepted Record.intro evidence',
        {
          candidateId: candidate.id,
          actualRule: premise?.RuleName ?? null,
          actualOperation: premise?.operation ?? null,
        },
      );
    }
    if (premise.id !== evidenceProofIds[index]) {
      return validationReject0(
        [...path, 'Premises', index],
        'MinCounterexample evidence proof id must exactly match the supplied premise id',
        { expected: premise.id, actual: evidenceProofIds[index] },
      );
    }

    const expectedHolds = makeSemanticMinCounterexampleEvidence0({
      searchId: search.searchId,
      candidateId: candidate.id,
      status: 'holds',
      judgment: candidate.holdsJudgment,
    });
    const expectedFails = makeSemanticMinCounterexampleEvidence0({
      searchId: search.searchId,
      candidateId: candidate.id,
      status: 'fails',
      judgment: candidate.failsJudgment,
    });

    if (sameCanonical0(premise.Conclusion, expectedHolds)) {
      if (index === search.candidates.length - 1
          && premises.length === search.candidates.length) {
        return validationReject0(
          [...path, 'Premises', index, 'Conclusion'],
          'MinCounterexample candidate domain contains no accepted failing candidate',
          { candidateCount: search.candidates.length },
        );
      }
      evidenceRecords.push(premise.Conclusion);
      holdsEvidenceProofIds.push(premise.id);
      continue;
    }

    if (sameCanonical0(premise.Conclusion, expectedFails)) {
      if (index !== premises.length - 1) {
        return validationReject0(
          [...path, 'Premises', index],
          'MinCounterexample failure evidence must be the terminal evidence premise',
          {
            candidateId: candidate.id,
            failureIndex: index,
            evidenceCount: premises.length,
          },
        );
      }
      selectedCandidate = candidate;
      failureEvidenceProofId = premise.id;
      evidenceRecords.push(premise.Conclusion);
      break;
    }

    return validationReject0(
      [...path, 'Premises', index, 'Conclusion'],
      'MinCounterexample evidence must contain the exact candidate hold or failure judgment',
      {
        candidateId: candidate.id,
        expectedHolds,
        expectedFails,
        actual: premise.Conclusion,
      },
    );
  }

  if (selectedCandidate === null) {
    return validationReject0(
      [...path, 'Premises'],
      'MinCounterexample evidence prefix must terminate at an accepted failing candidate',
      {
        evidenceCount: premises.length,
        candidateCount: search.candidates.length,
      },
    );
  }

  const earlierCandidateIds = search.candidates
    .slice(0, selectedCandidate.index)
    .map((candidate) => candidate.id);
  const terminalJudgment = Object.freeze({
    kind: 'SemanticMinimalCounterexampleResultJudgment0',
    version: CHECKER_VERSION,
    searchId: search.searchId,
    candidateId: selectedCandidate.id,
    candidateIndex: selectedCandidate.index,
    orderKey: selectedCandidate.orderKey,
    coordinate: search.terminalCoordinate,
    failureJudgment: selectedCandidate.failsJudgment,
  });
  const judgment = Object.freeze({
    kind: 'SemanticMinCounterexampleJudgment0',
    version: CHECKER_VERSION,
    searchId: search.searchId,
    candidateOrder: Object.freeze(
      search.candidates.map((candidate) => candidate.id),
    ),
    orderKeys: Object.freeze(
      search.candidates.map((candidate) => candidate.orderKey),
    ),
    candidateCount: search.candidates.length,
    selectedCandidateId: selectedCandidate.id,
    selectedCandidateIndex: selectedCandidate.index,
    selectedOrderKey: selectedCandidate.orderKey,
    terminalCoordinate: search.terminalCoordinate,
    earlierCandidateIds: Object.freeze(earlierCandidateIds),
    holdsEvidenceProofIds: Object.freeze([...holdsEvidenceProofIds]),
    failureEvidenceProofId,
    evidenceProofIds: Object.freeze([...evidenceProofIds]),
    evidenceRecords: Object.freeze([...evidenceRecords]),
    terminalJudgment,
    explicitFiniteCandidateDomain: true,
    canonicalCandidateOrder: true,
    earlierCandidatesSatisfy: true,
    selectedCandidateFails: true,
    leastFailureComputed: true,
    evidencePrefixComplete: true,
    noSearchSolverOrOracleUsed: true,
    terminalJudgmentComputed: true,
  });

  return validationAcceptWith0({
    kind: 'SemanticMinCounterexampleSelection0NF',
    searchId: search.searchId,
    selectedCandidateId: selectedCandidate.id,
    selectedCandidateIndex: selectedCandidate.index,
    earlierCandidateCount: earlierCandidateIds.length,
  }, {
    judgment,
    selectedCandidate,
  });
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofRankInd0(
      makeSemanticProofDAG0(nodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofRankInd0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofRankInd0 threw instead of returning a reject record',
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    };
  }
}

function evidenceRecordType0(searchId, candidateId, status) {
  return `MinCounterexampleEvidence0.${searchId}.${candidateId}.${status}`;
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
