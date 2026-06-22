import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofHall0,
  SEMANTIC_KERNEL_REQUIRED_RULES_HALL0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0,
} from './pcc-kernel-hall-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_RANK_ITEMS = 100_000;
const MAX_RANK_ARITY = 16;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

const INVARIANT_JUDGMENT_KINDS0 = Object.freeze([
  'SemanticEqJudgment0',
  'SemanticFormulaJudgment0',
  'SemanticRecordJudgment0',
]);

export const SEMANTIC_RANKIND_OPERATIONS0 = Object.freeze(['close']);
export const SEMANTIC_RANK_ITEM_KINDS0 = Object.freeze(['base', 'step']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_HALL0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0,
  'RankInd',
]);

export function makeSemanticRank0(coordinates = []) {
  if (!Array.isArray(coordinates)
      || coordinates.length === 0
      || coordinates.length > MAX_RANK_ARITY) {
    throw new TypeError(
      `makeSemanticRank0 coordinates must contain 1..${MAX_RANK_ARITY} entries`,
    );
  }
  for (const coordinate of coordinates) {
    if (!Number.isSafeInteger(coordinate) || coordinate < 0) {
      throw new TypeError(
        'makeSemanticRank0 coordinates must be nonnegative safe integers',
      );
    }
  }
  return Object.freeze({
    kind: 'SemanticRank0',
    version: CHECKER_VERSION,
    coordinates: Object.freeze([...coordinates]),
  });
}

export function makeSemanticRankItem0({
  index,
  id,
  rank,
  predecessorIds = [],
  invariant,
} = {}) {
  requireIndex0(index, 'makeSemanticRankItem0 index');
  requireIdentifier0(id, 'makeSemanticRankItem0 id');
  const rankCheck = validateRank0(rank, ['rank'], null);
  if (!rankCheck.ok) throw new TypeError(rankCheck.witness.reason);
  if (!Array.isArray(predecessorIds)) {
    throw new TypeError('makeSemanticRankItem0 predecessorIds must be an array');
  }
  const seen = new Set();
  for (const predecessorId of predecessorIds) {
    requireIdentifier0(
      predecessorId,
      'makeSemanticRankItem0 predecessor id',
    );
    if (seen.has(predecessorId)) {
      throw new TypeError(
        'makeSemanticRankItem0 predecessorIds must be unique',
      );
    }
    seen.add(predecessorId);
  }
  const invariantCheck = validateInvariantJudgment0(invariant, ['invariant']);
  if (!invariantCheck.ok) throw new TypeError(invariantCheck.witness.reason);

  return Object.freeze({
    kind: 'SemanticRankItem0',
    version: CHECKER_VERSION,
    itemKind: predecessorIds.length === 0 ? 'base' : 'step',
    index,
    id,
    rank,
    predecessorIds: Object.freeze([...predecessorIds]),
    invariant,
  });
}

export function makeSemanticRankProgram0({
  programId,
  rankArity,
  items = [],
  terminalItemId,
  terminalCoordinate,
} = {}) {
  requireIdentifier0(programId, 'makeSemanticRankProgram0 programId');
  if (!Number.isSafeInteger(rankArity)
      || rankArity < 1
      || rankArity > MAX_RANK_ARITY) {
    throw new TypeError(
      `makeSemanticRankProgram0 rankArity must be in 1..${MAX_RANK_ARITY}`,
    );
  }
  requireIdentifier0(
    terminalItemId,
    'makeSemanticRankProgram0 terminalItemId',
  );
  requireIdentifier0(
    terminalCoordinate,
    'makeSemanticRankProgram0 terminalCoordinate',
  );
  if (!Array.isArray(items) || items.length === 0) {
    throw new TypeError(
      'makeSemanticRankProgram0 items must be a nonempty array',
    );
  }

  const orderedItems = [...items].sort((left, right) => left.index - right.index);
  const program = Object.freeze({
    kind: 'SemanticRankProgram0',
    version: CHECKER_VERSION,
    programId,
    rankArity,
    items: Object.freeze(orderedItems),
    terminalItemId,
    terminalCoordinate,
  });
  const checked = validateProgram0(program, ['program']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return program;
}

export function makeSemanticRankIndCase0({
  programId,
  itemId,
  invariant,
  dependencyInvariants = [],
} = {}) {
  requireIdentifier0(programId, 'makeSemanticRankIndCase0 programId');
  requireIdentifier0(itemId, 'makeSemanticRankIndCase0 itemId');
  const invariantCheck = validateInvariantJudgment0(invariant, ['invariant']);
  if (!invariantCheck.ok) throw new TypeError(invariantCheck.witness.reason);
  if (!Array.isArray(dependencyInvariants)) {
    throw new TypeError(
      'makeSemanticRankIndCase0 dependencyInvariants must be an array',
    );
  }

  const fields = [
    makeSemanticRecordField0('invariant', invariant),
  ];
  const seen = new Set();
  for (const entry of dependencyInvariants) {
    if (!isPlainObject0(entry)) {
      throw new TypeError(
        'makeSemanticRankIndCase0 dependency entry must be an object',
      );
    }
    requireIdentifier0(
      entry.itemId,
      'makeSemanticRankIndCase0 dependency itemId',
    );
    if (seen.has(entry.itemId)) {
      throw new TypeError(
        'makeSemanticRankIndCase0 dependency itemIds must be unique',
      );
    }
    seen.add(entry.itemId);
    const dependencyCheck = validateInvariantJudgment0(
      entry.invariant,
      ['dependencyInvariants', entry.itemId],
    );
    if (!dependencyCheck.ok) {
      throw new TypeError(dependencyCheck.witness.reason);
    }
    fields.push(makeSemanticRecordField0(
      `dep.${entry.itemId}`,
      entry.invariant,
    ));
  }
  fields.sort((left, right) => compareText0(left.name, right.name));

  return makeSemanticRecordJudgment0(
    caseRecordType0(programId, itemId),
    fields,
  );
}

export function deriveSemanticRankIndJudgment0({
  program,
  caseRecords,
  caseProofIds,
} = {}) {
  const programCheck = validateProgram0(program, ['program']);
  if (!programCheck.ok) throw new TypeError(programCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError(
      'deriveSemanticRankIndJudgment0 requires caseRecords and caseProofIds arrays',
    );
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

export function CheckSemanticKernelReadinessRankInd0() {
  const checker = 'CheckSemanticKernelReadinessRankInd0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessRankInd0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofHall0',
    proofChecker: 'CheckSemanticKernelProofRankInd0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    rankIndOperations: [...SEMANTIC_RANKIND_OPERATIONS0],
    explicitFiniteRankedDomainRequired: true,
    fixedRankArityRequired: true,
    canonicalLexicographicEvaluationOrderRequired: true,
    zeroRankBasePrefixRequired: true,
    strictRankDecreaseRequired: true,
    acceptedLocalCaseEvidenceRequired: true,
    completeCaseCoverageRequired: true,
    allItemsContributeToTerminalRequired: true,
    terminalInvariantComputed: true,
    callerWellFoundednessAndCompletionAssertionsForbidden: true,
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
        reason: 'RankInd-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

export function CheckSemanticKernelProofRankInd0(input) {
  const checker = 'CheckSemanticKernelProofRankInd0';
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
        reason: 'RankInd-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofHall0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall sub-DAG rejected under the predecessor semantic checker',
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

    const semantic = node.RuleName === 'RankInd'
      ? checkRankIndRule0(node, premises, path)
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0.includes(rule),
  );
  const rankIndNodeCount = summaries.filter(
    (node) => node.RuleName === 'RankInd',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofRankInd0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofHall0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_RANKIND0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedRankIndOperations: [...SEMANTIC_RANKIND_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      rankIndNodeCount,
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
      { kind: 'SemanticRankIndProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticRankIndProofInput0NF', form: 'object', nodeCount: nodes.length },
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
        'RankInd-extended semantic proof node rejects undeclared fields',
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
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'RankInd-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'RankInd-extended semantic kernel accepts Full mode only',
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
    if (node.RuleName === 'RankInd') {
      const payload = validateRankIndPayload0(node.Payload, [...path, 'Payload']);
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
    kind: 'SemanticRankIndProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateRankIndPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'program']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'RankInd payload rejects caller-supplied well-foundedness, coverage, or terminal assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_RANKIND_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'RankInd operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_RANKIND_OPERATIONS0],
      },
    );
  }
  return validateProgram0(payload.program, [...path, 'program']);
}

function validateProgram0(program, path) {
  if (!isPlainObject0(program)) {
    return validationReject0(path, 'RankInd program must be an object', {
      actual: typeof program,
    });
  }
  const allowedProgramKeys = new Set([
    'kind', 'version', 'programId', 'rankArity',
    'items', 'terminalItemId', 'terminalCoordinate',
  ]);
  const unexpectedProgramKeys = Object.keys(program)
    .filter((key) => !allowedProgramKeys.has(key));
  if (unexpectedProgramKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedProgramKeys[0]],
      'RankInd program rejects undeclared well-foundedness, rank-complete, induction-complete, or terminal-ready assertions',
      { unexpectedFields: unexpectedProgramKeys.sort() },
    );
  }
  if (program.kind !== 'SemanticRankProgram0') {
    return validationReject0(
      [...path, 'kind'],
      'RankInd program kind must be SemanticRankProgram0',
      { actual: program.kind },
    );
  }
  if (program.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `RankInd program version must be ${CHECKER_VERSION}`,
      { actual: program.version },
    );
  }
  if (!isIdentifier0(program.programId)) {
    return validationReject0(
      [...path, 'programId'],
      'RankInd programId must be a canonical identifier',
      { actual: program.programId },
    );
  }
  if (!Number.isSafeInteger(program.rankArity)
      || program.rankArity < 1
      || program.rankArity > MAX_RANK_ARITY) {
    return validationReject0(
      [...path, 'rankArity'],
      `RankInd rankArity must be in 1..${MAX_RANK_ARITY}`,
      { actual: program.rankArity },
    );
  }
  if (!Array.isArray(program.items) || program.items.length === 0) {
    return validationReject0(
      [...path, 'items'],
      'RankInd program must contain a nonempty item array',
      { actual: typeof program.items },
    );
  }
  if (program.items.length > MAX_RANK_ITEMS) {
    return validationReject0(
      [...path, 'items'],
      'RankInd program exceeds maxItems',
      { maxItems: MAX_RANK_ITEMS, actual: program.items.length },
    );
  }
  if (!isIdentifier0(program.terminalItemId)) {
    return validationReject0(
      [...path, 'terminalItemId'],
      'RankInd terminalItemId must be a canonical identifier',
      { actual: program.terminalItemId },
    );
  }
  if (!isIdentifier0(program.terminalCoordinate)) {
    return validationReject0(
      [...path, 'terminalCoordinate'],
      'RankInd terminalCoordinate must be a canonical identifier',
      { actual: program.terminalCoordinate },
    );
  }

  const byId = new Map();
  const baseItemIds = [];
  const stepItemIds = [];
  let stepSeen = false;
  let previousItem = null;

  for (let index = 0; index < program.items.length; index += 1) {
    const item = program.items[index];
    const itemPath = [...path, 'items', index];
    if (!isPlainObject0(item)) {
      return validationReject0(itemPath, 'RankInd item must be an object', {
        actual: typeof item,
      });
    }
    const allowedItemKeys = new Set([
      'kind', 'version', 'itemKind', 'index', 'id',
      'rank', 'predecessorIds', 'invariant',
    ]);
    const unexpectedItemKeys = Object.keys(item)
      .filter((key) => !allowedItemKeys.has(key));
    if (unexpectedItemKeys.length !== 0) {
      return validationReject0(
        [...itemPath, unexpectedItemKeys[0]],
        'RankInd item rejects undeclared well-foundedness, completion, or terminal assertions',
        { unexpectedFields: unexpectedItemKeys.sort() },
      );
    }
    if (item.kind !== 'SemanticRankItem0') {
      return validationReject0(
        [...itemPath, 'kind'],
        'RankInd item kind must be SemanticRankItem0',
        { actual: item.kind },
      );
    }
    if (item.version !== CHECKER_VERSION) {
      return validationReject0(
        [...itemPath, 'version'],
        `RankInd item version must be ${CHECKER_VERSION}`,
        { actual: item.version },
      );
    }
    if (!SEMANTIC_RANK_ITEM_KINDS0.includes(item.itemKind)) {
      return validationReject0(
        [...itemPath, 'itemKind'],
        'RankInd itemKind must be base or step',
        { actual: item.itemKind },
      );
    }
    if (!Number.isSafeInteger(item.index) || item.index !== index) {
      return validationReject0(
        [...itemPath, 'index'],
        'RankInd item indices must be exact consecutive evaluation coordinates',
        { expected: index, actual: item.index },
      );
    }
    if (!isIdentifier0(item.id)) {
      return validationReject0(
        [...itemPath, 'id'],
        'RankInd item id must be a canonical identifier',
        { actual: item.id },
      );
    }
    if (byId.has(item.id)) {
      return validationReject0(
        [...itemPath, 'id'],
        'RankInd item ids must be unique',
        { id: item.id },
      );
    }
    const rankCheck = validateRank0(
      item.rank,
      [...itemPath, 'rank'],
      program.rankArity,
    );
    if (!rankCheck.ok) return rankCheck;
    if (previousItem !== null) {
      const rankComparison = compareRank0(previousItem.rank, item.rank);
      if (rankComparison > 0
          || (rankComparison === 0 && compareText0(previousItem.id, item.id) >= 0)) {
        return validationReject0(
          [...path, 'items'],
          'RankInd items must be in canonical lexicographic rank-then-id order',
          {
            previousItemId: previousItem.id,
            previousRank: previousItem.rank,
            itemId: item.id,
            rank: item.rank,
          },
        );
      }
    }
    previousItem = item;

    if (!Array.isArray(item.predecessorIds)) {
      return validationReject0(
        [...itemPath, 'predecessorIds'],
        'RankInd predecessorIds must be an array',
        { actual: typeof item.predecessorIds },
      );
    }
    const invariantCheck = validateInvariantJudgment0(
      item.invariant,
      [...itemPath, 'invariant'],
    );
    if (!invariantCheck.ok) return invariantCheck;

    const zeroRank = item.rank.coordinates.every((coordinate) => coordinate === 0);
    if (item.itemKind === 'base') {
      if (stepSeen) {
        return validationReject0(
          [...path, 'items'],
          'RankInd zero-rank base items must form one canonical prefix',
          { itemId: item.id, index },
        );
      }
      if (!zeroRank) {
        return validationReject0(
          [...itemPath, 'rank'],
          'RankInd base items must have the exact zero rank',
          { actual: item.rank },
        );
      }
      if (item.predecessorIds.length !== 0) {
        return validationReject0(
          [...itemPath, 'predecessorIds'],
          'RankInd base items must not declare predecessors',
          { actual: item.predecessorIds },
        );
      }
      baseItemIds.push(item.id);
    } else {
      stepSeen = true;
      if (zeroRank) {
        return validationReject0(
          [...itemPath, 'rank'],
          'RankInd step items must have a nonzero rank',
          { actual: item.rank },
        );
      }
      if (item.predecessorIds.length === 0) {
        return validationReject0(
          [...itemPath, 'predecessorIds'],
          'RankInd step items must declare at least one predecessor',
          { actual: item.predecessorIds },
        );
      }

      const predecessorIds = new Set();
      const predecessorItems = [];
      for (let predecessorIndex = 0;
        predecessorIndex < item.predecessorIds.length;
        predecessorIndex += 1) {
        const predecessorId = item.predecessorIds[predecessorIndex];
        if (!isIdentifier0(predecessorId)) {
          return validationReject0(
            [...itemPath, 'predecessorIds', predecessorIndex],
            'RankInd predecessor id must be a canonical identifier',
            { actual: predecessorId },
          );
        }
        if (predecessorIds.has(predecessorId)) {
          return validationReject0(
            [...itemPath, 'predecessorIds', predecessorIndex],
            'RankInd predecessor ids must be unique',
            { predecessorId },
          );
        }
        const predecessor = byId.get(predecessorId);
        if (predecessor === undefined) {
          return validationReject0(
            [...itemPath, 'predecessorIds', predecessorIndex],
            'RankInd predecessor must reference an earlier item',
            { itemId: item.id, predecessorId },
          );
        }
        if (compareRank0(predecessor.rank, item.rank) >= 0) {
          return validationReject0(
            [...itemPath, 'predecessorIds', predecessorIndex],
            'RankInd every predecessor rank must be strictly smaller than the item rank',
            {
              itemId: item.id,
              itemRank: item.rank,
              predecessorId,
              predecessorRank: predecessor.rank,
            },
          );
        }
        predecessorIds.add(predecessorId);
        predecessorItems.push(predecessor);
      }
      const expectedPredecessorIds = [...predecessorItems]
        .sort((left, right) => left.index - right.index)
        .map((predecessor) => predecessor.id);
      if (!sameCanonical0(item.predecessorIds, expectedPredecessorIds)) {
        return validationReject0(
          [...itemPath, 'predecessorIds'],
          'RankInd predecessors must be in canonical evaluation order',
          { expected: expectedPredecessorIds, actual: item.predecessorIds },
        );
      }
      stepItemIds.push(item.id);
    }

    byId.set(item.id, item);
  }

  if (baseItemIds.length === 0) {
    return validationReject0(
      [...path, 'items'],
      'RankInd program must contain at least one zero-rank base item',
      null,
    );
  }

  const terminalItem = byId.get(program.terminalItemId);
  if (terminalItem === undefined) {
    return validationReject0(
      [...path, 'terminalItemId'],
      'RankInd terminalItemId must name a declared item',
      { actual: program.terminalItemId },
    );
  }
  if (program.items.at(-1).id !== program.terminalItemId) {
    return validationReject0(
      [...path, 'terminalItemId'],
      'RankInd terminal item must be the final evaluation coordinate',
      {
        expected: program.items.at(-1).id,
        actual: program.terminalItemId,
      },
    );
  }

  const contributing = new Set();
  const stack = [program.terminalItemId];
  while (stack.length !== 0) {
    const itemId = stack.pop();
    if (contributing.has(itemId)) continue;
    contributing.add(itemId);
    const item = byId.get(itemId);
    for (const predecessorId of item.predecessorIds) stack.push(predecessorId);
  }
  if (contributing.size !== program.items.length) {
    const deadItemIds = program.items
      .map((item) => item.id)
      .filter((itemId) => !contributing.has(itemId));
    return validationReject0(
      [...path, 'items'],
      'RankInd every declared item must contribute to the terminal item',
      { deadItemIds },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticRankProgram0NF',
    programId: program.programId,
    rankArity: program.rankArity,
    itemCount: program.items.length,
    itemOrder: program.items.map((item) => item.id),
    baseItemIds,
    stepItemIds,
    terminalItemId: program.terminalItemId,
    terminalCoordinate: program.terminalCoordinate,
    canonicalRankOrder: true,
    zeroRankBasePrefix: true,
    strictRankDecrease: true,
    allItemsContributeToTerminal: true,
  }, {
    program,
    byId,
    baseItemIds,
    stepItemIds,
    terminalItem,
  });
}

function validateRank0(rank, path, expectedArity) {
  if (!isPlainObject0(rank)) {
    return validationReject0(path, 'RankInd rank must be an object', {
      actual: typeof rank,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'coordinates']);
  const unexpected = Object.keys(rank).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'RankInd rank rejects undeclared well-foundedness or comparison assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (rank.kind !== 'SemanticRank0') {
    return validationReject0(
      [...path, 'kind'],
      'RankInd rank kind must be SemanticRank0',
      { actual: rank.kind },
    );
  }
  if (rank.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `RankInd rank version must be ${CHECKER_VERSION}`,
      { actual: rank.version },
    );
  }
  if (!Array.isArray(rank.coordinates)
      || rank.coordinates.length === 0
      || rank.coordinates.length > MAX_RANK_ARITY) {
    return validationReject0(
      [...path, 'coordinates'],
      `RankInd rank coordinates must contain 1..${MAX_RANK_ARITY} entries`,
      { actual: rank.coordinates },
    );
  }
  if (expectedArity !== null && rank.coordinates.length !== expectedArity) {
    return validationReject0(
      [...path, 'coordinates'],
      'RankInd rank coordinate count must equal program rankArity',
      { expected: expectedArity, actual: rank.coordinates.length },
    );
  }
  for (let index = 0; index < rank.coordinates.length; index += 1) {
    const coordinate = rank.coordinates[index];
    if (!Number.isSafeInteger(coordinate) || coordinate < 0) {
      return validationReject0(
        [...path, 'coordinates', index],
        'RankInd rank coordinates must be nonnegative safe integers',
        { actual: coordinate },
      );
    }
  }
  return validationAccept0({
    kind: 'SemanticRank0NF',
    arity: rank.coordinates.length,
    coordinates: [...rank.coordinates],
  });
}

function validateInvariantJudgment0(invariant, path) {
  if (!isPlainObject0(invariant)) {
    return validationReject0(
      path,
      'RankInd invariant must be a semantic judgment object',
      { actual: typeof invariant },
    );
  }
  if (!INVARIANT_JUDGMENT_KINDS0.includes(invariant.kind)) {
    return validationReject0(
      [...path, 'kind'],
      'RankInd invariant must be an accepted equality, formula, or record judgment',
      {
        actual: invariant.kind,
        supportedKinds: [...INVARIANT_JUDGMENT_KINDS0],
      },
    );
  }
  return validationAccept0({
    kind: 'SemanticRankInvariant0NF',
    judgmentKind: invariant.kind,
    digest: digestCanonical0(invariant),
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'RankInd conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'programId', 'rankArity',
    'itemOrder', 'baseItemIds', 'stepItemIds',
    'itemCount', 'baseItemCount', 'stepItemCount',
    'rankAssignments', 'dependencyMap',
    'terminalItemId', 'terminalCoordinate', 'terminalInvariant',
    'terminalJudgment', 'caseProofIds', 'cases',
    'canonicalRankOrder', 'zeroRankBasePrefix',
    'strictRankDecrease', 'predecessorCoverageComplete',
    'localInvariantEvidenceExact', 'allItemsEvaluated',
    'allItemsContributeToTerminal', 'finiteLexicographicOrderWellFounded',
    'terminalInvariantComputed',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'RankInd conclusion rejects undeclared readiness, well-foundedness, or completion assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticRankIndJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'RankInd conclusion kind must be SemanticRankIndJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `RankInd conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  for (const field of [
    'itemOrder', 'baseItemIds', 'stepItemIds',
    'rankAssignments', 'dependencyMap', 'caseProofIds', 'cases',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `RankInd conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }
  return validationAccept0({
    kind: 'SemanticRankIndJudgmentShape0NF',
    programId: judgment.programId,
    itemCount: judgment.itemCount,
  });
}

function checkRankIndRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'RankInd rule supports only close',
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
      'RankInd conclusion must exactly equal the computed finite rank-induction closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticRankIndRule0NF',
    ruleName: 'RankInd',
    operation: 'close',
    programId: programCheck.program.programId,
    rankArity: programCheck.program.rankArity,
    itemCount: programCheck.program.items.length,
    baseItemCount: programCheck.baseItemIds.length,
    stepItemCount: programCheck.stepItemIds.length,
    terminalItemId: programCheck.program.terminalItemId,
    strictRankDecrease: true,
    completeCaseCoverage: true,
  });
}

function deriveClosure0(programCheck, premises, caseProofIds, path) {
  const { program, byId, baseItemIds, stepItemIds, terminalItem } = programCheck;
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'RankInd closure requires premise and case-proof arrays',
      null,
    );
  }
  if (premises.length !== program.items.length
      || caseProofIds.length !== program.items.length) {
    return validationReject0(
      [...path, 'Premises'],
      'RankInd requires exactly one local case for every ranked item',
      {
        expected: program.items.length,
        actualPremises: premises.length,
        actualCaseProofIds: caseProofIds.length,
      },
    );
  }

  const cases = [];
  for (let index = 0; index < program.items.length; index += 1) {
    const item = program.items[index];
    const premise = premises[index];
    if (!isPlainObject0(premise)
        || premise.RuleName !== 'Record'
        || premise.operation !== 'intro') {
      return validationReject0(
        [...path, 'Premises', index],
        'RankInd case premise must be accepted Record.intro evidence',
        {
          itemId: item.id,
          actualRule: premise?.RuleName ?? null,
          actualOperation: premise?.operation ?? null,
        },
      );
    }
    if (premise.id !== caseProofIds[index]) {
      return validationReject0(
        [...path, 'Premises', index],
        'RankInd case proof id must exactly match the supplied premise id',
        { expected: premise.id, actual: caseProofIds[index] },
      );
    }
    const expectedCase = makeSemanticRankIndCase0({
      programId: program.programId,
      itemId: item.id,
      invariant: item.invariant,
      dependencyInvariants: item.predecessorIds.map((predecessorId) => ({
        itemId: predecessorId,
        invariant: byId.get(predecessorId).invariant,
      })),
    });
    if (premise.Conclusion?.recordType !== caseRecordType0(program.programId, item.id)) {
      return validationReject0(
        [...path, 'Premises', index, 'Conclusion', 'recordType'],
        'RankInd case recordType must bind the program and item id',
        {
          expected: caseRecordType0(program.programId, item.id),
          actual: premise.Conclusion?.recordType ?? null,
        },
      );
    }
    if (!sameCanonical0(premise.Conclusion, expectedCase)) {
      return validationReject0(
        [...path, 'Premises', index, 'Conclusion'],
        'RankInd case fields must contain the exact invariant and predecessor invariants',
        { itemId: item.id, expected: expectedCase, actual: premise.Conclusion },
      );
    }
    cases.push(premise.Conclusion);
  }

  const rankAssignments = program.items.map((item) => Object.freeze({
    itemId: item.id,
    rank: item.rank,
  }));
  const dependencyMap = program.items.map((item) => Object.freeze({
    itemId: item.id,
    predecessorIds: Object.freeze([...item.predecessorIds]),
  }));
  const terminalJudgment = Object.freeze({
    kind: 'SemanticRankResultJudgment0',
    version: CHECKER_VERSION,
    programId: program.programId,
    itemId: terminalItem.id,
    coordinate: program.terminalCoordinate,
    invariant: terminalItem.invariant,
  });
  const judgment = Object.freeze({
    kind: 'SemanticRankIndJudgment0',
    version: CHECKER_VERSION,
    programId: program.programId,
    rankArity: program.rankArity,
    itemOrder: Object.freeze(program.items.map((item) => item.id)),
    baseItemIds: Object.freeze([...baseItemIds]),
    stepItemIds: Object.freeze([...stepItemIds]),
    itemCount: program.items.length,
    baseItemCount: baseItemIds.length,
    stepItemCount: stepItemIds.length,
    rankAssignments: Object.freeze(rankAssignments),
    dependencyMap: Object.freeze(dependencyMap),
    terminalItemId: terminalItem.id,
    terminalCoordinate: program.terminalCoordinate,
    terminalInvariant: terminalItem.invariant,
    terminalJudgment,
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    canonicalRankOrder: true,
    zeroRankBasePrefix: true,
    strictRankDecrease: true,
    predecessorCoverageComplete: true,
    localInvariantEvidenceExact: true,
    allItemsEvaluated: true,
    allItemsContributeToTerminal: true,
    finiteLexicographicOrderWellFounded: true,
    terminalInvariantComputed: true,
  });

  return validationAcceptWith0({
    kind: 'SemanticRankIndClosure0NF',
    programId: program.programId,
    itemCount: program.items.length,
    terminalItemId: terminalItem.id,
  }, { judgment });
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofHall0(makeSemanticProofDAG0(nodes));
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofHall0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofHall0 threw instead of returning a reject record',
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    };
  }
}

function caseRecordType0(programId, itemId) {
  return `RankIndCase0.${programId}.${itemId}`;
}

function compareRank0(left, right) {
  for (let index = 0; index < left.coordinates.length; index += 1) {
    if (left.coordinates[index] < right.coordinates[index]) return -1;
    if (left.coordinates[index] > right.coordinates[index]) return 1;
  }
  return 0;
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
