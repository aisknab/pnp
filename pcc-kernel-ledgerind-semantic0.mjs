import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofDAGInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0,
} from './pcc-kernel-dagind-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_LEDGER_ENTRIES = 100_000;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_LEDGERIND_OPERATIONS0 = Object.freeze(['close']);

export const SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_DAGIND0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0,
  'LedgerInd',
]);

export function makeSemanticLedgerEntry0({
  index,
  id,
  previousId = null,
  entry,
  transition,
} = {}) {
  if (!Number.isSafeInteger(index) || index < 0) {
    throw new TypeError('makeSemanticLedgerEntry0 index must be a nonnegative safe integer');
  }
  requireIdentifier0(id, 'makeSemanticLedgerEntry0 id');
  if (previousId !== null) {
    requireIdentifier0(previousId, 'makeSemanticLedgerEntry0 previousId');
  }
  if (!isPlainObject0(entry)) {
    throw new TypeError('makeSemanticLedgerEntry0 entry must be a semantic judgment object');
  }
  if (!isPlainObject0(transition)) {
    throw new TypeError('makeSemanticLedgerEntry0 transition must be a semantic judgment object');
  }

  return Object.freeze({
    kind: 'SemanticLedgerEntry0',
    index,
    id,
    previousId,
    entry,
    transition,
  });
}

export function makeSemanticLedger0(ledgerId, entries = []) {
  requireIdentifier0(ledgerId, 'makeSemanticLedger0 ledgerId');
  if (!Array.isArray(entries)) {
    throw new TypeError('makeSemanticLedger0 entries must be an array');
  }

  return Object.freeze({
    kind: 'SemanticLedger0',
    version: CHECKER_VERSION,
    ledgerId,
    entries: Object.freeze([...entries]),
  });
}

/**
 * A local ledger case is accepted Record.intro evidence. It binds the declared
 * entry and local transition judgment to a current invariant, and for non-base
 * entries binds the exact invariant closed at the previous ledger position.
 */
export function makeSemanticLedgerIndCase0({
  ledgerId,
  entryId,
  entry,
  transition,
  current,
  previous = null,
} = {}) {
  requireIdentifier0(ledgerId, 'makeSemanticLedgerIndCase0 ledgerId');
  requireIdentifier0(entryId, 'makeSemanticLedgerIndCase0 entryId');

  const fields = [
    makeSemanticRecordField0('current', current),
    makeSemanticRecordField0('entry', entry),
    makeSemanticRecordField0('transition', transition),
  ];
  if (previous !== null) {
    fields.push(makeSemanticRecordField0('previous', previous));
  }
  fields.sort((left, right) => compareText0(left.name, right.name));

  return makeSemanticRecordJudgment0(
    caseRecordType0(ledgerId, entryId),
    fields,
  );
}

export function makeSemanticLedgerIndJudgment0({
  ledgerId,
  entryOrder,
  baseEntryId,
  finalEntryId,
  caseProofIds,
  cases,
  baseInvariant,
  finalInvariant,
} = {}) {
  requireIdentifier0(ledgerId, 'makeSemanticLedgerIndJudgment0 ledgerId');
  for (const [name, value] of Object.entries({ entryOrder, caseProofIds, cases })) {
    if (!Array.isArray(value)) {
      throw new TypeError(`makeSemanticLedgerIndJudgment0 ${name} must be an array`);
    }
  }
  requireIdentifier0(baseEntryId, 'makeSemanticLedgerIndJudgment0 baseEntryId');
  requireIdentifier0(finalEntryId, 'makeSemanticLedgerIndJudgment0 finalEntryId');

  return Object.freeze({
    kind: 'SemanticLedgerIndJudgment0',
    version: CHECKER_VERSION,
    ledgerId,
    entryOrder: Object.freeze([...entryOrder]),
    baseEntryId,
    finalEntryId,
    caseProofIds: Object.freeze([...caseProofIds]),
    cases: Object.freeze([...cases]),
    baseInvariant,
    finalInvariant,
    allEntriesClosed: true,
  });
}

/**
 * Generator helper. The checker recomputes the complete closure and compares
 * it canonically; this helper is never a trusted readiness input.
 */
export function deriveSemanticLedgerIndJudgment0({
  ledger,
  caseRecords,
  caseProofIds,
} = {}) {
  const ledgerCheck = validateLedger0(ledger, ['ledger']);
  if (!ledgerCheck.ok) throw new TypeError(ledgerCheck.witness.reason);
  if (!Array.isArray(caseRecords) || !Array.isArray(caseProofIds)) {
    throw new TypeError('deriveSemanticLedgerIndJudgment0 requires case arrays');
  }

  const derived = deriveClosure0(
    ledgerCheck.ledger,
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

export function CheckSemanticKernelReadinessLedgerInd0() {
  const checker = 'CheckSemanticKernelReadinessLedgerInd0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessLedgerInd0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofDAGInd0',
    proofChecker: 'CheckSemanticKernelProofLedgerInd0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    ledgerIndOperations: [...SEMANTIC_LEDGERIND_OPERATIONS0],
    localCasesMustBeAcceptedRecordEvidence: true,
    localTransitionJudgmentsMustBeAccepted: true,
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
        reason: 'LedgerInd-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Checks Eq/Subst/Record/DAGInd with the predecessor checker and checks
 * LedgerInd as exact finite closure of accepted local ledger cases.
 */
export function CheckSemanticKernelProofLedgerInd0(input) {
  const checker = 'CheckSemanticKernelProofLedgerInd0';
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
        reason: 'LedgerInd-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0.includes(node.RuleName),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofDAGInd0',
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
        reason: 'Eq/Subst/Record/DAGInd sub-DAG rejected under the predecessor semantic checker',
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
    if (node.RuleName === 'LedgerInd') {
      semantic = checkLedgerIndRule0(node, premises, path);
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0.includes(rule),
  );
  const ledgerIndNodeCount = summaries.filter(
    (node) => node.RuleName === 'LedgerInd',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofLedgerInd0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofDAGInd0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedLedgerIndOperations: [...SEMANTIC_LEDGERIND_OPERATIONS0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      ledgerIndNodeCount,
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
      { kind: 'SemanticLedgerIndProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticLedgerIndProofInput0NF', form: 'object', nodeCount: nodes.length },
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
        'LedgerInd-extended semantic proof node rejects undeclared fields',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'LedgerInd-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'LedgerInd-extended semantic kernel accepts Full mode only',
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

    if (node.RuleName === 'LedgerInd') {
      const payload = validateLedgerIndPayload0(node.Payload, [...path, 'Payload']);
      if (!payload.ok) return payload;
      const conclusion = validateLedgerIndJudgmentShape0(
        node.Conclusion,
        [...path, 'Conclusion'],
      );
      if (!conclusion.ok) return conclusion;
    }

    seenIds.add(node.id);
  }

  return validationAccept0({
    kind: 'SemanticLedgerIndProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateLedgerIndPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'ledger']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'LedgerInd payload rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (!SEMANTIC_LEDGERIND_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'LedgerInd operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_LEDGERIND_OPERATIONS0],
      },
    );
  }

  return validateLedger0(payload.ledger, [...path, 'ledger']);
}

function validateLedger0(ledger, path) {
  if (!isPlainObject0(ledger)) {
    return validationReject0(path, 'LedgerInd ledger must be an object', {
      actual: typeof ledger,
    });
  }

  const allowedLedgerKeys = new Set(['kind', 'version', 'ledgerId', 'entries']);
  const unexpectedLedgerKeys = Object.keys(ledger)
    .filter((key) => !allowedLedgerKeys.has(key));
  if (unexpectedLedgerKeys.length !== 0) {
    return validationReject0(
      [...path, unexpectedLedgerKeys[0]],
      'LedgerInd ledger rejects undeclared fields',
      { unexpectedFields: unexpectedLedgerKeys.sort() },
    );
  }

  if (ledger.kind !== 'SemanticLedger0') {
    return validationReject0(
      [...path, 'kind'],
      'LedgerInd ledger kind must be SemanticLedger0',
      { actual: ledger.kind },
    );
  }

  if (ledger.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `LedgerInd ledger version must be ${CHECKER_VERSION}`,
      { actual: ledger.version },
    );
  }

  if (!isIdentifier0(ledger.ledgerId)) {
    return validationReject0(
      [...path, 'ledgerId'],
      'LedgerInd ledgerId must be a canonical identifier',
      { actual: ledger.ledgerId },
    );
  }

  if (!Array.isArray(ledger.entries) || ledger.entries.length === 0) {
    return validationReject0(
      [...path, 'entries'],
      'LedgerInd ledger must contain a nonempty entries array',
      {
        actual: Array.isArray(ledger.entries)
          ? ledger.entries.length
          : typeof ledger.entries,
      },
    );
  }

  if (ledger.entries.length > MAX_LEDGER_ENTRIES) {
    return validationReject0(
      [...path, 'entries'],
      'LedgerInd ledger exceeds maxLedgerEntries',
      { maxLedgerEntries: MAX_LEDGER_ENTRIES, actual: ledger.entries.length },
    );
  }

  const seenIds = new Set();
  let previousId = null;

  for (let index = 0; index < ledger.entries.length; index += 1) {
    const entry = ledger.entries[index];
    const entryPath = [...path, 'entries', index];

    if (!isPlainObject0(entry)) {
      return validationReject0(entryPath, 'LedgerInd entry must be an object', {
        actual: typeof entry,
      });
    }

    const allowedEntryKeys = new Set([
      'kind',
      'index',
      'id',
      'previousId',
      'entry',
      'transition',
    ]);
    const unexpectedEntryKeys = Object.keys(entry)
      .filter((key) => !allowedEntryKeys.has(key));
    if (unexpectedEntryKeys.length !== 0) {
      return validationReject0(
        [...entryPath, unexpectedEntryKeys[0]],
        'LedgerInd entry rejects undeclared fields',
        { unexpectedFields: unexpectedEntryKeys.sort() },
      );
    }

    if (entry.kind !== 'SemanticLedgerEntry0') {
      return validationReject0(
        [...entryPath, 'kind'],
        'LedgerInd entry kind must be SemanticLedgerEntry0',
        { actual: entry.kind },
      );
    }

    if (entry.index !== index) {
      return validationReject0(
        [...entryPath, 'index'],
        'LedgerInd entry indices must be consecutive from zero',
        { expected: index, actual: entry.index },
      );
    }

    if (!isIdentifier0(entry.id)) {
      return validationReject0(
        [...entryPath, 'id'],
        'LedgerInd entry id must be a canonical identifier',
        { actual: entry.id },
      );
    }

    if (seenIds.has(entry.id)) {
      return validationReject0(
        [...entryPath, 'id'],
        'LedgerInd entry ids must be unique',
        { id: entry.id },
      );
    }

    const expectedPreviousId = index === 0 ? null : previousId;
    if (entry.previousId !== expectedPreviousId) {
      return validationReject0(
        [...entryPath, 'previousId'],
        'LedgerInd previousId must name the immediately preceding ledger entry',
        { expected: expectedPreviousId, actual: entry.previousId },
      );
    }

    if (!isPlainObject0(entry.entry)) {
      return validationReject0(
        [...entryPath, 'entry'],
        'LedgerInd entry payload must be a semantic judgment object',
        { actual: typeof entry.entry },
      );
    }

    if (!isPlainObject0(entry.transition)) {
      return validationReject0(
        [...entryPath, 'transition'],
        'LedgerInd local transition must be a semantic judgment object',
        { actual: typeof entry.transition },
      );
    }

    seenIds.add(entry.id);
    previousId = entry.id;
  }

  return validationAcceptWith0({
    kind: 'SemanticLedger0NF',
    ledgerId: ledger.ledgerId,
    entryCount: ledger.entries.length,
    entryOrder: ledger.entries.map((entry) => entry.id),
    baseEntryId: ledger.entries[0].id,
    finalEntryId: ledger.entries.at(-1).id,
  }, {
    ledger,
  });
}

function validateLedgerIndJudgmentShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'LedgerInd conclusion must be an object', {
      actual: typeof judgment,
    });
  }

  const allowedKeys = new Set([
    'kind',
    'version',
    'ledgerId',
    'entryOrder',
    'baseEntryId',
    'finalEntryId',
    'caseProofIds',
    'cases',
    'baseInvariant',
    'finalInvariant',
    'allEntriesClosed',
  ]);
  const unexpected = Object.keys(judgment).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'LedgerInd conclusion rejects undeclared fields',
      { unexpectedFields: unexpected.sort() },
    );
  }

  if (judgment.kind !== 'SemanticLedgerIndJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'LedgerInd conclusion kind must be SemanticLedgerIndJudgment0',
      { actual: judgment.kind },
    );
  }

  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `LedgerInd conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }

  if (!isIdentifier0(judgment.ledgerId)) {
    return validationReject0(
      [...path, 'ledgerId'],
      'LedgerInd conclusion ledgerId must be a canonical identifier',
      { actual: judgment.ledgerId },
    );
  }

  for (const field of ['entryOrder', 'caseProofIds', 'cases']) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `LedgerInd conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }

  if (!isIdentifier0(judgment.baseEntryId)) {
    return validationReject0(
      [...path, 'baseEntryId'],
      'LedgerInd conclusion baseEntryId must be a canonical identifier',
      { actual: judgment.baseEntryId },
    );
  }

  if (!isIdentifier0(judgment.finalEntryId)) {
    return validationReject0(
      [...path, 'finalEntryId'],
      'LedgerInd conclusion finalEntryId must be a canonical identifier',
      { actual: judgment.finalEntryId },
    );
  }

  if (judgment.allEntriesClosed !== true) {
    return validationReject0(
      [...path, 'allEntriesClosed'],
      'LedgerInd conclusion allEntriesClosed must be true',
      { actual: judgment.allEntriesClosed },
    );
  }

  return validationAccept0({
    kind: 'SemanticLedgerIndJudgmentShape0NF',
    ledgerId: judgment.ledgerId,
    caseCount: judgment.cases.length,
  });
}

function checkLedgerIndRule0(node, premises, path) {
  if (node.Payload.op !== 'close') {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'LedgerInd rule supports only close',
      { actual: node.Payload.op },
    );
  }

  const ledgerCheck = validateLedger0(
    node.Payload.ledger,
    [...path, 'Payload', 'ledger'],
  );
  if (!ledgerCheck.ok) return ledgerCheck;

  const derived = deriveClosure0(
    ledgerCheck.ledger,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;

  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'LedgerInd conclusion must exactly equal the computed all-entry closure',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticLedgerIndRule0NF',
    ruleName: 'LedgerInd',
    operation: 'close',
    ledgerId: ledgerCheck.ledger.ledgerId,
    entryCount: ledgerCheck.ledger.entries.length,
    baseEntryId: ledgerCheck.ledger.entries[0].id,
    finalEntryId: ledgerCheck.ledger.entries.at(-1).id,
    caseProofIds: [...node.Premises],
    transitionComplete: true,
    allEntriesClosed: true,
  });
}

function deriveClosure0(ledger, premises, caseProofIds, path) {
  if (!Array.isArray(premises) || !Array.isArray(caseProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'LedgerInd closure requires premise and proof-id arrays',
      null,
    );
  }

  if (premises.length !== ledger.entries.length
      || caseProofIds.length !== ledger.entries.length) {
    return validationReject0(
      [...path, 'Premises'],
      'LedgerInd requires exactly one local case record for every ledger entry',
      {
        expected: ledger.entries.length,
        actualPremises: premises.length,
        actualProofIds: caseProofIds.length,
      },
    );
  }

  const currentByEntry = new Map();
  const cases = [];

  for (let index = 0; index < ledger.entries.length; index += 1) {
    const ledgerEntry = ledger.entries[index];
    const premise = premises[index];
    const casePath = [...path, 'Premises', index];

    if (!isPlainObject0(premise)) {
      return validationReject0(
        casePath,
        'LedgerInd case premise must resolve to an earlier accepted proof node',
        { actual: premise },
      );
    }

    if (premise.RuleName !== 'Record' || premise.operation !== 'intro') {
      return validationReject0(
        casePath,
        'LedgerInd case premise must be accepted Record.intro evidence',
        {
          actualRuleName: premise.RuleName,
          actualOperation: premise.operation,
        },
      );
    }

    const recordCheck = validateCaseRecord0(
      premise.Conclusion,
      ledger.ledgerId,
      ledgerEntry,
      currentByEntry,
      casePath,
    );
    if (!recordCheck.ok) return recordCheck;

    currentByEntry.set(ledgerEntry.id, recordCheck.current);
    cases.push(Object.freeze({
      kind: 'SemanticLedgerIndCaseResult0',
      index,
      entryId: ledgerEntry.id,
      previousId: ledgerEntry.previousId,
      entry: ledgerEntry.entry,
      transition: ledgerEntry.transition,
      invariant: recordCheck.current,
    }));
  }

  const baseInvariant = currentByEntry.get(ledger.entries[0].id);
  const finalInvariant = currentByEntry.get(ledger.entries.at(-1).id);
  const judgment = makeSemanticLedgerIndJudgment0({
    ledgerId: ledger.ledgerId,
    entryOrder: ledger.entries.map((entry) => entry.id),
    baseEntryId: ledger.entries[0].id,
    finalEntryId: ledger.entries.at(-1).id,
    caseProofIds,
    cases,
    baseInvariant,
    finalInvariant,
  });

  return validationAcceptWith0({
    kind: 'SemanticLedgerIndClosure0NF',
    ledgerId: ledger.ledgerId,
    entryCount: ledger.entries.length,
    caseProofIds: [...caseProofIds],
  }, {
    judgment,
  });
}

function validateCaseRecord0(record, ledgerId, ledgerEntry, currentByEntry, path) {
  if (!isPlainObject0(record)) {
    return validationReject0(path, 'LedgerInd case conclusion must be a record judgment', {
      actual: typeof record,
    });
  }

  if (record.kind !== 'SemanticRecordJudgment0') {
    return validationReject0(
      [...path, 'Conclusion', 'kind'],
      'LedgerInd case conclusion must be SemanticRecordJudgment0',
      { actual: record.kind },
    );
  }

  const expectedRecordType = caseRecordType0(ledgerId, ledgerEntry.id);
  if (record.recordType !== expectedRecordType) {
    return validationReject0(
      [...path, 'Conclusion', 'recordType'],
      'LedgerInd case recordType must bind the ledger and entry id',
      { expected: expectedRecordType, actual: record.recordType },
    );
  }

  if (!Array.isArray(record.fields)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'LedgerInd case record fields must be an array',
      { actual: typeof record.fields },
    );
  }

  const expectedNames = ledgerEntry.previousId === null
    ? ['current', 'entry', 'transition']
    : ['current', 'entry', 'previous', 'transition'];
  const actualNames = record.fields.map((field) => field?.name ?? null);
  if (!sameCanonical0(actualNames, expectedNames)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'LedgerInd case fields must contain the exact entry, transition, current invariant, and prior invariant',
      { expected: expectedNames, actual: actualNames },
    );
  }

  const fieldMap = new Map(record.fields.map((field) => [field.name, field.judgment]));
  const entry = fieldMap.get('entry');
  if (!sameCanonical0(entry, ledgerEntry.entry)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'LedgerInd case entry judgment must exactly match the declared ledger entry',
      { expected: ledgerEntry.entry, actual: entry },
    );
  }

  const transition = fieldMap.get('transition');
  if (!sameCanonical0(transition, ledgerEntry.transition)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'LedgerInd case transition judgment must exactly match the declared local transition',
      { expected: ledgerEntry.transition, actual: transition },
    );
  }

  const current = fieldMap.get('current');
  if (!isPlainObject0(current)) {
    return validationReject0(
      [...path, 'Conclusion', 'fields'],
      'LedgerInd current invariant must be a semantic judgment object',
      { actual: current },
    );
  }

  if (ledgerEntry.previousId !== null) {
    const expectedPrevious = currentByEntry.get(ledgerEntry.previousId);
    if (expectedPrevious === undefined) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'LedgerInd case refers to a previous entry without an earlier closed invariant',
        { entryId: ledgerEntry.id, previousId: ledgerEntry.previousId },
      );
    }

    const actualPrevious = fieldMap.get('previous');
    if (!sameCanonical0(actualPrevious, expectedPrevious)) {
      return validationReject0(
        [...path, 'Conclusion', 'fields'],
        'LedgerInd previous invariant must exactly match the immediately preceding closed invariant',
        {
          entryId: ledgerEntry.id,
          previousId: ledgerEntry.previousId,
          expected: expectedPrevious,
          actual: actualPrevious,
        },
      );
    }
  }

  return validationAcceptWith0({
    kind: 'SemanticLedgerIndCase0NF',
    ledgerId,
    entryId: ledgerEntry.id,
    index: ledgerEntry.index,
    previousId: ledgerEntry.previousId,
    transitionBound: true,
  }, {
    current,
  });
}

function caseRecordType0(ledgerId, entryId) {
  return `LedgerIndCase0.${ledgerId}.${entryId}`;
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(baseNodes));
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofDAGInd0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofDAGInd0 threw instead of returning a reject record',
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
