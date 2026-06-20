import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProof0,
  SEMANTIC_KERNEL_REQUIRED_RULES0,
  SEMANTIC_KERNEL_SUPPORTED_RULES0,
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_NODES = 100_000;
const MAX_RECORD_DEPTH = 128;

export const SEMANTIC_RECORD_OPERATIONS0 = Object.freeze([
  'intro',
  'project',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES0,
  'Record',
]);

export function makeSemanticRecordField0(name, judgment) {
  requireText0(name, 'makeSemanticRecordField0 name');
  return Object.freeze({
    kind: 'SemanticRecordField0',
    name,
    judgment,
  });
}

export function makeSemanticRecordJudgment0(recordType, fields = []) {
  requireText0(recordType, 'makeSemanticRecordJudgment0 recordType');
  if (!Array.isArray(fields)) {
    throw new TypeError('makeSemanticRecordJudgment0 fields must be an array');
  }

  return Object.freeze({
    kind: 'SemanticRecordJudgment0',
    version: CHECKER_VERSION,
    recordType,
    fields: Object.freeze([...fields]),
  });
}

/**
 * Readiness for the semantic kernel extended by the Record rule family.
 * Support is derived from executable checkers, not caller metadata.
 */
export function CheckSemanticKernelReadinessRecord0() {
  const checker = 'CheckSemanticKernelReadinessRecord0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessRecord0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProof0',
    proofChecker: 'CheckSemanticKernelProofRecord0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    recordOperations: [...SEMANTIC_RECORD_OPERATIONS0],
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
        reason: 'record-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({ checker, nf, ledger });
}

/**
 * Semantic proof checker for Eq, Subst, and Record.
 *
 * Eq/Subst nodes are validated once by the preceding semantic checker. Record
 * nodes are then validated in the original DAG order. An Eq/Subst node that
 * attempts to depend on a Record node fails in the base checker because the
 * filtered base DAG cannot resolve that premise. This is intentionally
 * fail-closed until those rule families explicitly support record judgments.
 */
export function CheckSemanticKernelProofRecord0(input) {
  const checker = 'CheckSemanticKernelProofRecord0';
  const ledger = [];

  const dag = normalizeDAG0(input);
  ledger.push(makeLedgerEntry0('input', dag.ok, dag.nf ?? dag.witness));
  if (!dag.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.input`,
      dag,
      ledger,
    );
  }

  if (dag.nodes.length > MAX_NODES) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.bounds`,
      path: ['nodes'],
      witness: {
        reason: 'record-extended semantic proof DAG exceeds maxNodes',
        maxNodes: MAX_NODES,
        actual: dag.nodes.length,
      },
      ledger,
    });
  }

  const shape = validateDAGShape0(dag.nodes);
  ledger.push(makeLedgerEntry0(
    'shape',
    shape.ok,
    shape.nf ?? shape.witness,
  ));
  if (!shape.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.shape`,
      shape,
      ledger,
    );
  }

  const baseNodes = dag.nodes.filter(
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES0.includes(node.RuleName),
  );
  const baseRecord = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProof0',
    baseRecord.ok && baseRecord.record.tag === 'accept',
    baseRecord.ok ? baseRecord.record : baseRecord.witness,
  ));

  if (!baseRecord.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.baseProof.exception`,
      path: ['nodes'],
      witness: baseRecord.witness,
      ledger,
    });
  }

  if (baseRecord.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.baseProof`,
      path: ['nodes'],
      witness: {
        reason: 'Eq/Subst sub-DAG rejected under the base semantic checker',
        baseNodeIds: baseNodes.map((node) => node.id),
        inner: compactReject0(baseRecord.record),
      },
      ledger,
    });
  }

  const accepted = new Map();
  const nodeSummaries = [];

  for (let index = 0; index < dag.nodes.length; index += 1) {
    const node = dag.nodes[index];
    const path = ['nodes', index];
    const phase = String(index).padStart(4, '0');
    const premises = node.Premises.map((premiseId) => accepted.get(premiseId));

    let semantic;
    if (node.RuleName === 'Record') {
      semantic = checkRecordRule0(node, premises, path);
    } else {
      semantic = validationAccept0({
        kind: 'SemanticBaseRuleReference0NF',
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
      Conclusion: node.Conclusion,
      operation: semantic.nf.operation ?? null,
      digest: digestCanonical0(node),
    });
    accepted.set(node.id, summary);
    nodeSummaries.push(summary);
  }

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0.includes(rule),
  );
  const recordNodeCount = nodeSummaries.filter(
    (node) => node.RuleName === 'Record',
  ).length;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofRecord0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProof0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_RECORD0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedRecordOperations: [...SEMANTIC_RECORD_OPERATIONS0],
      nodeCount: nodeSummaries.length,
      baseNodeCount: baseNodes.length,
      recordNodeCount,
      acceptedNodeIds: nodeSummaries.map((node) => node.id),
      conclusionDigests: nodeSummaries.map((node) => ({
        id: node.id,
        digest: digestCanonical0(node.Conclusion),
      })),
    },
    ledger,
  });
}

function normalizeDAG0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      { kind: 'SemanticRecordDAGInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'SemanticRecordDAGInput0NF', form: 'object', nodeCount: nodes.length },
    { nodes },
  );
}

function validateDAGShape0(nodes) {
  const seenIds = new Set();

  for (let index = 0; index < nodes.length; index += 1) {
    const path = ['nodes', index];
    const node = nodes[index];

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
        'record-extended semantic proof node rejects undeclared fields',
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

    if (!isText0(node.id)) {
      return validationReject0(
        [...path, 'id'],
        'semantic proof node id must be a non-empty string',
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

    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'record-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0],
        },
      );
    }

    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'record-extended semantic kernel accepts Full mode only',
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
      if (!isText0(premiseId)) {
        return validationReject0(
          [...path, 'Premises', premiseIndex],
          'semantic proof premise id must be a non-empty string',
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

    if (node.RuleName === 'Record') {
      if (!isPlainObject0(node.Conclusion)) {
        return validationReject0(
          [...path, 'Conclusion'],
          'Record rule conclusion must be a semantic judgment object',
          { actual: typeof node.Conclusion },
        );
      }

      if (node.Payload.op === 'intro') {
        const record = validateRecordJudgment0(
          node.Conclusion,
          [...path, 'Conclusion'],
          0,
          new Set(),
        );
        if (!record.ok) return record;
      }
    }

    seenIds.add(node.id);
  }

  return validationAccept0({
    kind: 'SemanticRecordDAGShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function checkRecordRule0(node, premises, path) {
  const operation = node.Payload.op;
  const allowedPayloadKeys = operation === 'intro'
    ? new Set(['op', 'recordType', 'fieldNames'])
    : operation === 'project'
      ? new Set(['op', 'recordType', 'fieldName'])
      : new Set(['op']);
  const unexpectedPayloadKeys = Object.keys(node.Payload)
    .filter((key) => !allowedPayloadKeys.has(key));
  if (unexpectedPayloadKeys.length !== 0) {
    return validationReject0(
      [...path, 'Payload', unexpectedPayloadKeys[0]],
      'Record rule payload rejects undeclared fields',
      { unexpectedFields: unexpectedPayloadKeys.sort() },
    );
  }

  if (!SEMANTIC_RECORD_OPERATIONS0.includes(operation)) {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'Record rule operation is unsupported',
      {
        actual: operation,
        supportedOperations: [...SEMANTIC_RECORD_OPERATIONS0],
      },
    );
  }

  if (operation === 'intro') {
    return checkRecordIntro0(node, premises, path);
  }

  return checkRecordProject0(node, premises, path);
}

function checkRecordIntro0(node, premises, path) {
  const conclusion = node.Conclusion;
  const recordType = node.Payload.recordType;
  const fieldNames = node.Payload.fieldNames;

  if (!isText0(recordType)) {
    return validationReject0(
      [...path, 'Payload', 'recordType'],
      'Record.intro payload must name a recordType',
      { actual: recordType },
    );
  }

  if (recordType !== conclusion.recordType) {
    return validationReject0(
      [...path, 'Payload', 'recordType'],
      'Record.intro payload recordType must match the conclusion recordType',
      { expected: conclusion.recordType, actual: recordType },
    );
  }

  if (!Array.isArray(fieldNames)) {
    return validationReject0(
      [...path, 'Payload', 'fieldNames'],
      'Record.intro payload fieldNames must be an array',
      { actual: typeof fieldNames },
    );
  }

  const conclusionNames = conclusion.fields.map((field) => field.name);
  if (!sameCanonical0(fieldNames, conclusionNames)) {
    return validationReject0(
      [...path, 'Payload', 'fieldNames'],
      'Record.intro payload fieldNames must exactly match the canonical conclusion fields',
      { expected: conclusionNames, actual: fieldNames },
    );
  }

  if (premises.length !== conclusion.fields.length) {
    return validationReject0(
      [...path, 'Premises'],
      'Record.intro requires exactly one premise for each conclusion field',
      { expected: conclusion.fields.length, actual: premises.length },
    );
  }

  for (let index = 0; index < conclusion.fields.length; index += 1) {
    const expected = conclusion.fields[index].judgment;
    const actual = premises[index].Conclusion;
    if (!sameCanonical0(expected, actual)) {
      return validationReject0(
        [...path, 'Premises', index],
        'Record.intro field judgment must exactly equal the corresponding premise conclusion',
        {
          fieldName: conclusion.fields[index].name,
          expected,
          actual,
        },
      );
    }
  }

  return validationAccept0({
    kind: 'SemanticRecordRule0NF',
    ruleName: 'Record',
    operation: 'intro',
    recordType,
    fieldCount: conclusion.fields.length,
    fieldNames: conclusionNames,
    premiseCount: premises.length,
  });
}

function checkRecordProject0(node, premises, path) {
  if (premises.length !== 1) {
    return validationReject0(
      [...path, 'Premises'],
      'Record.project requires exactly one record premise',
      { expected: 1, actual: premises.length },
    );
  }

  const premiseConclusion = premises[0].Conclusion;
  const premiseRecord = validateRecordJudgment0(
    premiseConclusion,
    [...path, 'Premises', 0, 'Conclusion'],
    0,
    new Set(),
  );
  if (!premiseRecord.ok) {
    return validationReject0(
      [...path, 'Premises', 0],
      'Record.project premise must conclude a semantic record judgment',
      { actual: premiseConclusion },
    );
  }

  const recordType = node.Payload.recordType;
  const fieldName = node.Payload.fieldName;

  if (recordType !== premiseConclusion.recordType) {
    return validationReject0(
      [...path, 'Payload', 'recordType'],
      'Record.project payload recordType must match the premise recordType',
      { expected: premiseConclusion.recordType, actual: recordType },
    );
  }

  if (!isText0(fieldName)) {
    return validationReject0(
      [...path, 'Payload', 'fieldName'],
      'Record.project payload must name a field',
      { actual: fieldName },
    );
  }

  const field = premiseConclusion.fields.find((entry) => entry.name === fieldName);
  if (field === undefined) {
    return validationReject0(
      [...path, 'Payload', 'fieldName'],
      'Record.project field is not present in the premise record',
      {
        fieldName,
        availableFields: premiseConclusion.fields.map((entry) => entry.name),
      },
    );
  }

  if (!sameCanonical0(node.Conclusion, field.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'Record.project conclusion must exactly equal the selected field judgment',
      { expected: field.judgment, actual: node.Conclusion },
    );
  }

  return validationAccept0({
    kind: 'SemanticRecordRule0NF',
    ruleName: 'Record',
    operation: 'project',
    recordType,
    fieldName,
    premiseCount: 1,
  });
}

function validateRecordJudgment0(value, path, depth, seen) {
  if (depth > MAX_RECORD_DEPTH) {
    return validationReject0(path, 'semantic record exceeds maxRecordDepth', {
      maxRecordDepth: MAX_RECORD_DEPTH,
    });
  }

  if (!isPlainObject0(value)) {
    return validationReject0(path, 'semantic record judgment must be an object', {
      actual: typeof value,
    });
  }

  if (seen.has(value)) {
    return validationReject0(path, 'semantic record judgments must be acyclic', null);
  }
  seen.add(value);

  if (value.kind !== 'SemanticRecordJudgment0') {
    seen.delete(value);
    return validationReject0(
      [...path, 'kind'],
      'semantic record judgment kind must be SemanticRecordJudgment0',
      { actual: value.kind },
    );
  }

  if (value.version !== CHECKER_VERSION) {
    seen.delete(value);
    return validationReject0(
      [...path, 'version'],
      `semantic record judgment version must be ${CHECKER_VERSION}`,
      { actual: value.version },
    );
  }

  if (!isText0(value.recordType)) {
    seen.delete(value);
    return validationReject0(
      [...path, 'recordType'],
      'semantic record judgment recordType must be non-empty',
      { actual: value.recordType },
    );
  }

  if (!Array.isArray(value.fields)) {
    seen.delete(value);
    return validationReject0(
      [...path, 'fields'],
      'semantic record judgment fields must be an array',
      { actual: typeof value.fields },
    );
  }

  const allowedRecordKeys = new Set([
    'kind',
    'version',
    'recordType',
    'fields',
  ]);
  const unexpectedRecordKeys = Object.keys(value)
    .filter((key) => !allowedRecordKeys.has(key));
  if (unexpectedRecordKeys.length !== 0) {
    seen.delete(value);
    return validationReject0(
      [...path, unexpectedRecordKeys[0]],
      'semantic record judgment rejects undeclared fields',
      { unexpectedFields: unexpectedRecordKeys.sort() },
    );
  }

  const names = [];
  for (let index = 0; index < value.fields.length; index += 1) {
    const field = value.fields[index];
    const fieldPath = [...path, 'fields', index];

    if (!isPlainObject0(field)) {
      seen.delete(value);
      return validationReject0(fieldPath, 'semantic record field must be an object', {
        actual: typeof field,
      });
    }

    const allowedFieldKeys = new Set(['kind', 'name', 'judgment']);
    const unexpectedFieldKeys = Object.keys(field)
      .filter((key) => !allowedFieldKeys.has(key));
    if (unexpectedFieldKeys.length !== 0) {
      seen.delete(value);
      return validationReject0(
        [...fieldPath, unexpectedFieldKeys[0]],
        'semantic record field rejects undeclared fields',
        { unexpectedFields: unexpectedFieldKeys.sort() },
      );
    }

    if (field.kind !== 'SemanticRecordField0') {
      seen.delete(value);
      return validationReject0(
        [...fieldPath, 'kind'],
        'semantic record field kind must be SemanticRecordField0',
        { actual: field.kind },
      );
    }

    if (!isText0(field.name)) {
      seen.delete(value);
      return validationReject0(
        [...fieldPath, 'name'],
        'semantic record field name must be non-empty',
        { actual: field.name },
      );
    }

    if (!isPlainObject0(field.judgment)) {
      seen.delete(value);
      return validationReject0(
        [...fieldPath, 'judgment'],
        'semantic record field judgment must be an object',
        { actual: typeof field.judgment },
      );
    }

    if (field.judgment.kind === 'SemanticRecordJudgment0') {
      const nested = validateRecordJudgment0(
        field.judgment,
        [...fieldPath, 'judgment'],
        depth + 1,
        seen,
      );
      if (!nested.ok) {
        seen.delete(value);
        return nested;
      }
    }

    names.push(field.name);
  }

  const sorted = [...names].sort(compareText0);
  if (!sameCanonical0(names, sorted)) {
    seen.delete(value);
    return validationReject0(
      [...path, 'fields'],
      'semantic record fields must be in canonical name order',
      { expected: sorted, actual: names },
    );
  }

  if (new Set(names).size !== names.length) {
    seen.delete(value);
    return validationReject0(
      [...path, 'fields'],
      'semantic record field names must be unique',
      { fieldNames: names },
    );
  }

  seen.delete(value);
  return validationAccept0({
    kind: 'SemanticRecordJudgment0NF',
    recordType: value.recordType,
    fieldCount: value.fields.length,
    fieldNames: names,
  });
}

function callBaseProofChecker0(baseNodes) {
  try {
    const record = CheckSemanticKernelProof0(makeSemanticProofDAG0(baseNodes));
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProof0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProof0 threw instead of returning a reject record',
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

function isText0(value) {
  return typeof value === 'string' && value.trim().length > 0;
}

function requireText0(value, label) {
  if (!isText0(value)) {
    throw new TypeError(`${label} must be a non-empty string`);
  }
}
