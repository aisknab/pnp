import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSemanticKernelProofIntArith0,
  SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0,
} from './pcc-kernel-intarith-semantic0.mjs';

import {
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from './pcc-kernel-record-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;
const MAX_PROOF_NODES = 100_000;
const MAX_COORDINATES = 4_096;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;
const JUDGMENT_KIND_PATTERN = /^Semantic[A-Za-z0-9]+Judgment0$/;

export const SEMANTIC_TRANSPORT_OPERATIONS0 = Object.freeze([
  'rename',
  'project',
  'lift',
]);

export const SEMANTIC_TRANSPORT_MODES0 = Object.freeze([
  'full',
  'quotient',
]);

export const SEMANTIC_TRANSPORT_COORDINATE_ROLES0 = Object.freeze([
  'boundary',
  'interface',
  'truth',
  'relation',
  'profile',
  'origin',
  'kernel',
  'obligation',
  'prefix',
  'direction',
  'saturation',
  'budget',
  'charge',
  'payload',
]);

export const SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0 = Object.freeze([
  ...SEMANTIC_KERNEL_REQUIRED_RULES_INTARITH0,
]);

export const SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0 = Object.freeze([
  ...SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0,
  'Transport',
]);

export function makeSemanticTransportCoordinate0({
  index,
  id,
  role,
} = {}) {
  requireIndex0(index, 'makeSemanticTransportCoordinate0 index');
  requireIdentifier0(id, 'makeSemanticTransportCoordinate0 id');
  if (!SEMANTIC_TRANSPORT_COORDINATE_ROLES0.includes(role)) {
    throw new TypeError(
      `makeSemanticTransportCoordinate0 role must be one of ${SEMANTIC_TRANSPORT_COORDINATE_ROLES0.join(', ')}`,
    );
  }
  return Object.freeze({
    kind: 'SemanticTransportCoordinate0',
    version: CHECKER_VERSION,
    index,
    id,
    role,
  });
}

export function makeSemanticTransportCarrier0({
  carrierId,
  mode,
  coordinates = [],
} = {}) {
  requireIdentifier0(carrierId, 'makeSemanticTransportCarrier0 carrierId');
  if (!SEMANTIC_TRANSPORT_MODES0.includes(mode)) {
    throw new TypeError(
      `makeSemanticTransportCarrier0 mode must be one of ${SEMANTIC_TRANSPORT_MODES0.join(', ')}`,
    );
  }
  if (!Array.isArray(coordinates)) {
    throw new TypeError(
      'makeSemanticTransportCarrier0 coordinates must be an array',
    );
  }
  const carrier = Object.freeze({
    kind: 'SemanticTransportCarrier0',
    version: CHECKER_VERSION,
    carrierId,
    mode,
    coordinates: Object.freeze([...coordinates]),
  });
  const checked = validateCarrier0(carrier, ['carrier']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return carrier;
}

export function makeSemanticTransportMapEntry0({
  index,
  sourceCoordinateId,
  targetCoordinateId,
} = {}) {
  requireIndex0(index, 'makeSemanticTransportMapEntry0 index');
  requireIdentifier0(
    sourceCoordinateId,
    'makeSemanticTransportMapEntry0 sourceCoordinateId',
  );
  requireIdentifier0(
    targetCoordinateId,
    'makeSemanticTransportMapEntry0 targetCoordinateId',
  );
  return Object.freeze({
    kind: 'SemanticTransportMapEntry0',
    version: CHECKER_VERSION,
    index,
    sourceCoordinateId,
    targetCoordinateId,
  });
}

export function makeSemanticTransportSpec0({
  transportId,
  operation,
  sourceCarrier,
  targetCarrier,
  mapping = [],
} = {}) {
  requireIdentifier0(transportId, 'makeSemanticTransportSpec0 transportId');
  if (!SEMANTIC_TRANSPORT_OPERATIONS0.includes(operation)) {
    throw new TypeError(
      `makeSemanticTransportSpec0 operation must be one of ${SEMANTIC_TRANSPORT_OPERATIONS0.join(', ')}`,
    );
  }
  if (!Array.isArray(mapping)) {
    throw new TypeError('makeSemanticTransportSpec0 mapping must be an array');
  }
  const spec = Object.freeze({
    kind: 'SemanticTransportSpec0',
    version: CHECKER_VERSION,
    transportId,
    operation,
    sourceCarrier,
    targetCarrier,
    mapping: Object.freeze([...mapping]),
  });
  const checked = validateSpec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return spec;
}

export function makeSemanticTransportFactEvidence0({
  carrierId,
  coordinateId,
  judgment,
} = {}) {
  requireIdentifier0(
    carrierId,
    'makeSemanticTransportFactEvidence0 carrierId',
  );
  requireIdentifier0(
    coordinateId,
    'makeSemanticTransportFactEvidence0 coordinateId',
  );
  const judgmentCheck = validateEvidenceJudgment0(judgment, ['judgment']);
  if (!judgmentCheck.ok) {
    throw new TypeError(judgmentCheck.witness.reason);
  }
  return makeSemanticRecordJudgment0(
    factRecordType0(carrierId, coordinateId),
    [makeSemanticRecordField0('fact', judgment)],
  );
}

export function deriveSemanticTransportJudgment0({
  spec,
  evidenceRecords,
  evidenceProofIds,
} = {}) {
  const specCheck = validateSpec0(spec, ['spec']);
  if (!specCheck.ok) throw new TypeError(specCheck.witness.reason);
  if (!Array.isArray(evidenceRecords) || !Array.isArray(evidenceProofIds)) {
    throw new TypeError(
      'deriveSemanticTransportJudgment0 requires evidenceRecords and evidenceProofIds arrays',
    );
  }
  if (evidenceRecords.length !== evidenceProofIds.length) {
    throw new TypeError(
      'deriveSemanticTransportJudgment0 evidence arrays must have equal length',
    );
  }
  const premises = evidenceRecords.map((Conclusion, index) => ({
    id: evidenceProofIds[index],
    RuleName: 'Record',
    operation: 'intro',
    Conclusion,
  }));
  const derived = deriveTransport0(
    specCheck,
    premises,
    evidenceProofIds,
    ['derive'],
  );
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.judgment;
}

export function CheckSemanticKernelReadinessTransport0() {
  const checker = 'CheckSemanticKernelReadinessTransport0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadinessTransport0NF',
    checker,
    version: CHECKER_VERSION,
    baseProofChecker: 'CheckSemanticKernelProofIntArith0',
    proofChecker: 'CheckSemanticKernelProofTransport0',
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
    transportOperations: [...SEMANTIC_TRANSPORT_OPERATIONS0],
    transportModes: [...SEMANTIC_TRANSPORT_MODES0],
    coordinateRoles: [...SEMANTIC_TRANSPORT_COORDINATE_ROLES0],
    explicitFiniteCarriersRequired: true,
    exactSourceEvidenceCoverageRequired: true,
    orderAndRolePreservationRequired: true,
    projectionIsComparisonOnly: true,
    quotientResultCannotJustifyFullUse: true,
    liftRequiresEvidenceForEveryAddedCoordinate: true,
    callerLiftCompletionAndPreservationAssertionsForbidden: true,
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
        reason: 'Transport-extended semantic kernel is not ready for final-theorem use',
        missingRules,
      },
      ledger,
    });
  }
  return makeAcceptRecord0({ checker, nf, ledger });
}

export function CheckSemanticKernelProofTransport0(input) {
  const checker = 'CheckSemanticKernelProofTransport0';
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
        reason: 'Transport-extended semantic proof DAG exceeds maxNodes',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0.includes(
      node.RuleName,
    ),
  );
  const baseCall = callBaseProofChecker0(baseNodes);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofIntArith0',
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
        reason: 'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample/IntArith sub-DAG rejected under the predecessor semantic checker',
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
    const semantic = node.RuleName === 'Transport'
      ? checkTransportRule0(node, premises, path)
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

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0.includes(rule),
  );
  const transportNodeCount = summaries.filter(
    (node) => node.RuleName === 'Transport',
  ).length;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticKernelProofTransport0NF',
      checker,
      version: CHECKER_VERSION,
      semanticRuleChecking: true,
      failClosedUnsupportedRules: true,
      baseProofChecker: 'CheckSemanticKernelProofIntArith0',
      requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_TRANSPORT0],
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0],
      missingRequiredRules,
      semanticRuleCoverageComplete: missingRequiredRules.length === 0,
      supportedTransportOperations: [...SEMANTIC_TRANSPORT_OPERATIONS0],
      supportedTransportModes: [...SEMANTIC_TRANSPORT_MODES0],
      nodeCount: summaries.length,
      baseNodeCount: baseNodes.length,
      transportNodeCount,
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
        kind: 'SemanticTransportProofInput0NF',
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
      kind: 'SemanticTransportProofInput0NF',
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
        'Transport-extended semantic proof node rejects undeclared fields',
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
    if (!SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0.includes(node.RuleName)) {
      return validationReject0(
        [...path, 'RuleName'],
        'Transport-extended semantic kernel rejects unsupported rule',
        {
          actual: node.RuleName,
          supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0],
        },
      );
    }
    if ((node.Mode ?? 'Full') !== 'Full') {
      return validationReject0(
        [...path, 'Mode'],
        'Transport-extended semantic kernel accepts Full proof-node mode only',
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
    if (node.RuleName === 'Transport') {
      const payload = validateTransportPayload0(
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
    kind: 'SemanticTransportProofShape0NF',
    nodeCount: nodes.length,
    ids: nodes.map((node) => node.id),
  });
}

function validateTransportPayload0(payload, path) {
  const allowedKeys = new Set(['op', 'spec']);
  const unexpected = Object.keys(payload).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Transport payload rejects caller-supplied target facts, lost coordinates, lift completion, preservation, full-use, solver, search, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (!SEMANTIC_TRANSPORT_OPERATIONS0.includes(payload.op)) {
    return validationReject0(
      [...path, 'op'],
      'Transport operation is unsupported',
      {
        actual: payload.op,
        supportedOperations: [...SEMANTIC_TRANSPORT_OPERATIONS0],
      },
    );
  }
  const spec = validateSpec0(payload.spec, [...path, 'spec']);
  if (!spec.ok) return spec;
  if (payload.op !== spec.spec.operation) {
    return validationReject0(
      [...path, 'op'],
      'Transport payload operation must exactly match the transport specification',
      { expected: spec.spec.operation, actual: payload.op },
    );
  }
  return validationAccept0({
    kind: 'SemanticTransportPayload0NF',
    operation: payload.op,
    transportId: spec.spec.transportId,
  });
}

function validateCoordinate0(coordinate, path) {
  if (!isPlainObject0(coordinate)) {
    return validationReject0(path, 'Transport coordinate must be an object', {
      actual: typeof coordinate,
    });
  }
  const allowedKeys = new Set(['kind', 'version', 'index', 'id', 'role']);
  const unexpected = Object.keys(coordinate)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Transport coordinate rejects undeclared value, preservation, or obligation fields',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (coordinate.kind !== 'SemanticTransportCoordinate0') {
    return validationReject0(
      [...path, 'kind'],
      'Transport coordinate kind must be SemanticTransportCoordinate0',
      { actual: coordinate.kind },
    );
  }
  if (coordinate.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Transport coordinate version must be ${CHECKER_VERSION}`,
      { actual: coordinate.version },
    );
  }
  if (!Number.isSafeInteger(coordinate.index) || coordinate.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'Transport coordinate index must be a nonnegative safe integer',
      { actual: coordinate.index },
    );
  }
  if (!isIdentifier0(coordinate.id)) {
    return validationReject0(
      [...path, 'id'],
      'Transport coordinate id must be a canonical identifier',
      { actual: coordinate.id },
    );
  }
  if (!SEMANTIC_TRANSPORT_COORDINATE_ROLES0.includes(coordinate.role)) {
    return validationReject0(
      [...path, 'role'],
      'Transport coordinate role is unsupported',
      {
        actual: coordinate.role,
        supportedRoles: [...SEMANTIC_TRANSPORT_COORDINATE_ROLES0],
      },
    );
  }
  return validationAcceptWith0({
    kind: 'SemanticTransportCoordinate0NF',
    index: coordinate.index,
    id: coordinate.id,
    role: coordinate.role,
  }, { coordinate });
}

function validateCarrier0(carrier, path) {
  if (!isPlainObject0(carrier)) {
    return validationReject0(path, 'Transport carrier must be an object', {
      actual: typeof carrier,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'carrierId', 'mode', 'coordinates',
  ]);
  const unexpected = Object.keys(carrier).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Transport carrier rejects undeclared completeness, lift, projection, or preservation assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (carrier.kind !== 'SemanticTransportCarrier0') {
    return validationReject0(
      [...path, 'kind'],
      'Transport carrier kind must be SemanticTransportCarrier0',
      { actual: carrier.kind },
    );
  }
  if (carrier.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Transport carrier version must be ${CHECKER_VERSION}`,
      { actual: carrier.version },
    );
  }
  if (!isIdentifier0(carrier.carrierId)) {
    return validationReject0(
      [...path, 'carrierId'],
      'Transport carrierId must be a canonical identifier',
      { actual: carrier.carrierId },
    );
  }
  if (!SEMANTIC_TRANSPORT_MODES0.includes(carrier.mode)) {
    return validationReject0(
      [...path, 'mode'],
      'Transport carrier mode is unsupported',
      {
        actual: carrier.mode,
        supportedModes: [...SEMANTIC_TRANSPORT_MODES0],
      },
    );
  }
  if (!Array.isArray(carrier.coordinates)
      || carrier.coordinates.length === 0) {
    return validationReject0(
      [...path, 'coordinates'],
      'Transport carrier must contain a nonempty coordinate array',
      { actual: typeof carrier.coordinates },
    );
  }
  if (carrier.coordinates.length > MAX_COORDINATES) {
    return validationReject0(
      [...path, 'coordinates'],
      'Transport carrier exceeds maxCoordinates',
      { maxCoordinates: MAX_COORDINATES, actual: carrier.coordinates.length },
    );
  }
  const coordinateById = new Map();
  const indexById = new Map();
  for (let index = 0; index < carrier.coordinates.length; index += 1) {
    const checked = validateCoordinate0(
      carrier.coordinates[index],
      [...path, 'coordinates', index],
    );
    if (!checked.ok) return checked;
    if (checked.coordinate.index !== index) {
      return validationReject0(
        [...path, 'coordinates', index, 'index'],
        'Transport coordinate indices must be exact consecutive carrier coordinates',
        { expected: index, actual: checked.coordinate.index },
      );
    }
    if (coordinateById.has(checked.coordinate.id)) {
      return validationReject0(
        [...path, 'coordinates', index, 'id'],
        'Transport carrier coordinate ids must be unique',
        { id: checked.coordinate.id },
      );
    }
    coordinateById.set(checked.coordinate.id, checked.coordinate);
    indexById.set(checked.coordinate.id, index);
  }
  return validationAcceptWith0({
    kind: 'SemanticTransportCarrier0NF',
    carrierId: carrier.carrierId,
    mode: carrier.mode,
    coordinateCount: carrier.coordinates.length,
    coordinateIds: carrier.coordinates.map((coordinate) => coordinate.id),
    roles: carrier.coordinates.map((coordinate) => coordinate.role),
  }, {
    carrier,
    coordinateById,
    indexById,
  });
}

function validateMapEntry0(entry, path) {
  if (!isPlainObject0(entry)) {
    return validationReject0(path, 'Transport map entry must be an object', {
      actual: typeof entry,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'index', 'sourceCoordinateId', 'targetCoordinateId',
  ]);
  const unexpected = Object.keys(entry).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Transport map entry rejects undeclared preservation or completion assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (entry.kind !== 'SemanticTransportMapEntry0') {
    return validationReject0(
      [...path, 'kind'],
      'Transport map entry kind must be SemanticTransportMapEntry0',
      { actual: entry.kind },
    );
  }
  if (entry.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Transport map entry version must be ${CHECKER_VERSION}`,
      { actual: entry.version },
    );
  }
  if (!Number.isSafeInteger(entry.index) || entry.index < 0) {
    return validationReject0(
      [...path, 'index'],
      'Transport map entry index must be a nonnegative safe integer',
      { actual: entry.index },
    );
  }
  if (!isIdentifier0(entry.sourceCoordinateId)
      || !isIdentifier0(entry.targetCoordinateId)) {
    return validationReject0(
      path,
      'Transport map entry coordinate ids must be canonical identifiers',
      {
        sourceCoordinateId: entry.sourceCoordinateId,
        targetCoordinateId: entry.targetCoordinateId,
      },
    );
  }
  return validationAcceptWith0({
    kind: 'SemanticTransportMapEntry0NF',
    index: entry.index,
    sourceCoordinateId: entry.sourceCoordinateId,
    targetCoordinateId: entry.targetCoordinateId,
  }, { entry });
}

function validateSpec0(spec, path) {
  if (!isPlainObject0(spec)) {
    return validationReject0(path, 'Transport specification must be an object', {
      actual: typeof spec,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'transportId', 'operation',
    'sourceCarrier', 'targetCarrier', 'mapping',
  ]);
  const unexpected = Object.keys(spec).filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Transport specification rejects caller-supplied lost coordinates, lift completion, preservation, full-use, solver, search, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (spec.kind !== 'SemanticTransportSpec0') {
    return validationReject0(
      [...path, 'kind'],
      'Transport specification kind must be SemanticTransportSpec0',
      { actual: spec.kind },
    );
  }
  if (spec.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Transport specification version must be ${CHECKER_VERSION}`,
      { actual: spec.version },
    );
  }
  if (!isIdentifier0(spec.transportId)) {
    return validationReject0(
      [...path, 'transportId'],
      'Transport transportId must be a canonical identifier',
      { actual: spec.transportId },
    );
  }
  if (!SEMANTIC_TRANSPORT_OPERATIONS0.includes(spec.operation)) {
    return validationReject0(
      [...path, 'operation'],
      'Transport specification operation is unsupported',
      {
        actual: spec.operation,
        supportedOperations: [...SEMANTIC_TRANSPORT_OPERATIONS0],
      },
    );
  }
  const source = validateCarrier0(spec.sourceCarrier, [...path, 'sourceCarrier']);
  if (!source.ok) return source;
  const target = validateCarrier0(spec.targetCarrier, [...path, 'targetCarrier']);
  if (!target.ok) return target;
  if (!Array.isArray(spec.mapping)) {
    return validationReject0(
      [...path, 'mapping'],
      'Transport specification mapping must be an array',
      { actual: typeof spec.mapping },
    );
  }
  if (spec.mapping.length > MAX_COORDINATES) {
    return validationReject0(
      [...path, 'mapping'],
      'Transport specification mapping exceeds maxCoordinates',
      { maxCoordinates: MAX_COORDINATES, actual: spec.mapping.length },
    );
  }

  if (spec.operation === 'rename'
      && source.carrier.mode !== target.carrier.mode) {
    return validationReject0(
      [...path, 'operation'],
      'Transport rename requires source and target carriers in the same mode',
      { sourceMode: source.carrier.mode, targetMode: target.carrier.mode },
    );
  }
  if (spec.operation === 'project'
      && !(source.carrier.mode === 'full'
        && target.carrier.mode === 'quotient')) {
    return validationReject0(
      [...path, 'operation'],
      'Transport project requires a full source and quotient target carrier',
      { sourceMode: source.carrier.mode, targetMode: target.carrier.mode },
    );
  }
  if (spec.operation === 'lift'
      && !(source.carrier.mode === 'quotient'
        && target.carrier.mode === 'full')) {
    return validationReject0(
      [...path, 'operation'],
      'Transport lift requires a quotient source and full target carrier',
      { sourceMode: source.carrier.mode, targetMode: target.carrier.mode },
    );
  }

  const sourceIds = new Set();
  const targetIds = new Set();
  const sourceToTarget = new Map();
  const targetToSource = new Map();
  let previousSourceIndex = -1;
  let previousTargetIndex = -1;
  for (let index = 0; index < spec.mapping.length; index += 1) {
    const checked = validateMapEntry0(
      spec.mapping[index],
      [...path, 'mapping', index],
    );
    if (!checked.ok) return checked;
    const entry = checked.entry;
    if (entry.index !== index) {
      return validationReject0(
        [...path, 'mapping', index, 'index'],
        'Transport map entry indices must be exact consecutive coordinates',
        { expected: index, actual: entry.index },
      );
    }
    const sourceCoordinate = source.coordinateById.get(entry.sourceCoordinateId);
    const targetCoordinate = target.coordinateById.get(entry.targetCoordinateId);
    if (sourceCoordinate === undefined || targetCoordinate === undefined) {
      return validationReject0(
        [...path, 'mapping', index],
        'Transport map entries must reference declared source and target coordinates',
        {
          sourceCoordinateId: entry.sourceCoordinateId,
          targetCoordinateId: entry.targetCoordinateId,
        },
      );
    }
    if (sourceIds.has(entry.sourceCoordinateId)
        || targetIds.has(entry.targetCoordinateId)) {
      return validationReject0(
        [...path, 'mapping', index],
        'Transport mapping must be injective on source and target coordinates',
        {
          sourceCoordinateId: entry.sourceCoordinateId,
          targetCoordinateId: entry.targetCoordinateId,
        },
      );
    }
    const sourceIndex = source.indexById.get(entry.sourceCoordinateId);
    const targetIndex = target.indexById.get(entry.targetCoordinateId);
    if (sourceIndex <= previousSourceIndex || targetIndex <= previousTargetIndex) {
      return validationReject0(
        [...path, 'mapping', index],
        'Transport mapping must preserve source and target coordinate order',
        {
          previousSourceIndex,
          sourceIndex,
          previousTargetIndex,
          targetIndex,
        },
      );
    }
    if (sourceCoordinate.role !== targetCoordinate.role) {
      return validationReject0(
        [...path, 'mapping', index],
        'Transport mapping must preserve coordinate roles exactly',
        {
          sourceRole: sourceCoordinate.role,
          targetRole: targetCoordinate.role,
        },
      );
    }
    sourceIds.add(entry.sourceCoordinateId);
    targetIds.add(entry.targetCoordinateId);
    sourceToTarget.set(entry.sourceCoordinateId, entry.targetCoordinateId);
    targetToSource.set(entry.targetCoordinateId, entry.sourceCoordinateId);
    previousSourceIndex = sourceIndex;
    previousTargetIndex = targetIndex;
  }

  const sourceCount = source.carrier.coordinates.length;
  const targetCount = target.carrier.coordinates.length;
  if (spec.operation === 'rename'
      && !(spec.mapping.length === sourceCount
        && sourceCount === targetCount)) {
    return validationReject0(
      [...path, 'mapping'],
      'Transport rename requires an order-preserving bijection over both carriers',
      { mappingCount: spec.mapping.length, sourceCount, targetCount },
    );
  }
  if (spec.operation === 'project'
      && spec.mapping.length !== targetCount) {
    return validationReject0(
      [...path, 'mapping'],
      'Transport project must map every quotient target coordinate from the full source',
      { mappingCount: spec.mapping.length, targetCount },
    );
  }
  if (spec.operation === 'lift'
      && spec.mapping.length !== sourceCount) {
    return validationReject0(
      [...path, 'mapping'],
      'Transport lift must map every quotient source coordinate into the full target',
      { mappingCount: spec.mapping.length, sourceCount },
    );
  }

  const lostSourceCoordinateIds = source.carrier.coordinates
    .filter((coordinate) => !sourceIds.has(coordinate.id))
    .map((coordinate) => coordinate.id);
  const liftedTargetCoordinateIds = target.carrier.coordinates
    .filter((coordinate) => !targetIds.has(coordinate.id))
    .map((coordinate) => coordinate.id);
  return validationAcceptWith0({
    kind: 'SemanticTransportSpec0NF',
    transportId: spec.transportId,
    operation: spec.operation,
    sourceCarrierId: source.carrier.carrierId,
    targetCarrierId: target.carrier.carrierId,
    sourceMode: source.carrier.mode,
    targetMode: target.carrier.mode,
    mappingCount: spec.mapping.length,
    lostSourceCoordinateIds,
    liftedTargetCoordinateIds,
    orderPreserved: true,
    rolesPreserved: true,
  }, {
    spec,
    source,
    target,
    sourceToTarget,
    targetToSource,
    lostSourceCoordinateIds,
    liftedTargetCoordinateIds,
  });
}

function validateEvidenceJudgment0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(
      path,
      'Transport fact evidence must be a semantic judgment object',
      { actual: typeof judgment },
    );
  }
  if (typeof judgment.kind !== 'string'
      || !JUDGMENT_KIND_PATTERN.test(judgment.kind)
      || judgment.kind === 'SemanticTransportJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'Transport fact evidence must be a predecessor semantic judgment',
      { actual: judgment.kind },
    );
  }
  return validationAccept0({
    kind: 'SemanticTransportEvidenceJudgment0NF',
    judgmentKind: judgment.kind,
    digest: digestCanonical0(judgment),
  });
}

function validateConclusionShape0(judgment, path) {
  if (!isPlainObject0(judgment)) {
    return validationReject0(path, 'Transport conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  const allowedKeys = new Set([
    'kind', 'version', 'transportId', 'operation',
    'sourceCarrier', 'targetCarrier', 'mapping',
    'sourceFactProofIds', 'liftFactProofIds', 'targetFacts',
    'lostSourceCoordinateIds', 'liftedTargetCoordinateIds',
    'sourceCarrierDigest', 'targetCarrierDigest', 'mappingDigest',
    'sourceFactCount', 'targetFactCount',
    'orderPreserved', 'rolesPreserved',
    'exactSourceEvidenceCoverage', 'exactTargetFactCoverage',
    'projectionComparisonOnly', 'quotientResultCannotJustifyFullUse',
    'fullLiftEvidenceComplete', 'constructiveTargetUseAllowed',
    'constructiveFullUseAllowed', 'noImplicitDefaults',
    'terminalJudgmentComputed',
  ]);
  const unexpected = Object.keys(judgment)
    .filter((key) => !allowedKeys.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'Transport conclusion rejects undeclared readiness, preservation, lift, solver, search, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (judgment.kind !== 'SemanticTransportJudgment0') {
    return validationReject0(
      [...path, 'kind'],
      'Transport conclusion kind must be SemanticTransportJudgment0',
      { actual: judgment.kind },
    );
  }
  if (judgment.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `Transport conclusion version must be ${CHECKER_VERSION}`,
      { actual: judgment.version },
    );
  }
  for (const field of [
    'sourceFactProofIds',
    'liftFactProofIds',
    'targetFacts',
    'lostSourceCoordinateIds',
    'liftedTargetCoordinateIds',
  ]) {
    if (!Array.isArray(judgment[field])) {
      return validationReject0(
        [...path, field],
        `Transport conclusion ${field} must be an array`,
        { actual: typeof judgment[field] },
      );
    }
  }
  for (let index = 0; index < judgment.targetFacts.length; index += 1) {
    const fact = judgment.targetFacts[index];
    const factPath = [...path, 'targetFacts', index];
    if (!isPlainObject0(fact)) {
      return validationReject0(
        factPath,
        'Transport target fact must be an object',
        { actual: typeof fact },
      );
    }
    const allowedFactKeys = new Set([
      'kind', 'version', 'targetCoordinateId', 'targetRole',
      'sourceCoordinateId', 'evidenceProofId', 'judgment',
    ]);
    const unexpectedFactKeys = Object.keys(fact)
      .filter((key) => !allowedFactKeys.has(key));
    if (unexpectedFactKeys.length !== 0) {
      return validationReject0(
        [...factPath, unexpectedFactKeys[0]],
        'Transport target fact rejects undeclared preservation or completion fields',
        { unexpectedFields: unexpectedFactKeys.sort() },
      );
    }
    if (fact.kind !== 'SemanticTransportedFact0'
        || fact.version !== CHECKER_VERSION
        || !isIdentifier0(fact.targetCoordinateId)
        || !SEMANTIC_TRANSPORT_COORDINATE_ROLES0.includes(fact.targetRole)
        || !(fact.sourceCoordinateId === null
          || isIdentifier0(fact.sourceCoordinateId))
        || !isIdentifier0(fact.evidenceProofId)) {
      return validationReject0(
        factPath,
        'Transport target fact has invalid canonical fields',
        { actual: fact },
      );
    }
    const judgmentCheck = validateEvidenceJudgment0(
      fact.judgment,
      [...factPath, 'judgment'],
    );
    if (!judgmentCheck.ok) return judgmentCheck;
  }
  return validationAccept0({
    kind: 'SemanticTransportJudgmentShape0NF',
    transportId: judgment.transportId,
    operation: judgment.operation,
    targetFactCount: judgment.targetFacts.length,
  });
}

function checkTransportRule0(node, premises, path) {
  const specCheck = validateSpec0(
    node.Payload.spec,
    [...path, 'Payload', 'spec'],
  );
  if (!specCheck.ok) return specCheck;
  if (node.Payload.op !== specCheck.spec.operation) {
    return validationReject0(
      [...path, 'Payload', 'op'],
      'Transport node operation must exactly match its specification',
      { expected: specCheck.spec.operation, actual: node.Payload.op },
    );
  }
  const derived = deriveTransport0(
    specCheck,
    premises,
    node.Premises,
    path,
  );
  if (!derived.ok) return derived;
  if (!sameCanonical0(node.Conclusion, derived.judgment)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'Transport conclusion must exactly equal the computed carrier transport decision',
      { expected: derived.judgment, actual: node.Conclusion },
    );
  }
  return validationAccept0({
    kind: 'SemanticTransportRule0NF',
    ruleName: 'Transport',
    operation: specCheck.spec.operation,
    transportId: specCheck.spec.transportId,
    sourceMode: specCheck.source.carrier.mode,
    targetMode: specCheck.target.carrier.mode,
    sourceFactCount: specCheck.source.carrier.coordinates.length,
    targetFactCount: specCheck.target.carrier.coordinates.length,
    lostSourceCoordinateCount: specCheck.lostSourceCoordinateIds.length,
    liftedTargetCoordinateCount: specCheck.liftedTargetCoordinateIds.length,
    orderPreserved: true,
    rolesPreserved: true,
  });
}

function deriveTransport0(specCheck, premises, evidenceProofIds, path) {
  if (!Array.isArray(premises) || !Array.isArray(evidenceProofIds)) {
    return validationReject0(
      [...path, 'Premises'],
      'Transport requires premise and evidence-proof arrays',
      null,
    );
  }
  const sourceCoordinates = specCheck.source.carrier.coordinates;
  const liftedCoordinates = specCheck.target.carrier.coordinates.filter(
    (coordinate) => specCheck.liftedTargetCoordinateIds.includes(coordinate.id),
  );
  const expectedCount = sourceCoordinates.length
    + (specCheck.spec.operation === 'lift' ? liftedCoordinates.length : 0);
  if (premises.length !== expectedCount
      || evidenceProofIds.length !== expectedCount) {
    return validationReject0(
      [...path, 'Premises'],
      'Transport premises must contain every source fact and every required lift fact exactly once',
      {
        expected: expectedCount,
        actualPremises: premises.length,
        actualEvidenceProofIds: evidenceProofIds.length,
      },
    );
  }

  const sourceFactByCoordinate = new Map();
  const sourceProofByCoordinate = new Map();
  for (let index = 0; index < sourceCoordinates.length; index += 1) {
    const coordinate = sourceCoordinates[index];
    const evidence = readFactEvidence0(
      premises[index],
      evidenceProofIds[index],
      specCheck.source.carrier.carrierId,
      coordinate.id,
      [...path, 'Premises', index],
    );
    if (!evidence.ok) return evidence;
    sourceFactByCoordinate.set(coordinate.id, evidence.judgment);
    sourceProofByCoordinate.set(coordinate.id, evidence.proofId);
  }

  const liftFactByCoordinate = new Map();
  const liftProofByCoordinate = new Map();
  if (specCheck.spec.operation === 'lift') {
    for (let offset = 0; offset < liftedCoordinates.length; offset += 1) {
      const coordinate = liftedCoordinates[offset];
      const premiseIndex = sourceCoordinates.length + offset;
      const evidence = readFactEvidence0(
        premises[premiseIndex],
        evidenceProofIds[premiseIndex],
        specCheck.target.carrier.carrierId,
        coordinate.id,
        [...path, 'Premises', premiseIndex],
      );
      if (!evidence.ok) return evidence;
      liftFactByCoordinate.set(coordinate.id, evidence.judgment);
      liftProofByCoordinate.set(coordinate.id, evidence.proofId);
    }
  }

  const targetFacts = [];
  for (const targetCoordinate of specCheck.target.carrier.coordinates) {
    const sourceCoordinateId = specCheck.targetToSource.get(targetCoordinate.id)
      ?? null;
    const judgment = sourceCoordinateId === null
      ? liftFactByCoordinate.get(targetCoordinate.id)
      : sourceFactByCoordinate.get(sourceCoordinateId);
    const evidenceProofId = sourceCoordinateId === null
      ? liftProofByCoordinate.get(targetCoordinate.id)
      : sourceProofByCoordinate.get(sourceCoordinateId);
    if (judgment === undefined || evidenceProofId === undefined) {
      return validationReject0(
        [...path, 'Premises'],
        'Transport could not construct exact target fact coverage',
        {
          targetCoordinateId: targetCoordinate.id,
          sourceCoordinateId,
        },
      );
    }
    targetFacts.push(Object.freeze({
      kind: 'SemanticTransportedFact0',
      version: CHECKER_VERSION,
      targetCoordinateId: targetCoordinate.id,
      targetRole: targetCoordinate.role,
      sourceCoordinateId,
      evidenceProofId,
      judgment,
    }));
  }

  const operation = specCheck.spec.operation;
  const targetMode = specCheck.target.carrier.mode;
  const judgment = Object.freeze({
    kind: 'SemanticTransportJudgment0',
    version: CHECKER_VERSION,
    transportId: specCheck.spec.transportId,
    operation,
    sourceCarrier: specCheck.spec.sourceCarrier,
    targetCarrier: specCheck.spec.targetCarrier,
    mapping: specCheck.spec.mapping,
    sourceFactProofIds: Object.freeze(
      evidenceProofIds.slice(0, sourceCoordinates.length),
    ),
    liftFactProofIds: Object.freeze(
      operation === 'lift'
        ? evidenceProofIds.slice(sourceCoordinates.length)
        : [],
    ),
    targetFacts: Object.freeze(targetFacts),
    lostSourceCoordinateIds: Object.freeze([
      ...specCheck.lostSourceCoordinateIds,
    ]),
    liftedTargetCoordinateIds: Object.freeze([
      ...specCheck.liftedTargetCoordinateIds,
    ]),
    sourceCarrierDigest: digestCanonical0(specCheck.spec.sourceCarrier),
    targetCarrierDigest: digestCanonical0(specCheck.spec.targetCarrier),
    mappingDigest: digestCanonical0(specCheck.spec.mapping),
    sourceFactCount: sourceCoordinates.length,
    targetFactCount: targetFacts.length,
    orderPreserved: true,
    rolesPreserved: true,
    exactSourceEvidenceCoverage: true,
    exactTargetFactCoverage: true,
    projectionComparisonOnly: operation === 'project',
    quotientResultCannotJustifyFullUse: targetMode === 'quotient',
    fullLiftEvidenceComplete: operation === 'lift',
    constructiveTargetUseAllowed: operation !== 'project',
    constructiveFullUseAllowed:
      targetMode === 'full' && operation !== 'project',
    noImplicitDefaults: true,
    terminalJudgmentComputed: true,
  });
  return validationAcceptWith0({
    kind: 'SemanticTransportDerivation0NF',
    transportId: specCheck.spec.transportId,
    operation,
    sourceFactCount: sourceCoordinates.length,
    targetFactCount: targetFacts.length,
  }, { judgment });
}

function readFactEvidence0(
  premise,
  proofId,
  carrierId,
  coordinateId,
  path,
) {
  if (!isPlainObject0(premise)
      || premise.RuleName !== 'Record'
      || premise.operation !== 'intro') {
    return validationReject0(
      path,
      'Transport fact evidence premise must be accepted Record.intro evidence',
      {
        actualRule: premise?.RuleName ?? null,
        actualOperation: premise?.operation ?? null,
      },
    );
  }
  if (!isIdentifier0(proofId) || premise.id !== proofId) {
    return validationReject0(
      path,
      'Transport evidence proof id must exactly match the supplied premise id',
      { expected: premise.id, actual: proofId },
    );
  }
  const conclusion = premise.Conclusion;
  if (!isPlainObject0(conclusion)
      || conclusion.kind !== 'SemanticRecordJudgment0'
      || conclusion.version !== CHECKER_VERSION
      || conclusion.recordType !== factRecordType0(carrierId, coordinateId)
      || !Array.isArray(conclusion.fields)
      || conclusion.fields.length !== 1
      || conclusion.fields[0]?.kind !== 'SemanticRecordField0'
      || conclusion.fields[0]?.name !== 'fact') {
    return validationReject0(
      [...path, 'Conclusion'],
      'Transport fact evidence must be the exact carrier-coordinate fact record',
      {
        expectedRecordType: factRecordType0(carrierId, coordinateId),
        actual: conclusion,
      },
    );
  }
  const judgment = conclusion.fields[0].judgment;
  const judgmentCheck = validateEvidenceJudgment0(
    judgment,
    [...path, 'Conclusion', 'fields', 0, 'judgment'],
  );
  if (!judgmentCheck.ok) return judgmentCheck;
  const expected = makeSemanticTransportFactEvidence0({
    carrierId,
    coordinateId,
    judgment,
  });
  if (!sameCanonical0(conclusion, expected)) {
    return validationReject0(
      [...path, 'Conclusion'],
      'Transport fact evidence must exactly equal the canonical fact record',
      { expected, actual: conclusion },
    );
  }
  return validationAcceptWith0({
    kind: 'SemanticTransportFactEvidence0NF',
    proofId,
    carrierId,
    coordinateId,
    judgmentDigest: digestCanonical0(judgment),
  }, {
    proofId,
    judgment,
  });
}

function factRecordType0(carrierId, coordinateId) {
  return `TransportFact0.${carrierId}.${coordinateId}`;
}

function callBaseProofChecker0(nodes) {
  try {
    const record = CheckSemanticKernelProofIntArith0(
      makeSemanticProofDAG0(nodes),
    );
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: 'CheckSemanticKernelProofIntArith0 did not return a total accept/reject record',
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: 'CheckSemanticKernelProofIntArith0 threw instead of returning a reject record',
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
