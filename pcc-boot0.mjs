import {
  CheckVerifierFrag0,
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckDuplicateRows0,
  CheckRowKey0,
  ComputeRowKey0,
  DigestObject0,
} from './pcc-core.mjs';

const CHECKER_VERSION = 0;

const REQUIRED_BOOT0_FIELDS = [
  'ByteLang0',
  'Codec0',
  'Digest0',
  'IfaceDict0',
  'Sched0',
  'KernelSeed0',
  'B0',
  'BootAudit0',
];

const REQUIRED_ROW_FIELDS = [
  'PackageID',
  'SchemaID',
  'RawObj',
  'NormObj',
  'RowKey',
  'TransportProof',
  'CandidateRoutes',
  'ActiveRouteSet',
  'SelectedRoute',
  'ProofRef',
  'BoundsRef',
  'HashKey',
];

const REQUIRED_SCHEDULE_CORE = Object.freeze({
  B0: 64,
  K0: 512,
  R0: 64,
  H0: 128,
  O0: 64,
  Rel0: 16,
});

const REQUIRED_KERNEL_RULES = [
  'Eq',
  'Subst',
  'Record',
  'DAGInd',
  'LedgerInd',
  'OblTopoInd',
  'TraceInd',
  'FiniteExhaust',
  'DPInd',
  'Hall',
  'RankInd',
  'MinCounterexample',
  'IntArith',
  'Transport',
  'TruthVec',
  'FiniteRel',
];

const REQUIRED_FORBIDDEN_SYMBOLS = [
  'µ',
  'µ*',
  'µ#',
  'Can',
  'argmin',
  'maxG',
  'minimumEquivalent',
  'optimalCircuit',
  'exactMinSearch',
  'canonicalMinimizer',
  'maximizeGain',
];

export function makeBootRow0({
  PackageID,
  SchemaID,
  KindKey = 'infra',
  ArityKey = 0,
  ModeKey = 'Full',
  FrontKey = 'front',
  SemanticKey = 'semantic',
  IncidenceKey = 'incidence',
  DependencyKey = 'dependency',
  ProfileKey = 'profile',
  ChargeKey = 'charge',
  ObligationKey = 'obligation',
  BudgetKey = 'budget',
  ActivationKey = 'activation',
  RankKey = 'rank',
  PayloadKey = 'payload',
  RawObj,
  NormObj,
  TransportProof,
  CandidateRoutes,
  ActiveRouteSet,
  SelectedRoute = 'Neutral',
  ProofRef,
  BoundsRef,
  IfaceHash = 'IfaceDict0.synthetic',
}) {
  if (!isNonEmptyString(PackageID)) {
    throw new TypeError('makeBootRow0 requires a non-empty PackageID');
  }

  if (!isNonEmptyString(SchemaID)) {
    throw new TypeError('makeBootRow0 requires a non-empty SchemaID');
  }

  const row = {
    IfaceHash,
    PackageID,
    SchemaID,
    RawObj: RawObj ?? {
      tag: 'RawObj0',
      package: PackageID,
      schema: SchemaID,
      kind: KindKey,
    },
    NormObj: NormObj ?? RawObj ?? {
      tag: 'RawObj0',
      package: PackageID,
      schema: SchemaID,
      kind: KindKey,
    },
    KindKey,
    ArityKey,
    ModeKey,
    FrontKey,
    SemanticKey,
    IncidenceKey,
    DependencyKey,
    ProfileKey,
    ChargeKey,
    ObligationKey,
    BudgetKey,
    ActivationKey,
    RankKey,
    PayloadKey,
    TransportProof: TransportProof ?? {
      tag: 'TransportProof0',
      kind: 'identity',
    },
    CandidateRoutes: CandidateRoutes ?? [SelectedRoute],
    ActiveRouteSet: ActiveRouteSet ?? [SelectedRoute],
    SelectedRoute,
    ProofRef: ProofRef ?? {
      tag: 'ProofRef0',
      id: `${PackageID}.${SchemaID}.${KindKey}.proof`,
    },
    BoundsRef: BoundsRef ?? {
      tag: 'BoundsRef0',
      id: `${PackageID}.${SchemaID}.${KindKey}.bounds`,
    },
  };

  row.RowKey = ComputeRowKey0(row);
  row.HashKey = DigestObject0(row.RowKey);

  return row;
}

export async function CheckBoot0(boot) {
  const checker = 'CheckBoot0';
  const ledger = [];

  const shape = validateBoot0Shape(boot);

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const validations = [
    ['ByteLang0', validateByteLang0(boot.ByteLang0)],
    ['Codec0', validateCodec0(boot.Codec0)],
    ['Digest0', validateDigest0(boot.Digest0)],
    ['IfaceDict0', validateIfaceDict0(boot.IfaceDict0)],
    ['Sched0', validateSched0(boot.Sched0)],
    ['KernelSeed0', validateKernelSeed0(boot.KernelSeed0)],
    ['PiBoot', validatePiBoot0(getPiBoot0(boot))],
  ];

  for (const [name, result] of validations) {
    ledger.push({
      phase: name,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.${name}`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const batchResult = await CheckBootBatch0(boot.B0);

  ledger.push({
    phase: 'CheckBootBatch0',
    status: isRejectRecord(batchResult) ? 'fail' : 'pass',
    digest: batchResult.Digest ?? batchResult.digest,
  });

  if (isRejectRecord(batchResult)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.B0`,
      path: ['B0'],
      witness: {
        reason: 'CheckBootBatch0 rejected',
        inner: compactReject0(batchResult),
      },
      ledger,
    });
  }

  const auditResult = await CheckBootAudit0(boot.BootAudit0);

  ledger.push({
    phase: 'CheckBootAudit0',
    status: isRejectRecord(auditResult) ? 'fail' : 'pass',
    digest: auditResult.Digest ?? auditResult.digest,
  });

  if (isRejectRecord(auditResult)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.BootAudit0`,
      path: ['BootAudit0'],
      witness: {
        reason: 'CheckBootAudit0 rejected',
        inner: compactReject0(auditResult),
      },
      ledger,
    });
  }

  const nf = {
    kind: 'Boot0NF',
    checker,
    version: CHECKER_VERSION,
    byteLangDigest: digestCanonical0(boot.ByteLang0),
    codecDigest: digestCanonical0(boot.Codec0),
    digestDigest: digestCanonical0(boot.Digest0),
    ifaceDigest: digestCanonical0(boot.IfaceDict0),
    schedDigest: digestCanonical0(boot.Sched0),
    kernelSeedDigest: digestCanonical0(boot.KernelSeed0),
    piBootDigest: digestCanonical0(getPiBoot0(boot)),
    bootBatchDigest: batchResult.Digest ?? batchResult.digest,
    bootAuditDigest: auditResult.Digest ?? auditResult.digest,
    rowCount: batchResult.NF?.rowCount ?? batchResult.nf?.rowCount ?? null,
    kernelRuleCount: boot.KernelSeed0.rules.length,
    scheduleCore: normalizeScheduleCore0(boot.Sched0),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckBootBatch0(batch) {
  const checker = 'CheckBootBatch0';
  const ledger = [];

  const shape = validateBatchShape0(batch);

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const rows = getBatchRows0(batch);

  for (let index = 0; index < rows.length; index += 1) {
    const rowResult = validateBootRow0(rows[index], index);

    ledger.push({
      phase: 'row',
      index,
      status: rowResult.ok ? 'pass' : 'fail',
      digest: digestCanonical0(rowResult.nf ?? rowResult.witness ?? null),
    });

    if (!rowResult.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.row.${String(index).padStart(4, '0')}`,
        path: rowResult.path,
        witness: rowResult.witness,
        ledger,
      });
    }
  }

  const duplicateResult = CheckDuplicateRows0(rows);

  ledger.push({
    phase: 'duplicateRows',
    status: isRejectRecord(duplicateResult) ? 'fail' : 'pass',
    digest: digestCanonical0(duplicateResult),
  });

  if (isRejectRecord(duplicateResult)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.duplicateRows`,
      path: ['rows'],
      witness: {
        reason: 'duplicate row conflict',
        inner: compactReject0(duplicateResult),
      },
      ledger,
    });
  }

  const nf = {
    kind: 'BootBatch0NF',
    checker,
    version: CHECKER_VERSION,
    batchId: getBatchId0(batch),
    rowCount: rows.length,
    packages: sortedUnique0(rows.map((row) => row.PackageID)),
    schemas: sortedUnique0(rows.map((row) => `${row.PackageID}:${row.SchemaID}`)),
    rowDigests: rows.map((row, index) => ({
      index,
      packageId: row.PackageID,
      schemaId: row.SchemaID,
      selectedRoute: row.SelectedRoute,
      rowKeyDigest: digestCanonical0(row.RowKey),
      hashKey: row.HashKey,
    })),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckBootAudit0(audit) {
  const checker = 'CheckBootAudit0';
  const ledger = [];

  if (isAcceptRecord(audit) && audit.checker === 'CheckVerifierFrag0') {
    const nf = {
      kind: 'BootAudit0NF',
      checker,
      version: CHECKER_VERSION,
      auditKind: 'precomputed',
      verifierDigest: audit.Digest ?? audit.digest,
    };

    return makeAcceptRecord({
      checker,
      nf,
      ledger,
    });
  }

  if (!isPlainObject(audit) || !Array.isArray(audit.cases)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: [],
      witness: {
        reason: 'BootAudit0 must be a VerifierFrag0 suite or accepted CheckVerifierFrag0 record',
      },
      ledger,
    });
  }

  const verifierResult = await CheckVerifierFrag0(audit);

  ledger.push({
    phase: 'CheckVerifierFrag0',
    status: isRejectRecord(verifierResult) ? 'fail' : 'pass',
    digest: verifierResult.Digest ?? verifierResult.digest,
  });

  if (isRejectRecord(verifierResult)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.audit`,
      path: ['BootAudit0'],
      witness: {
        reason: 'VerifierFrag0 audit rejected',
        inner: compactReject0(verifierResult),
      },
      ledger,
    });
  }

  const nf = {
    kind: 'BootAudit0NF',
    checker,
    version: CHECKER_VERSION,
    auditKind: 'suite',
    suiteId: audit.suiteId ?? 'BootAudit0',
    verifierDigest: verifierResult.Digest ?? verifierResult.digest,
    caseCount: verifierResult.NF?.caseCount ?? verifierResult.nf?.caseCount ?? audit.cases.length,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateBoot0Shape(boot) {
  if (!isPlainObject(boot)) {
    return validationReject([], 'Boot0 must be an object', {
      actual: typeof boot,
    });
  }

  if (boot.kind !== undefined && boot.kind !== 'Boot0') {
    return validationReject(['kind'], 'Boot0 kind must be Boot0 when present', {
      actual: boot.kind,
    });
  }

  if (boot.version !== undefined && boot.version !== CHECKER_VERSION) {
    return validationReject(['version'], `Boot0 version must be ${CHECKER_VERSION} when present`, {
      actual: boot.version,
    });
  }

  for (const field of REQUIRED_BOOT0_FIELDS) {
    if (!Object.prototype.hasOwnProperty.call(boot, field)) {
      return validationReject([field], 'Boot0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiBoot0(boot) === undefined) {
    return validationReject(['PiBoot'], 'Boot0 is missing PiBoot or Πboot', null);
  }

  return validationAccept({
    kind: 'Boot0ShapeNF',
  });
}

function validateBatchShape0(batch) {
  if (Array.isArray(batch)) {
    return validationAccept({
      kind: 'BootBatch0ShapeNF',
      form: 'array',
    });
  }

  if (!isPlainObject(batch)) {
    return validationReject([], 'BootBatch0 must be an object or row array', {
      actual: typeof batch,
    });
  }

  if (batch.kind !== undefined && batch.kind !== 'BootBatch0') {
    return validationReject(['kind'], 'BootBatch0 kind must be BootBatch0 when present', {
      actual: batch.kind,
    });
  }

  if (batch.version !== undefined && batch.version !== CHECKER_VERSION) {
    return validationReject(['version'], `BootBatch0 version must be ${CHECKER_VERSION} when present`, {
      actual: batch.version,
    });
  }

  if (!Array.isArray(getBatchRows0(batch))) {
    return validationReject(['rows'], 'BootBatch0 rows must be an array', {
      actual: typeof getBatchRows0(batch),
    });
  }

  return validationAccept({
    kind: 'BootBatch0ShapeNF',
    form: 'object',
    batchId: getBatchId0(batch),
  });
}

function validateBootRow0(row, index) {
  if (!isPlainObject(row)) {
    return validationReject(['rows', index], 'row must be an object', {
      actual: typeof row,
    });
  }

  for (const field of REQUIRED_ROW_FIELDS) {
    if (!Object.prototype.hasOwnProperty.call(row, field)) {
      return validationReject(['rows', index, field], 'row is missing a required field', {
        field,
      });
    }
  }

  if (!isNonEmptyString(row.PackageID)) {
    return validationReject(['rows', index, 'PackageID'], 'PackageID must be a non-empty string', {
      actual: row.PackageID,
    });
  }

  if (!isNonEmptyString(row.SchemaID)) {
    return validationReject(['rows', index, 'SchemaID'], 'SchemaID must be a non-empty string', {
      actual: row.SchemaID,
    });
  }

  if (!Array.isArray(row.CandidateRoutes)) {
    return validationReject(['rows', index, 'CandidateRoutes'], 'CandidateRoutes must be an array', null);
  }

  if (!Array.isArray(row.ActiveRouteSet)) {
    return validationReject(['rows', index, 'ActiveRouteSet'], 'ActiveRouteSet must be an array', null);
  }

  if (!row.ActiveRouteSet.some((route) => stableStringify0(route) === stableStringify0(row.SelectedRoute))) {
    return validationReject(['rows', index, 'SelectedRoute'], 'SelectedRoute must be active', {
      selectedRoute: row.SelectedRoute,
      activeRouteSet: row.ActiveRouteSet,
    });
  }

  const rowKeyResult = CheckRowKey0(row, row.RowKey);

  if (isRejectRecord(rowKeyResult)) {
    return validationReject(['rows', index, 'RowKey'], 'row key check rejected', {
      inner: compactReject0(rowKeyResult),
    });
  }

  const expectedHashKey = DigestObject0(row.RowKey);

  if (!isPlainObject(row.HashKey) || row.HashKey.hex !== expectedHashKey.hex) {
    return validationReject(['rows', index, 'HashKey'], 'HashKey must be the digest of RowKey', {
      expected: expectedHashKey,
      actual: row.HashKey,
    });
  }

  return validationAccept({
    kind: 'BootRow0NF',
    index,
    packageId: row.PackageID,
    schemaId: row.SchemaID,
    rowKeyDigest: digestCanonical0(row.RowKey),
    hashKey: row.HashKey,
  });
}

function validateByteLang0(byteLang) {
  if (!isPlainObject(byteLang)) {
    return validationReject(['ByteLang0'], 'ByteLang0 must be an object', null);
  }

  if (byteLang.kind !== undefined && byteLang.kind !== 'ByteLang0') {
    return validationReject(['ByteLang0', 'kind'], 'ByteLang0 kind must be ByteLang0 when present', {
      actual: byteLang.kind,
    });
  }

  if (byteLang.version !== undefined && byteLang.version !== CHECKER_VERSION) {
    return validationReject(['ByteLang0', 'version'], `ByteLang0 version must be ${CHECKER_VERSION} when present`, {
      actual: byteLang.version,
    });
  }

  for (const field of ['tags', 'sorts', 'constructors', 'records']) {
    if (!isPlainObject(byteLang[field])) {
      return validationReject(['ByteLang0', field], `ByteLang0.${field} must be an object`, {
        actual: typeof byteLang[field],
      });
    }
  }

  const duplicateTagValue = firstDuplicateValue0(byteLang.tags);

  if (duplicateTagValue !== null) {
    return validationReject(['ByteLang0', 'tags'], 'ByteLang0 tags must have unique values', {
      value: duplicateTagValue,
    });
  }

  return validationAccept({
    kind: 'ByteLang0NF',
    tagCount: Object.keys(byteLang.tags).length,
    sortCount: Object.keys(byteLang.sorts).length,
    constructorCount: Object.keys(byteLang.constructors).length,
    recordCount: Object.keys(byteLang.records).length,
  });
}

function validateCodec0(codec) {
  if (!isPlainObject(codec)) {
    return validationReject(['Codec0'], 'Codec0 must be an object', null);
  }

  if (codec.kind !== undefined && codec.kind !== 'Codec0') {
    return validationReject(['Codec0', 'kind'], 'Codec0 kind must be Codec0 when present', {
      actual: codec.kind,
    });
  }

  if (codec.version !== undefined && codec.version !== CHECKER_VERSION) {
    return validationReject(['Codec0', 'version'], `Codec0 version must be ${CHECKER_VERSION} when present`, {
      actual: codec.version,
    });
  }

  return validationAccept({
    kind: 'Codec0NF',
    canonical: codec.canonical !== false,
  });
}

function validateDigest0(digest) {
  if (!isPlainObject(digest)) {
    return validationReject(['Digest0'], 'Digest0 must be an object', null);
  }

  if (digest.kind !== undefined && digest.kind !== 'Digest0') {
    return validationReject(['Digest0', 'kind'], 'Digest0 kind must be Digest0 when present', {
      actual: digest.kind,
    });
  }

  if (digest.version !== undefined && digest.version !== CHECKER_VERSION) {
    return validationReject(['Digest0', 'version'], `Digest0 version must be ${CHECKER_VERSION} when present`, {
      actual: digest.version,
    });
  }

  if (digest.alg !== undefined && digest.alg !== 'SHA256') {
    return validationReject(['Digest0', 'alg'], 'Digest0 algorithm must be SHA256 when present', {
      actual: digest.alg,
    });
  }

  return validationAccept({
    kind: 'Digest0NF',
    alg: digest.alg ?? 'SHA256',
  });
}

function validateIfaceDict0(iface) {
  if (!isPlainObject(iface)) {
    return validationReject(['IfaceDict0'], 'IfaceDict0 must be an object', null);
  }

  if (iface.kind !== undefined && iface.kind !== 'IfaceDict0') {
    return validationReject(['IfaceDict0', 'kind'], 'IfaceDict0 kind must be IfaceDict0 when present', {
      actual: iface.kind,
    });
  }

  if (iface.version !== undefined && iface.version !== CHECKER_VERSION) {
    return validationReject(['IfaceDict0', 'version'], `IfaceDict0 version must be ${CHECKER_VERSION} when present`, {
      actual: iface.version,
    });
  }

  if (!Array.isArray(iface.forbiddenSymbols)) {
    return validationReject(['IfaceDict0', 'forbiddenSymbols'], 'IfaceDict0 forbiddenSymbols must be an array', null);
  }

  for (const symbol of REQUIRED_FORBIDDEN_SYMBOLS) {
    if (!iface.forbiddenSymbols.includes(symbol)) {
      return validationReject(['IfaceDict0', 'forbiddenSymbols'], 'IfaceDict0 is missing a forbidden executable symbol', {
        symbol,
      });
    }
  }

  return validationAccept({
    kind: 'IfaceDict0NF',
    forbiddenSymbolCount: iface.forbiddenSymbols.length,
  });
}

function validateSched0(schedule) {
  if (!isPlainObject(schedule)) {
    return validationReject(['Sched0'], 'Sched0 must be an object', null);
  }

  if (schedule.kind !== undefined && schedule.kind !== 'Sched0') {
    return validationReject(['Sched0', 'kind'], 'Sched0 kind must be Sched0 when present', {
      actual: schedule.kind,
    });
  }

  if (schedule.version !== undefined && schedule.version !== CHECKER_VERSION) {
    return validationReject(['Sched0', 'version'], `Sched0 version must be ${CHECKER_VERSION} when present`, {
      actual: schedule.version,
    });
  }

  const core = normalizeScheduleCore0(schedule);

  if (!isPlainObject(core)) {
    return validationReject(['Sched0', 'core'], 'Sched0 core must be an object', null);
  }

  for (const [key, expected] of Object.entries(REQUIRED_SCHEDULE_CORE)) {
    if (core[key] !== expected) {
      return validationReject(['Sched0', 'core', key], 'Sched0 core constant mismatch', {
        expected,
        actual: core[key],
      });
    }
  }

  return validationAccept({
    kind: 'Sched0NF',
    core,
  });
}

function validateKernelSeed0(kernelSeed) {
  if (!isPlainObject(kernelSeed)) {
    return validationReject(['KernelSeed0'], 'KernelSeed0 must be an object', null);
  }

  if (kernelSeed.kind !== undefined && kernelSeed.kind !== 'KernelSeed0') {
    return validationReject(['KernelSeed0', 'kind'], 'KernelSeed0 kind must be KernelSeed0 when present', {
      actual: kernelSeed.kind,
    });
  }

  if (kernelSeed.version !== undefined && kernelSeed.version !== CHECKER_VERSION) {
    return validationReject(['KernelSeed0', 'version'], `KernelSeed0 version must be ${CHECKER_VERSION} when present`, {
      actual: kernelSeed.version,
    });
  }

  if (!Array.isArray(kernelSeed.rules)) {
    return validationReject(['KernelSeed0', 'rules'], 'KernelSeed0 rules must be an array', null);
  }

  for (const rule of REQUIRED_KERNEL_RULES) {
    if (!kernelSeed.rules.includes(rule)) {
      return validationReject(['KernelSeed0', 'rules'], 'KernelSeed0 is missing a required primitive rule', {
        rule,
      });
    }
  }

  return validationAccept({
    kind: 'KernelSeed0NF',
    ruleCount: kernelSeed.rules.length,
  });
}

function validatePiBoot0(piBoot) {
  if (!isPlainObject(piBoot)) {
    return validationReject(['PiBoot'], 'PiBoot must be an object', null);
  }

  const kind = piBoot.kind ?? piBoot.tag;

  if (kind !== undefined && kind !== 'PiBoot0' && kind !== 'Πboot') {
    return validationReject(['PiBoot', 'kind'], 'PiBoot kind must be PiBoot0 or Πboot when present', {
      actual: kind,
    });
  }

  return validationAccept({
    kind: 'PiBoot0NF',
    digest: digestCanonical0(piBoot),
  });
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
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

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

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

function validationAccept(nf) {
  return {
    ok: true,
    nf,
  };
}

function validationReject(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function getPiBoot0(boot) {
  return boot.PiBoot ?? boot['Πboot'] ?? boot.piBoot;
}

function getBatchRows0(batch) {
  if (Array.isArray(batch)) {
    return batch;
  }

  return batch.rows ?? batch.Rows;
}

function getBatchId0(batch) {
  if (Array.isArray(batch)) {
    return 'B0';
  }

  return batch.batchId ?? batch.BatchID ?? batch.id ?? 'B0';
}

function normalizeScheduleCore0(schedule) {
  return schedule.core ?? schedule.Core;
}

function isAcceptRecord(value) {
  return classifyRecord0(value) === 'accept';
}

function isRejectRecord(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function firstDuplicateValue0(record) {
  const seen = new Set();

  for (const value of Object.values(record)) {
    const key = stableStringify0(value);

    if (seen.has(key)) {
      return value;
    }

    seen.add(key);
  }

  return null;
}

function sortedUnique0(values) {
  return Array.from(new Set(values.map((value) => String(value)))).sort();
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}