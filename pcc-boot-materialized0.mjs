import fs from 'node:fs/promises';
import path from 'node:path';
import { createHash } from 'node:crypto';

import {
  CheckBoot0,
  CheckBootAudit0,
  CheckBootBatch0,
  makeBootstrapB0Rows0,
} from './pcc-boot0.mjs';

import {
  CheckVerifierFrag0,
  digestCanonical0,
  makeAcceptCase,
  makeRejectCase,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_BOOT0_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export const MATERIALIZED_BOOT0_REQUIRED_FILES0 = Object.freeze([
  'Boot0.json',
  'MaterializedBoot0.check.json',
]);

export const MATERIALIZED_BOOT0_KERNEL_RULES0 = Object.freeze([
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
]);

export const MATERIALIZED_BOOT0_FORBIDDEN_SYMBOLS0 = Object.freeze([
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
]);

export const MATERIALIZED_BOOT0_PUBLIC_CONSTRUCTORS0 = Object.freeze([
  'Gain',
  'Minimum',
  'ZeroSlack',
  'NoBudget',
  'NoHereditary',
  'SelectorSilent',
  'Faithful',
  'Token',
]);

export function makeMaterializedByteLang0(overrides = {}) {
  return {
    kind: 'ByteLang0',
    version: CHECKER_VERSION,
    tags: {
      Boot0: 0x0001,
      BootBatch0: 0x0002,
      Row0: 0x0003,
      Digest0: 0x0004,
      IfaceDict0: 0x0005,
      Sched0: 0x0006,
      KernelSeed0: 0x0007,
      BootAudit0: 0x0008,
      PiBoot0: 0x0009,
      ProofRef0: 0x000a,
      BoundsRef0: 0x000b,
      TransportProof0: 0x000c,
    },
    sorts: {
      Unit: 'Unit',
      Name: 'Name',
      Record: 'Record',
      Row: 'Row',
      Digest: 'Digest',
      Route: 'Route',
      ProofRef: 'ProofRef',
      BoundsRef: 'BoundsRef',
    },
    constructors: {
      accept: 'accept',
      reject: 'reject',
      row: 'row',
      digest: 'digest',
      proofRef: 'proofRef',
      boundsRef: 'boundsRef',
      transport: 'transport',
    },
    records: {
      Boot0: 9,
      BootBatch0: 3,
      Row0: 12,
      Digest0: 4,
      IfaceDict0: 4,
      Sched0: 3,
      KernelSeed0: 3,
      BootAudit0: 3,
      PiBoot0: 4,
    },
    ...overrides,
  };
}

export function makeMaterializedCodec0(overrides = {}) {
  return {
    kind: 'Codec0',
    version: CHECKER_VERSION,
    canonical: true,
    naturalEncoding: 'u32be-length-shortest-big-endian-magnitude',
    integerEncoding: 'sign-byte-plus-canonical-natural-no-negative-zero',
    stringEncoding: 'utf8-nfc-length-prefixed',
    topLevelConsumesAllBytes: true,
    normalFormSerialization: 'canonical-json-v0',
    ...overrides,
  };
}

export function makeMaterializedDigest0(overrides = {}) {
  return {
    kind: 'Digest0',
    version: CHECKER_VERSION,
    alg: 'SHA256',
    bytes: 'canonical-json-v0',
    digestEqualityIsNotObjectEquality: true,
    fullKeyComparisonAfterHashLookup: true,
    ...overrides,
  };
}

export function makeMaterializedIfaceDict0(overrides = {}) {
  return {
    kind: 'IfaceDict0',
    version: CHECKER_VERSION,
    forbiddenSymbols: [...MATERIALIZED_BOOT0_FORBIDDEN_SYMBOLS0],
    publicConstructors: [...MATERIALIZED_BOOT0_PUBLIC_CONSTRUCTORS0],
    criticalKinds: [
      'CritC',
      'Q',
      'E',
      'L',
      'X1',
      'X2',
      'X3',
      'X4',
    ],
    routeTokens: [
      'UnaryWindow',
      'BCLeak',
      'HNShape',
      'BudgetShape',
      'SelectorSeed',
      'ExactRoute',
      'StrictDescent',
    ],
    ...overrides,
  };
}

export function makeMaterializedSched0(overrides = {}) {
  return {
    kind: 'Sched0',
    version: CHECKER_VERSION,
    core: {
      B0: 64,
      K0: 512,
      R0: 64,
      H0: 128,
      O0: 64,
      Rel0: 16,
    },
    packageScaleFactors: {
      FT: 1,
      X: 2,
      Splice: 2,
      BC: 4,
      UN: 4,
      HN: 8,
      BUD: 8,
      RW: 8,
      BN: 8,
      PkgC: 16,
      Packet: 16,
      R: 16,
    },
    selectorBounds: {
      bH: 8,
      bTheta: 12,
      polynomialExponent: 36,
    },
    ...overrides,
  };
}

export function makeMaterializedKernelSeed0(overrides = {}) {
  return {
    kind: 'KernelSeed0',
    version: CHECKER_VERSION,
    rules: [...MATERIALIZED_BOOT0_KERNEL_RULES0],
    proofNodeKinds: [
      'PrimitiveRule',
      'SigmaInstance',
      'ReflectionInstance',
      'RowProof',
      'PackageTheorem',
    ],
    proofReferencePolicy: {
      rejectsOpaqueProofBlobs: true,
      requiresTypedAcyclicRefs: true,
      hashIndependent: true,
    },
    ...overrides,
  };
}

export async function makeMaterializedBoot0(overrides = {}) {
  const ByteLang0 = overrides.ByteLang0 ?? makeMaterializedByteLang0();
  const Codec0 = overrides.Codec0 ?? makeMaterializedCodec0();
  const Digest0 = overrides.Digest0 ?? makeMaterializedDigest0();
  const IfaceDict0 = overrides.IfaceDict0 ?? makeMaterializedIfaceDict0();
  const Sched0 = overrides.Sched0 ?? makeMaterializedSched0();
  const KernelSeed0 = overrides.KernelSeed0 ?? makeMaterializedKernelSeed0();

  const ifaceDigest = digestCanonical0(IfaceDict0);
  const rows = makeBootstrapB0Rows0({
    IfaceHash: ifaceDigest.hex,
    SelectedRoute: 'Accept',
  });

  const B0 = overrides.B0 ?? {
    kind: 'BootBatch0',
    version: CHECKER_VERSION,
    batchId: 'B0',
    rows,
  };

  const auditSuite = makeMaterializedBootAuditSuite0({
    B0,
  });

  const BootAudit0 = overrides.BootAudit0 ?? await CheckVerifierFrag0(auditSuite);

  const PiBoot = overrides.PiBoot ?? {
    kind: 'PiBoot0',
    version: CHECKER_VERSION,
    materialized: true,
    externalJson: true,
    note: 'materialized bootstrap proof references',
    refs: [
      {
        label: 'ByteLang0',
        digest: digestCanonical0(ByteLang0),
      },
      {
        label: 'Codec0',
        digest: digestCanonical0(Codec0),
      },
      {
        label: 'Digest0',
        digest: digestCanonical0(Digest0),
      },
      {
        label: 'IfaceDict0',
        digest: ifaceDigest,
      },
      {
        label: 'Sched0',
        digest: digestCanonical0(Sched0),
      },
      {
        label: 'KernelSeed0',
        digest: digestCanonical0(KernelSeed0),
      },
      {
        label: 'B0',
        digest: digestCanonical0(B0),
      },
      {
        label: 'BootAudit0',
        digest: BootAudit0.Digest ?? BootAudit0.digest ?? digestCanonical0(BootAudit0),
      },
    ],
  };

  return {
    kind: 'Boot0',
    version: CHECKER_VERSION,
    ByteLang0,
    Codec0,
    Digest0,
    IfaceDict0,
    Sched0,
    KernelSeed0,
    B0,
    BootAudit0,
    PiBoot,
    ...withoutBootOverrideFields0(overrides),
  };
}

export function makeMaterializedBootAuditSuite0({
  B0,
} = {}) {
  if (!isPlainObject(B0)) {
    throw new TypeError('makeMaterializedBootAuditSuite0 requires a BootBatch0 object');
  }

  const rows = Array.isArray(B0.rows) ? B0.rows : [];
  const missingCoverageRows = rows.slice(1);
  const hashKeyTamperRows = rows.length === 0
    ? []
    : [
        {
          ...rows[0],
          HashKey: {
            ...rows[0].HashKey,
            hex: '0000000000000000000000000000000000000000000000000000000000000000',
          },
        },
        ...rows.slice(1),
      ];

  return {
    kind: 'VerifierFrag0',
    version: CHECKER_VERSION,
    suiteId: 'boot0.materialized.audit',
    cases: [
      makeAcceptCase({
        id: 'boot0.materialized.b0.accepts',
        target: 'CheckBootBatch0',
        description: 'materialized B0 accepts as the first concrete bootstrap row batch',
        run: () => CheckBootBatch0(B0),
      }),
      makeRejectCase({
        id: 'boot0.materialized.b0.rejects.missing.coverage',
        target: 'CheckBootBatch0',
        description: 'materialized B0 rejects when a required bootstrap row family is absent',
        run: () => CheckBootBatch0({
          ...B0,
          rows: missingCoverageRows,
        }),
      }),
      makeRejectCase({
        id: 'boot0.materialized.b0.rejects.hashkey.tamper',
        target: 'CheckBootBatch0',
        description: 'materialized B0 rejects when a displayed row hash no longer matches its row key',
        run: () => CheckBootBatch0({
          ...B0,
          rows: hashKeyTamperRows,
        }),
      }),
    ],
  };
}

export async function CheckMaterializedBoot0(boot, config = {}) {
  const checker = 'CheckMaterializedBoot0';
  const ledger = [];

  const bootRecord = await CheckBoot0(boot);
  const bootResult = recordToValidation0(bootRecord, ['Boot0']);

  ledger.push({
    phase: 'CheckBoot0',
    status: bootResult.ok ? 'pass' : 'fail',
    digest: bootRecord.Digest ?? bootRecord.digest ?? digestCanonical0(bootRecord),
  });

  if (!bootResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.CheckBoot0`,
      path: bootResult.path,
      witness: bootResult.witness,
      ledger,
    });
  }

  const json = validateJsonMaterializable0(boot);

  ledger.push({
    phase: 'jsonMaterializable',
    status: json.ok ? 'pass' : 'fail',
    digest: digestCanonical0(json.nf ?? json.witness ?? null),
  });

  if (!json.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.json`,
      path: json.path,
      witness: json.witness,
      ledger,
    });
  }

  const audit = validatePrecomputedAudit0(boot.BootAudit0);

  ledger.push({
    phase: 'precomputedAudit',
    status: audit.ok ? 'pass' : 'fail',
    digest: digestCanonical0(audit.nf ?? audit.witness ?? null),
  });

  if (!audit.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.BootAudit0`,
      path: audit.path,
      witness: audit.witness,
      ledger,
    });
  }

  const iface = validateConcreteIfaceHash0(boot);

  ledger.push({
    phase: 'concreteIfaceHash',
    status: iface.ok ? 'pass' : 'fail',
    digest: digestCanonical0(iface.nf ?? iface.witness ?? null),
  });

  if (!iface.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.IfaceHash`,
      path: iface.path,
      witness: iface.witness,
      ledger,
    });
  }

  const markers = validateNoSyntheticMarkers0(boot, config);

  ledger.push({
    phase: 'noFixtureMarkers',
    status: markers.ok ? 'pass' : 'fail',
    digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
  });

  if (!markers.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noFixtureMarkers`,
      path: markers.path,
      witness: markers.witness,
      ledger,
    });
  }

  const bootNF = bootRecord.NF ?? bootRecord.nf;
  const canonicalBytes = stableStringify0(boot);

  const nf = {
    kind: 'MaterializedBoot0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    jsonMaterializable: true,
    precomputedAudit: true,
    noFixtureMarkers: true,
    bootDigest: bootRecord.Digest ?? bootRecord.digest,
    canonicalByteDigest: sha256Utf8DigestRecord0(canonicalBytes),
    byteLength: Buffer.byteLength(canonicalBytes, 'utf8'),
    rowCount: bootNF.rowCount,
    kernelRuleCount: bootNF.kernelRuleCount,
    ifaceDigest: digestCanonical0(boot.IfaceDict0),
    schedDigest: digestCanonical0(boot.Sched0),
    bootBatchDigest: bootNF.bootBatchDigest,
    bootAuditDigest: bootNF.bootAuditDigest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedBoot0Files0(outputDir, config = {}) {
  const outDir = typeof outputDir === 'string' && outputDir.length > 0
    ? outputDir
    : './materialized-boot0';

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const boot = config.boot ?? await makeMaterializedBoot0(config.bootOverrides ?? {});
  const checked = await CheckMaterializedBoot0(boot, config.checkConfig ?? {});

  if (checked.tag !== 'accept') {
    return checked;
  }

  const bootBytes = `${stableStringify0(boot)}\n`;
  const checkBytes = `${stableStringify0(checked)}\n`;
  const bootPath = path.join(outDir, 'Boot0.json');
  const checkPath = path.join(outDir, 'MaterializedBoot0.check.json');

  await fs.writeFile(bootPath, bootBytes, 'utf8');
  await fs.writeFile(checkPath, checkBytes, 'utf8');

  const nf = {
    kind: 'MaterializedBoot0Write0NF',
    checker: 'WriteMaterializedBoot0Files0',
    version: CHECKER_VERSION,
    outputDir: outDir,
    files: [
      {
        path: bootPath,
        byteLength: Buffer.byteLength(bootBytes, 'utf8'),
        fileDigest: sha256Utf8DigestRecord0(bootBytes),
      },
      {
        path: checkPath,
        byteLength: Buffer.byteLength(checkBytes, 'utf8'),
        fileDigest: sha256Utf8DigestRecord0(checkBytes),
      },
    ],
    bootDigest: checked.NF.bootDigest,
    materializedBootDigest: checked.Digest,
  };

  return makeAcceptRecord({
    checker: 'WriteMaterializedBoot0Files0',
    nf,
    ledger: [
      {
        phase: 'CheckMaterializedBoot0',
        status: 'pass',
        digest: checked.Digest,
      },
      {
        phase: 'writeFiles',
        status: 'pass',
        digest: digestCanonical0(nf.files),
      },
    ],
  });
}

function validateJsonMaterializable0(value) {
  const hit = findNonJsonValue0(value, []);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized Boot0 must be JSON-materializable data', {
      actual: hit.actual,
    });
  }

  const canonical = stableStringify0(value);
  let reparsed;

  try {
    reparsed = JSON.parse(canonical);
  } catch (error) {
    return validationReject0([], 'materialized Boot0 canonical bytes must parse as JSON', {
      error: error.message,
    });
  }

  if (stableStringify0(reparsed) !== canonical) {
    return validationReject0([], 'materialized Boot0 JSON roundtrip must be byte-stable', null);
  }

  return validationAccept0({
    kind: 'MaterializedBoot0Json0NF',
    byteLength: Buffer.byteLength(canonical, 'utf8'),
    byteDigest: sha256Utf8DigestRecord0(canonical),
  });
}

function validatePrecomputedAudit0(audit) {
  if (!isPlainObject(audit)) {
    return validationReject0(['BootAudit0'], 'BootAudit0 must be a precomputed CheckVerifierFrag0 accept record', {
      actual: typeof audit,
    });
  }

  if (audit.tag !== 'accept' || audit.checker !== 'CheckVerifierFrag0') {
    return validationReject0(['BootAudit0'], 'materialized BootAudit0 must embed an accepted CheckVerifierFrag0 record', {
      tag: audit.tag,
      checker: audit.checker,
    });
  }

  const nf = audit.NF ?? audit.nf;

  if (!isPlainObject(nf) || nf.kind !== 'VerifierFrag0AuditNF') {
    return validationReject0(['BootAudit0', 'NF'], 'BootAudit0 verifier normal form mismatch', {
      actual: nf?.kind ?? typeof nf,
    });
  }

  return validationAccept0({
    kind: 'MaterializedBoot0PrecomputedAudit0NF',
    suiteId: nf.suiteId,
    caseCount: nf.caseCount,
    auditDigest: audit.Digest ?? audit.digest,
  });
}

function validateConcreteIfaceHash0(boot) {
  const expected = digestCanonical0(boot.IfaceDict0).hex;
  const rows = boot?.B0?.rows;

  if (!Array.isArray(rows)) {
    return validationReject0(['B0', 'rows'], 'Boot0 B0 rows must be an array before interface-hash checking', {
      actual: typeof rows,
    });
  }

  for (let index = 0; index < rows.length; index += 1) {
    const actual = rows[index]?.IfaceHash;

    if (actual !== expected) {
      return validationReject0(['B0', 'rows', index, 'IfaceHash'], 'B0 row IfaceHash must be the concrete IfaceDict0 digest hex', {
        expected,
        actual,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedBoot0IfaceHash0NF',
    ifaceHash: expected,
    rowCount: rows.length,
  });
}

function validateNoSyntheticMarkers0(value, config = {}) {
  const allow = new Set(config.allowedMarkerPaths ?? []);
  const hit = findSyntheticMarker0(value, [], allow);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized Boot0 must not contain fixture-level marker text', {
      marker: hit.marker,
      value: hit.value,
    });
  }

  return validationAccept0({
    kind: 'MaterializedBoot0NoFixtureMarkers0NF',
  });
}

function findSyntheticMarker0(value, pathNow, allow) {
  const pathKey = pathNow.join('.');

  if (allow.has(pathKey)) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_BOOT0_FORBIDDEN_MARKERS0) {
      if (lower.includes(marker)) {
        return {
          path: pathNow,
          marker,
          value,
        };
      }
    }

    return null;
  }

  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'number' || typeof value === 'boolean') {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findSyntheticMarker0(value[index], [...pathNow, index], allow);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    const keyHit = findSyntheticMarker0(key, [...pathNow, key], allow);

    if (keyHit !== null) {
      return keyHit;
    }

    const valueHit = findSyntheticMarker0(value[key], [...pathNow, key], allow);

    if (valueHit !== null) {
      return valueHit;
    }
  }

  return null;
}

function findNonJsonValue0(value, pathNow) {
  if (value === undefined) {
    return {
      path: pathNow,
      actual: 'undefined',
    };
  }

  if (typeof value === 'function') {
    return {
      path: pathNow,
      actual: 'function',
    };
  }

  if (typeof value === 'symbol') {
    return {
      path: pathNow,
      actual: 'symbol',
    };
  }

  if (typeof value === 'bigint') {
    return {
      path: pathNow,
      actual: 'bigint',
    };
  }

  if (value === null || typeof value === 'string' || typeof value === 'boolean') {
    return null;
  }

  if (typeof value === 'number') {
    if (!Number.isFinite(value) || Object.is(value, -0)) {
      return {
        path: pathNow,
        actual: String(value),
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findNonJsonValue0(value[index], [...pathNow, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return {
      path: pathNow,
      actual: Object.prototype.toString.call(value),
    };
  }

  for (const key of Object.keys(value)) {
    const hit = findNonJsonValue0(value[key], [...pathNow, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function withoutBootOverrideFields0(overrides) {
  const out = {
    ...overrides,
  };

  for (const key of [
    'ByteLang0',
    'Codec0',
    'Digest0',
    'IfaceDict0',
    'Sched0',
    'KernelSeed0',
    'B0',
    'BootAudit0',
    'PiBoot',
  ]) {
    delete out[key];
  }

  return out;
}

function sha256Utf8DigestRecord0(value) {
  return {
    alg: 'SHA256',
    bytes: 'utf8',
    hex: createHash('sha256').update(String(value), 'utf8').digest('hex'),
  };
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
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

function validationAccept0(nf) {
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isRejectRecord0(value) {
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

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}
