import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  BOOT_BATCH0_REQUIRED_ROWS,
  makeBootstrapB0Rows0,
} from './pcc-boot0.mjs';

import {
  CheckMaterializedBoot0,
  makeMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

import {
  CheckBatchDeps0,
  CheckRowFamilies0,
  CheckRows0,
  ROW_BATCH_IDS0,
  ROW_REQUIRED_FAMILIES0,
  makeBatchInventory0,
  makeBoundsLedger0,
  makeCoverageLedger0,
  makeDupLedger0,
  makeGeneratedPackageRows0,
  makeHashIndex0,
  makeNFMap0,
  makeProofRefLedger0,
  makeRouteLedger0,
  makeSchemaInventory0,
} from './pcc-rows0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_ROW_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeConcreteMaterializedRowsConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedRowsConfig0',
    version: CHECKER_VERSION,
    checkBoot: true,
    checkRows: true,
    checkBatchDeps: true,
    checkRowFamilies: true,
    checkConcreteIfaceHash: true,
    checkNoScaffoldMarkers: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    ...overrides,
  };
}

export async function makeConcreteMaterializedRowPack0({
  Boot0 = null,
  overrides = {},
} = {}) {
  const boot0 = Boot0 ?? await makeMaterializedBoot0();

  const ifaceHash = digestCanonical0(boot0.IfaceDict0);
  const schedHash = digestCanonical0(boot0.Sched0);

  const rows = [
    ...makeConcreteB0Rows0(ifaceHash),
    ...makeGeneratedPackageRows0({
      IfaceHash: ifaceHash,
      SelectedRoute: 'Accept',
    }),
  ];

  return {
    kind: 'RowPack0',
    version: CHECKER_VERSION,
    SchedHash: schedHash,
    IfaceHash: ifaceHash,
    SchemaInv: makeSchemaInventory0(),
    BatchInv: makeBatchInventory0(),
    Rows: rows,
    NFMap: makeNFMap0(rows),
    HashIndex: makeHashIndex0(rows),
    DupLedger: makeDupLedger0(rows),
    CoverageLedger: makeCoverageLedger0(rows),
    RouteLedger: makeRouteLedger0(rows),
    ProofRefLedger: makeProofRefLedger0(rows),
    BoundsLedger: makeBoundsLedger0(rows),
    PiRows: {
      kind: 'PiRows0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'concrete-materialized-row-package',
      note: 'concrete materialized row-package proof references',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'IfaceDict0',
          digest: ifaceHash,
        },
        {
          kind: 'MaterializedRef0',
          target: 'Sched0',
          digest: schedHash,
        },
      ],
    },
    ...overrides,
  };
}

export async function makeConcreteMaterializedRows0({
  Boot0 = null,
  RowPack = null,
  overrides = {},
} = {}) {
  const boot0 = Boot0 ?? await makeMaterializedBoot0();
  const rowPack = RowPack ?? await makeConcreteMaterializedRowPack0({
    Boot0: boot0,
  });

  const linkage = {
    kind: 'ConcreteMaterializedRowsLinkage0',
    version: CHECKER_VERSION,
    bootDigest: digestCanonical0(boot0),
    ifaceHash: digestCanonical0(boot0.IfaceDict0),
    schedHash: digestCanonical0(boot0.Sched0),
    rowPackDigest: digestCanonical0(rowPack),
    rowCount: Array.isArray(rowPack.Rows) ? rowPack.Rows.length : null,
    batchCount: ROW_BATCH_IDS0.length,
    familyCount: ROW_REQUIRED_FAMILIES0.length,
  };

  return {
    kind: 'ConcreteMaterializedRows0',
    version: CHECKER_VERSION,
    Boot0: boot0,
    RowPack: rowPack,
    Linkage: linkage,
    PiConcreteMaterializedRows: {
      kind: 'PiConcreteMaterializedRows0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'Boot0',
          digest: linkage.bootDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'RowPack',
          digest: linkage.rowPackDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckConcreteMaterializedRows0(
  input,
  config = makeConcreteMaterializedRowsConfig0(),
) {
  const checker = 'CheckConcreteMaterializedRows0';
  const ledger = [];
  const cfg = makeConcreteMaterializedRowsConfig0(config);
  const envelope = normalizeInput0(input);

  const cfgCheck = validateConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: cfgCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cfgCheck.nf ?? cfgCheck.witness ?? null),
  });

  if (!cfgCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: cfgCheck.path,
      witness: cfgCheck.witness,
      ledger,
    });
  }

  const shape = validateShape0(envelope);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  if (cfg.checkBoot === true) {
    const bootRecord = await CheckMaterializedBoot0(envelope.Boot0);
    const boot = recordToValidation0(bootRecord, ['Boot0']);

    ledger.push({
      phase: 'CheckMaterializedBoot0',
      status: boot.ok ? 'pass' : 'fail',
      digest: bootRecord.Digest ?? bootRecord.digest ?? digestCanonical0(bootRecord),
    });

    if (!boot.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.Boot0`,
        path: boot.path,
        witness: boot.witness,
        ledger,
      });
    }
  }

  if (cfg.checkRows === true) {
    const rowsRecord = await CheckRows0(envelope.RowPack);
    const rows = recordToValidation0(rowsRecord, ['RowPack']);

    ledger.push({
      phase: 'CheckRows0',
      status: rows.ok ? 'pass' : 'fail',
      digest: rowsRecord.Digest ?? rowsRecord.digest ?? digestCanonical0(rowsRecord),
    });

    if (!rows.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.Rows`,
        path: rows.path,
        witness: rows.witness,
        ledger,
      });
    }
  }

  if (cfg.checkBatchDeps === true) {
    const batchRecord = await CheckBatchDeps0(envelope.RowPack.BatchInv);
    const batch = recordToValidation0(batchRecord, ['RowPack', 'BatchInv']);

    ledger.push({
      phase: 'CheckBatchDeps0',
      status: batch.ok ? 'pass' : 'fail',
      digest: batchRecord.Digest ?? batchRecord.digest ?? digestCanonical0(batchRecord),
    });

    if (!batch.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.BatchDeps`,
        path: batch.path,
        witness: batch.witness,
        ledger,
      });
    }
  }

  if (cfg.checkRowFamilies === true) {
    const familiesRecord = await CheckRowFamilies0(envelope.RowPack);
    const families = recordToValidation0(familiesRecord, ['RowPack']);

    ledger.push({
      phase: 'CheckRowFamilies0',
      status: families.ok ? 'pass' : 'fail',
      digest: familiesRecord.Digest ?? familiesRecord.digest ?? digestCanonical0(familiesRecord),
    });

    if (!families.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.RowFamilies`,
        path: families.path,
        witness: families.witness,
        ledger,
      });
    }
  }

  if (cfg.checkConcreteIfaceHash === true) {
    const iface = validateConcreteIfaceHash0(envelope);

    ledger.push({
      phase: 'concreteIfaceHash',
      status: iface.ok ? 'pass' : 'fail',
      digest: digestCanonical0(iface.nf ?? iface.witness ?? null),
    });

    if (!iface.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.concreteIfaceHash`,
        path: iface.path,
        witness: iface.witness,
        ledger,
      });
    }
  }

  if (cfg.checkNoScaffoldMarkers === true) {
    const markers = validateNoScaffoldMarkers0(envelope.RowPack);

    ledger.push({
      phase: 'noScaffoldMarkers',
      status: markers.ok ? 'pass' : 'fail',
      digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
    });

    if (!markers.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.scaffoldMarkers`,
        path: markers.path,
        witness: markers.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope.RowPack);

    ledger.push({
      phase: 'jsonMaterialized',
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
  }

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope);

    ledger.push({
      phase: 'linkage',
      status: linkage.ok ? 'pass' : 'fail',
      digest: digestCanonical0(linkage.nf ?? linkage.witness ?? null),
    });

    if (!linkage.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.linkage`,
        path: linkage.path,
        witness: linkage.witness,
        ledger,
      });
    }
  }

  const rowsRecord = await CheckRows0(envelope.RowPack);
  const rowsNF = rowsRecord.NF ?? rowsRecord.nf ?? {};

  const nf = {
    kind: 'ConcreteMaterializedRows0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    rowPackDigest: rowsRecord.Digest ?? rowsRecord.digest,
    rowPackObjectDigest: digestCanonical0(envelope.RowPack),
    bootDigest: digestCanonical0(envelope.Boot0),
    ifaceHash: envelope.RowPack.IfaceHash,
    schedHash: envelope.RowPack.SchedHash,
    rowCount: rowsNF.rowCount ?? envelope.RowPack.Rows.length,
    batchCount: rowsNF.batchCount ?? ROW_BATCH_IDS0.length,
    familyCount: rowsNF.familyCount ?? ROW_REQUIRED_FAMILIES0.length,
    concreteIfaceHash: true,
    syntheticIfaceHashCount: envelope.RowPack.Rows.filter((row) => row.IfaceHash === 'IfaceDict0.synthetic').length,
    scaffoldMarkerCount: 0,
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeConcreteMaterializedRowsFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedRowsFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedRows0(options);
  const checked = await CheckConcreteMaterializedRows0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedRows0.json');
  const rowPackPath = path.join(outDir, 'ConcreteRowPack0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedRows0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(rowPackPath, envelope.RowPack);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      rowPackPath,
      checkPath,
    },
  };
}

function makeConcreteB0Rows0(ifaceHash) {
  const b0Rows = makeBootstrapB0Rows0({
    IfaceHash: ifaceHash,
    SelectedRoute: 'Accept',
  });

  return b0Rows.map((row, index) => ({
    ...row,
    BatchID: 'B0',
    FamilyID: BOOT_BATCH0_REQUIRED_ROWS[index].family,
    RowFamily: BOOT_BATCH0_REQUIRED_ROWS[index].family,
    ImportRefs: [],
  }));
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'RowPack0') {
    return {
      kind: 'ConcreteMaterializedRows0',
      version: CHECKER_VERSION,
      Boot0: null,
      RowPack: input,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedRowsConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedRowsConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedRowsConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedRowsConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkBoot',
    'checkRows',
    'checkBatchDeps',
    'checkRowFamilies',
    'checkConcreteIfaceHash',
    'checkNoScaffoldMarkers',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedRowsConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedRowsConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedRows0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedRows0') {
    return validationReject0(['kind'], 'ConcreteMaterializedRows0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedRows0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.RowPack)) {
    return validationReject0(['RowPack'], 'ConcreteMaterializedRows0 must include RowPack', {
      actual: typeof envelope.RowPack,
    });
  }

  if (envelope.RowPack.kind !== 'RowPack0') {
    return validationReject0(['RowPack', 'kind'], 'RowPack kind must be RowPack0', {
      actual: envelope.RowPack.kind,
    });
  }

  if (!Array.isArray(envelope.RowPack.Rows)) {
    return validationReject0(['RowPack', 'Rows'], 'RowPack Rows must be an array', {
      actual: typeof envelope.RowPack.Rows,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedRowsShape0NF',
  });
}

function validateConcreteIfaceHash0(envelope) {
  if (!isPlainObject(envelope.Boot0)) {
    return validationReject0(['Boot0'], 'Boot0 is required for concrete IfaceHash validation', {
      actual: typeof envelope.Boot0,
    });
  }

  const expectedIfaceHash = digestCanonical0(envelope.Boot0.IfaceDict0);
  const expectedSchedHash = digestCanonical0(envelope.Boot0.Sched0);

  if (!sameDigestHex0(envelope.RowPack.IfaceHash, expectedIfaceHash)) {
    return validationReject0(['RowPack', 'IfaceHash'], 'RowPack IfaceHash must match materialized Boot0 IfaceDict0 digest', {
      expected: expectedIfaceHash,
      actual: envelope.RowPack.IfaceHash,
    });
  }

  if (!sameDigestHex0(envelope.RowPack.SchedHash, expectedSchedHash)) {
    return validationReject0(['RowPack', 'SchedHash'], 'RowPack SchedHash must match materialized Boot0 Sched0 digest', {
      expected: expectedSchedHash,
      actual: envelope.RowPack.SchedHash,
    });
  }

  for (let index = 0; index < envelope.RowPack.Rows.length; index += 1) {
    const row = envelope.RowPack.Rows[index];

    if (!sameDigestHex0(row.IfaceHash, expectedIfaceHash)) {
      return validationReject0(['RowPack', 'Rows', index, 'IfaceHash'], 'row IfaceHash must match materialized Boot0 IfaceDict0 digest', {
        expected: expectedIfaceHash,
        actual: row.IfaceHash,
      });
    }

    if (row.IfaceHash === 'IfaceDict0.synthetic') {
      return validationReject0(['RowPack', 'Rows', index, 'IfaceHash'], 'row IfaceHash must not use the synthetic fixture marker', null);
    }
  }

  return validationAccept0({
    kind: 'ConcreteIfaceHash0NF',
    rowCount: envelope.RowPack.Rows.length,
    ifaceHash: expectedIfaceHash,
    schedHash: expectedSchedHash,
  });
}

function validateNoScaffoldMarkers0(rowPack) {
  const hit = firstMarker0(rowPack, ['RowPack']);

  if (hit !== null) {
    return validationReject0(hit.path, 'concrete materialized RowPack must not contain scaffold-marker text', hit);
  }

  return validationAccept0({
    kind: 'ConcreteRowsNoScaffoldMarkers0NF',
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['RowPack'], 'RowPack must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['RowPack'], 'RowPack canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteRowsJson0NF',
    byteLength: bytes.length,
    rowPackDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteRowsLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedRows0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    bootDigest: digestCanonical0(envelope.Boot0),
    ifaceHash: digestCanonical0(envelope.Boot0.IfaceDict0),
    schedHash: digestCanonical0(envelope.Boot0.Sched0),
    rowPackDigest: digestCanonical0(envelope.RowPack),
  };

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  if (envelope.Linkage.rowCount !== envelope.RowPack.Rows.length) {
    return validationReject0(['Linkage', 'rowCount'], 'Linkage rowCount mismatch', {
      expected: envelope.RowPack.Rows.length,
      actual: envelope.Linkage.rowCount,
    });
  }

  return validationAccept0({
    kind: 'ConcreteRowsLinkage0NF',
    present: true,
    ...expected,
  });
}

function firstMarker0(value, path) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of CONCRETE_ROW_FORBIDDEN_MARKERS0) {
      if (lower.includes(marker)) {
        return {
          path,
          marker,
          value,
        };
      }
    }

    return null;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = firstMarker0(value[index], [...path, index]);

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
    const hit = firstMarker0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function sameDigestHex0(actual, expected) {
  return (
    isPlainObject(actual) &&
    isPlainObject(expected) &&
    typeof actual.hex === 'string' &&
    typeof expected.hex === 'string' &&
    actual.hex === expected.hex &&
    (
      actual.alg === undefined ||
      expected.alg === undefined ||
      actual.alg === expected.alg
    )
  );
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
