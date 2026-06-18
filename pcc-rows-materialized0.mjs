import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckBatchDeps0,
  CheckRowFamilies0,
  CheckRows0,
  ROW_BATCH_IDS0,
  ROW_REQUIRED_FAMILIES0,
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_ROW_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const MATERIALIZED_ROW_SYNTHETIC_MARKER0 = 'synthetic';

export function makeMaterializedRowsConfig0(overrides = {}) {
  return {
    kind: 'MaterializedRowsConfig0',
    version: CHECKER_VERSION,
    checkRows: true,
    checkBatchDeps: true,
    checkRowFamilies: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    ...overrides,
  };
}

export function makeMaterializedRowPack0(overrides = {}) {
  const rowPack = makeSyntheticRowPack0({
    PiRows: {
      kind: 'PiRows0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-row-package',
      note: 'materialized row package proof references',
      refs: [],
    },
  });

  return {
    ...rowPack,
    ...overrides,
  };
}

export function makeMaterializedRows0({
  RowPack = null,
  overrides = {},
} = {}) {
  const rowPack = RowPack ?? makeMaterializedRowPack0();

  const linkage = {
    kind: 'MaterializedRowsLinkage0',
    version: CHECKER_VERSION,
    rowPackDigest: digestCanonical0(rowPack),
    rowCount: Array.isArray(rowPack.Rows) ? rowPack.Rows.length : null,
    batchCount: ROW_BATCH_IDS0.length,
    familyCount: ROW_REQUIRED_FAMILIES0.length,
    batches: [...ROW_BATCH_IDS0],
    families: [...ROW_REQUIRED_FAMILIES0],
    schedHash: rowPack.SchedHash ?? null,
    ifaceHash: rowPack.IfaceHash ?? null,
  };

  return {
    kind: 'MaterializedRows0',
    version: CHECKER_VERSION,
    RowPack: rowPack,
    Linkage: linkage,
    PiMaterializedRows: {
      kind: 'PiMaterializedRows0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
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

export async function CheckMaterializedRows0(input, config = makeMaterializedRowsConfig0()) {
  const checker = 'CheckMaterializedRows0';
  const ledger = [];
  const cfg = makeMaterializedRowsConfig0(config);
  const envelope = normalizeEnvelope0(input);

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
    const depsRecord = await CheckBatchDeps0(envelope.RowPack.BatchInv);
    const deps = recordToValidation0(depsRecord, ['RowPack', 'BatchInv']);

    ledger.push({
      phase: 'CheckBatchDeps0',
      status: deps.ok ? 'pass' : 'fail',
      digest: depsRecord.Digest ?? depsRecord.digest ?? digestCanonical0(depsRecord),
    });

    if (!deps.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.BatchDeps`,
        path: deps.path,
        witness: deps.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope.RowPack, ['RowPack']);

  ledger.push({
    phase: 'fixtureMarkerInventory',
    status: 'pass',
    digest: digestCanonical0(markerInventory),
  });

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoForbiddenFixtureMarkers0(markerInventory, cfg);

    ledger.push({
      phase: 'fixtureMarkers',
      status: markers.ok ? 'pass' : 'fail',
      digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
    });

    if (!markers.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.fixtureMarkers`,
        path: markers.path,
        witness: markers.witness,
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
    kind: 'MaterializedRows0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    rowPackDigest: rowsRecord.Digest ?? rowsRecord.digest,
    rowPackObjectDigest: digestCanonical0(envelope.RowPack),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    rowCount: rowsNF.rowCount ?? envelope.RowPack.Rows.length,
    batchCount: rowsNF.batchCount ?? ROW_BATCH_IDS0.length,
    familyCount: rowsNF.familyCount ?? ROW_REQUIRED_FAMILIES0.length,
    batches: rowsNF.batches ?? ROW_BATCH_IDS0,
    families: rowsNF.families ?? ROW_REQUIRED_FAMILIES0,
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedRowsFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedRowsFiles0 requires a non-empty output directory');
  }

  const envelope = makeMaterializedRows0(options);
  const checked = await CheckMaterializedRows0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedRows0.json');
  const rowPackPath = path.join(outDir, 'RowPack0.json');
  const checkPath = path.join(outDir, 'MaterializedRows0.check.json');

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

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'RowPack0') {
    return makeMaterializedRows0({
      RowPack: input,
    });
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedRowsConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedRowsConfig0') {
    return validationReject0(['kind'], 'MaterializedRowsConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedRowsConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkRows',
    'checkBatchDeps',
    'checkRowFamilies',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedRowsConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedRowsConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedRows0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedRows0') {
    return validationReject0(['kind'], 'MaterializedRows0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedRows0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.RowPack)) {
    return validationReject0(['RowPack'], 'MaterializedRows0 must include a RowPack object', {
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
    kind: 'MaterializedRowsShape0NF',
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
    kind: 'MaterializedRowsJson0NF',
    byteLength: bytes.length,
    rowPackDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'MaterializedRowsFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === MATERIALIZED_ROW_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== MATERIALIZED_ROW_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== MATERIALIZED_ROW_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'materialized RowPack contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'MaterializedRowsNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedRowsLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedRows0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expectedRowPackDigest = digestCanonical0(envelope.RowPack);

  if (!sameDigestHex0(envelope.Linkage.rowPackDigest, expectedRowPackDigest)) {
    return validationReject0(['Linkage', 'rowPackDigest'], 'Linkage rowPackDigest must match RowPack canonical object digest', {
      expected: expectedRowPackDigest,
      actual: envelope.Linkage.rowPackDigest,
    });
  }

  if (envelope.Linkage.rowCount !== envelope.RowPack.Rows.length) {
    return validationReject0(['Linkage', 'rowCount'], 'Linkage rowCount mismatch', {
      expected: envelope.RowPack.Rows.length,
      actual: envelope.Linkage.rowCount,
    });
  }

  if (envelope.Linkage.batchCount !== ROW_BATCH_IDS0.length) {
    return validationReject0(['Linkage', 'batchCount'], 'Linkage batchCount mismatch', {
      expected: ROW_BATCH_IDS0.length,
      actual: envelope.Linkage.batchCount,
    });
  }

  if (envelope.Linkage.familyCount !== ROW_REQUIRED_FAMILIES0.length) {
    return validationReject0(['Linkage', 'familyCount'], 'Linkage familyCount mismatch', {
      expected: ROW_REQUIRED_FAMILIES0.length,
      actual: envelope.Linkage.familyCount,
    });
  }

  return validationAccept0({
    kind: 'MaterializedRowsLinkage0NF',
    present: true,
    rowPackDigest: expectedRowPackDigest,
  });
}

function scanFixtureMarkers0(value, path, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      MATERIALIZED_ROW_SYNTHETIC_MARKER0,
      ...MATERIALIZED_ROW_FORBIDDEN_MARKERS0,
    ]) {
      if (lower.includes(marker)) {
        hits.push({
          path,
          marker,
          value,
        });
      }
    }

    return;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      scanFixtureMarkers0(value[index], [...path, index], hits);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    const lowerKey = key.toLowerCase();

    for (const marker of [
      MATERIALIZED_ROW_SYNTHETIC_MARKER0,
      ...MATERIALIZED_ROW_FORBIDDEN_MARKERS0,
    ]) {
      if (lowerKey.includes(marker)) {
        hits.push({
          path: [...path, key],
          marker,
          value: key,
        });
      }
    }

    scanFixtureMarkers0(value[key], [...path, key], hits);
  }
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
