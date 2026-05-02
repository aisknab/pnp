import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckHard0,
  HARD_CHECKER_FIELDS0,
  HARD_FORBIDDEN_IMPORT_EDGES0,
  HARD_FORBIDDEN_SYMBOLS0,
  HARD_ROUTE_PRIORITY0,
  HARD_ROWKEY_FIELDS0,
  makeSyntheticHardCheck0,
} from './pcc-hard0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_HARD_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedHardConfig0(overrides = {}) {
  return {
    kind: 'MaterializedHardConfig0',
    version: CHECKER_VERSION,
    checkHard: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    checkLinkage: true,
    ...overrides,
  };
}

export function makeMaterializedHardCheck0(overrides = {}) {
  return makeSyntheticHardCheck0({
    PiHard: {
      kind: 'PiHard0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-hard-checker-suite',
      note: 'materialized hardened checker proof references',
      refs: [],
    },
    ...overrides,
  });
}

export function makeMaterializedHard0({
  HardCheck = null,
  overrides = {},
} = {}) {
  const hard = HardCheck ?? makeMaterializedHardCheck0();

  const linkage = {
    kind: 'MaterializedHardCheckLinkage0',
    version: CHECKER_VERSION,
    hardCheckDigest: digestCanonical0(hard),
    checkerCount: HARD_CHECKER_FIELDS0.length,
    checkerFields: [...HARD_CHECKER_FIELDS0],
    checkerIds: HARD_CHECKER_FIELDS0.map((field) => ({
      field,
      checkerId: hard[field]?.checkerId ?? null,
    })),
    rowKeyFields: hard.RowKeyCheck?.rowKeyFields ?? [...HARD_ROWKEY_FIELDS0],
    routePriority: hard.RouteCheck?.priority ?? [...HARD_ROUTE_PRIORITY0],
    forbiddenSymbols: hard.NoMinCheck?.forbiddenSymbols ?? [...HARD_FORBIDDEN_SYMBOLS0],
    forbiddenImportEdges: hard.ImportCheck?.forbiddenEdges ?? HARD_FORBIDDEN_IMPORT_EDGES0,
  };

  return {
    kind: 'MaterializedHardCheck0',
    version: CHECKER_VERSION,
    HardCheck: hard,
    Linkage: linkage,
    PiMaterializedHardCheck: {
      kind: 'PiMaterializedHardCheck0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'HardCheck',
          digest: linkage.hardCheckDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckMaterializedHard0(input, config = makeMaterializedHardConfig0()) {
  const checker = 'CheckMaterializedHard0';
  const ledger = [];
  const cfg = makeMaterializedHardConfig0(config);
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

  if (cfg.checkHard === true) {
    const hardRecord = await CheckHard0(envelope.HardCheck);
    const hard = recordToValidation0(hardRecord, ['HardCheck']);

    ledger.push({
      phase: 'CheckHard0',
      status: hard.ok ? 'pass' : 'fail',
      digest: hardRecord.Digest ?? hardRecord.digest ?? digestCanonical0(hardRecord),
    });

    if (!hard.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.HardCheck`,
        path: hard.path,
        witness: hard.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope.HardCheck);

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

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoFixtureMarkers0({
      HardCheck: envelope.HardCheck,
      PiMaterializedHardCheck: envelope.PiMaterializedHardCheck ?? null,
    });

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

  const hardRecord = await CheckHard0(envelope.HardCheck);
  const hardNF = hardRecord.NF ?? hardRecord.nf ?? {};

  const nf = {
    kind: 'MaterializedHardCheck0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    hardCheckDigest: hardRecord.Digest ?? hardRecord.digest,
    hardObjectDigest: digestCanonical0(envelope.HardCheck),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    checkerCount: hardNF.checkerCount ?? HARD_CHECKER_FIELDS0.length,
    checkerFields: [...HARD_CHECKER_FIELDS0],
    rowKeyFields: envelope.HardCheck.RowKeyCheck.rowKeyFields,
    routePriority: envelope.HardCheck.RouteCheck.priority,
    forbiddenSymbols: envelope.HardCheck.NoMinCheck.forbiddenSymbols,
    forbiddenImportEdges: envelope.HardCheck.ImportCheck.forbiddenEdges,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedHardFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedHardFiles0 requires a non-empty output directory');
  }

  const envelope = makeMaterializedHard0(options);
  const checked = await CheckMaterializedHard0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedHardCheck0.json');
  const hardPath = path.join(outDir, 'HardCheck0.json');
  const checkPath = path.join(outDir, 'MaterializedHardCheck0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(hardPath, envelope.HardCheck);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      hardPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'HardCheck0') {
    return makeMaterializedHard0({
      HardCheck: input,
    });
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedHardConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedHardConfig0') {
    return validationReject0(['kind'], 'MaterializedHardConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedHardConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkHard',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedHardConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedHardConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedHardCheck0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedHardCheck0') {
    return validationReject0(['kind'], 'MaterializedHardCheck0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedHardCheck0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.HardCheck)) {
    return validationReject0(['HardCheck'], 'MaterializedHardCheck0 must include a HardCheck object', {
      actual: typeof envelope.HardCheck,
    });
  }

  if (envelope.HardCheck.kind !== 'HardCheck0') {
    return validationReject0(['HardCheck', 'kind'], 'HardCheck kind must be HardCheck0', {
      actual: envelope.HardCheck.kind,
    });
  }

  return validationAccept0({
    kind: 'MaterializedHardCheckShape0NF',
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['HardCheck'], 'HardCheck must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['HardCheck'], 'HardCheck canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedHardJson0NF',
    byteLength: bytes.length,
    hardDigest: digestCanonical0(value),
  });
}

function validateNoFixtureMarkers0(value) {
  const hit = firstFixtureMarker0(value, ['MaterializedHardCheck0']);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized HardCheck must not contain fixture-marker text', hit);
  }

  return validationAccept0({
    kind: 'MaterializedHardNoFixtureMarkers0NF',
  });
}

function validateLinkage0(envelope) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedHardLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedHardCheck0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expectedHardDigest = digestCanonical0(envelope.HardCheck);

  if (!sameDigestHex0(envelope.Linkage.hardCheckDigest, expectedHardDigest)) {
    return validationReject0(['Linkage', 'hardCheckDigest'], 'Linkage hardCheckDigest must match HardCheck canonical object digest', {
      expected: expectedHardDigest,
      actual: envelope.Linkage.hardCheckDigest,
    });
  }

  if (envelope.Linkage.checkerCount !== HARD_CHECKER_FIELDS0.length) {
    return validationReject0(['Linkage', 'checkerCount'], 'Linkage checkerCount mismatch', {
      expected: HARD_CHECKER_FIELDS0.length,
      actual: envelope.Linkage.checkerCount,
    });
  }

  if (!Array.isArray(envelope.Linkage.checkerFields)) {
    return validationReject0(['Linkage', 'checkerFields'], 'Linkage checkerFields must be an array', {
      actual: typeof envelope.Linkage.checkerFields,
    });
  }

  for (let index = 0; index < HARD_CHECKER_FIELDS0.length; index += 1) {
    if (envelope.Linkage.checkerFields[index] !== HARD_CHECKER_FIELDS0[index]) {
      return validationReject0(['Linkage', 'checkerFields', index], 'Linkage checkerFields order mismatch', {
        expected: HARD_CHECKER_FIELDS0[index],
        actual: envelope.Linkage.checkerFields[index],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedHardLinkage0NF',
    present: true,
    hardCheckDigest: expectedHardDigest,
  });
}

function firstFixtureMarker0(value, path) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_HARD_FORBIDDEN_MARKERS0) {
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
      const hit = firstFixtureMarker0(value[index], [...path, index]);

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
    const lowerKey = key.toLowerCase();

    for (const marker of MATERIALIZED_HARD_FORBIDDEN_MARKERS0) {
      if (lowerKey.includes(marker)) {
        return {
          path: [...path, key],
          marker,
          value: key,
        };
      }
    }

    const hit = firstFixtureMarker0(value[key], [...path, key]);

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
