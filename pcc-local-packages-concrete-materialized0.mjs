import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckLocalPackages0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
} from './pcc-local-packages0.mjs';

import {
  CheckMaterializedLocalPackages0,
  makeMaterializedLocalPackagePack0,
  makeMaterializedLocalPackages0,
} from './pcc-local-packages-materialized0.mjs';

import {
  CheckConcreteMaterializedRows0,
  makeConcreteMaterializedRows0,
} from './pcc-rows-concrete-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_LOCAL_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_LOCAL_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteMaterializedLocalPackagesConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedLocalPackagesConfig0',
    version: CHECKER_VERSION,
    checkConcreteRows: true,
    checkMaterializedLocalPackages: true,
    checkLocalPackages: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    ...overrides,
  };
}

export async function makeConcreteMaterializedLocalPackages0({
  ConcreteRowsEnvelope = null,
  LocalPackages = null,
  overrides = {},
} = {}) {
  const concreteRowsEnvelope = ConcreteRowsEnvelope ?? await makeConcreteMaterializedRows0();
  const rowPack = resolveRowPack0(concreteRowsEnvelope);

  if (!isPlainObject(rowPack)) {
    throw new TypeError('makeConcreteMaterializedLocalPackages0 requires a concrete RowPack0');
  }

  const localPackages = LocalPackages ?? makeMaterializedLocalPackagePack0({
    RowPack: rowPack,
  });

  const linkage = {
    kind: 'ConcreteMaterializedLocalPackagesLinkage0',
    version: CHECKER_VERSION,
    concreteRowsDigest: digestCanonical0(concreteRowsEnvelope),
    rowPackDigest: digestCanonical0(rowPack),
    declaredRowPackDigest: localPackages.RowPackDigest,
    localPackagePackDigest: digestCanonical0(localPackages),
    packageCount: Array.isArray(localPackages.Packages) ? localPackages.Packages.length : null,
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    families: [...LOCAL_PACKAGE_REQUIRED_FAMILIES0],
    schedHash: localPackages.SchedHash ?? null,
    ifaceHash: localPackages.IfaceHash ?? null,
  };

  return {
    kind: 'ConcreteMaterializedLocalPackages0',
    version: CHECKER_VERSION,
    ConcreteRowsEnvelope: concreteRowsEnvelope,
    RowPack: rowPack,
    LocalPackages: localPackages,
    Linkage: linkage,
    PiConcreteMaterializedLocalPackages: {
      kind: 'PiConcreteMaterializedLocalPackages0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteRowsEnvelope',
          digest: linkage.concreteRowsDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'LocalPackages',
          digest: linkage.localPackagePackDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckConcreteMaterializedLocalPackages0(
  input,
  config = makeConcreteMaterializedLocalPackagesConfig0(),
) {
  const checker = 'CheckConcreteMaterializedLocalPackages0';
  const ledger = [];
  const cfg = makeConcreteMaterializedLocalPackagesConfig0(config);
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

  if (cfg.checkConcreteRows === true) {
    const rowsRecord = await CheckConcreteMaterializedRows0(envelope.ConcreteRowsEnvelope);
    const rows = recordToValidation0(rowsRecord, ['ConcreteRowsEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedRows0',
      status: rows.ok ? 'pass' : 'fail',
      digest: rowsRecord.Digest ?? rowsRecord.digest ?? digestCanonical0(rowsRecord),
    });

    if (!rows.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteRows`,
        path: rows.path,
        witness: rows.witness,
        ledger,
      });
    }
  }

  if (cfg.checkMaterializedLocalPackages === true) {
    const materializedEnvelope = makeMaterializedLocalPackages0({
      RowPack: envelope.RowPack,
      LocalPackages: envelope.LocalPackages,
    });

    const materializedRecord = await CheckMaterializedLocalPackages0(materializedEnvelope, {
      checkRows: false,
    });
    const materialized = recordToValidation0(materializedRecord, ['LocalPackages']);

    ledger.push({
      phase: 'CheckMaterializedLocalPackages0',
      status: materialized.ok ? 'pass' : 'fail',
      digest: materializedRecord.Digest ?? materializedRecord.digest ?? digestCanonical0(materializedRecord),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedLocalPackages`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }
  }

  if (cfg.checkLocalPackages === true) {
    const localRecord = await CheckLocalPackages0(envelope.LocalPackages);
    const local = recordToValidation0(localRecord, ['LocalPackages']);

    ledger.push({
      phase: 'CheckLocalPackages0',
      status: local.ok ? 'pass' : 'fail',
      digest: localRecord.Digest ?? localRecord.digest ?? digestCanonical0(localRecord),
    });

    if (!local.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.LocalPackages`,
        path: local.path,
        witness: local.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope.LocalPackages);

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

  const markerInventory = collectFixtureMarkers0(envelope.LocalPackages, ['LocalPackages']);

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

  const localRecord = await CheckLocalPackages0(envelope.LocalPackages);
  const localNF = localRecord.NF ?? localRecord.nf ?? {};

  const nf = {
    kind: 'ConcreteMaterializedLocalPackages0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    concreteRows: true,
    concreteRowsEnvelopeKind: envelope.ConcreteRowsEnvelope.kind,
    localPackagesDigest: localRecord.Digest ?? localRecord.digest,
    localPackagesObjectDigest: digestCanonical0(envelope.LocalPackages),
    concreteRowsDigest: digestCanonical0(envelope.ConcreteRowsEnvelope),
    rowPackDigest: digestCanonical0(envelope.RowPack),
    declaredRowPackDigest: envelope.LocalPackages.RowPackDigest,
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    packageCount: localNF.packageCount ?? envelope.LocalPackages.Packages.length,
    familyCount: localNF.familyCount ?? LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    families: localNF.families ?? LOCAL_PACKAGE_REQUIRED_FAMILIES0,
    globalTheorems: localNF.globalTheorems ?? [],
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

export async function writeConcreteMaterializedLocalPackagesFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedLocalPackagesFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedLocalPackages0(options);
  const checked = await CheckConcreteMaterializedLocalPackages0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedLocalPackages0.json');
  const rowPackPath = path.join(outDir, 'ConcreteRowPack0.json');
  const localPackagesPath = path.join(outDir, 'ConcreteLocalPackagePack0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedLocalPackages0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(rowPackPath, envelope.RowPack);
  await writeJsonFile0(localPackagesPath, envelope.LocalPackages);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      rowPackPath,
      localPackagesPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'LocalPackagePack0') {
    return {
      kind: 'ConcreteMaterializedLocalPackages0',
      version: CHECKER_VERSION,
      ConcreteRowsEnvelope: null,
      RowPack: null,
      LocalPackages: input,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedLocalPackagesConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedLocalPackagesConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedLocalPackagesConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedLocalPackagesConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteRows',
    'checkMaterializedLocalPackages',
    'checkLocalPackages',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedLocalPackagesConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedLocalPackagesConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedLocalPackages0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedLocalPackages0') {
    return validationReject0(['kind'], 'ConcreteMaterializedLocalPackages0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedLocalPackages0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ConcreteRowsEnvelope)) {
    return validationReject0(['ConcreteRowsEnvelope'], 'ConcreteMaterializedLocalPackages0 must include ConcreteRowsEnvelope', {
      actual: typeof envelope.ConcreteRowsEnvelope,
    });
  }

  if (!isPlainObject(envelope.RowPack)) {
    return validationReject0(['RowPack'], 'ConcreteMaterializedLocalPackages0 must include RowPack', {
      actual: typeof envelope.RowPack,
    });
  }

  if (!isPlainObject(envelope.LocalPackages)) {
    return validationReject0(['LocalPackages'], 'ConcreteMaterializedLocalPackages0 must include LocalPackages', {
      actual: typeof envelope.LocalPackages,
    });
  }

  if (envelope.LocalPackages.kind !== 'LocalPackagePack0') {
    return validationReject0(['LocalPackages', 'kind'], 'LocalPackages kind must be LocalPackagePack0', {
      actual: envelope.LocalPackages.kind,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedLocalPackagesShape0NF',
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['LocalPackages'], 'LocalPackages must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['LocalPackages'], 'LocalPackages canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedLocalPackagesJson0NF',
    byteLength: bytes.length,
    localPackagesDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope) {
  const expectedConcreteRowsDigest = digestCanonical0(envelope.ConcreteRowsEnvelope);
  const expectedRowPackDigest = digestCanonical0(envelope.RowPack);
  const expectedLocalDigest = digestCanonical0(envelope.LocalPackages);

  if (!sameDigestHex0(envelope.LocalPackages.RowPackDigest, expectedRowPackDigest)) {
    return validationReject0(['LocalPackages', 'RowPackDigest'], 'LocalPackages RowPackDigest must match concrete RowPack canonical digest', {
      expected: expectedRowPackDigest,
      actual: envelope.LocalPackages.RowPackDigest,
    });
  }

  if (envelope.ConcreteRowsEnvelope.RowPack !== envelope.RowPack) {
    if (!sameDigestHex0(digestCanonical0(envelope.ConcreteRowsEnvelope.RowPack), expectedRowPackDigest)) {
      return validationReject0(['ConcreteRowsEnvelope', 'RowPack'], 'ConcreteRowsEnvelope RowPack must match top-level RowPack', {
        expected: expectedRowPackDigest,
        actual: digestCanonical0(envelope.ConcreteRowsEnvelope.RowPack),
      });
    }
  }

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteMaterializedLocalPackagesLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedLocalPackages0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const checks = [
    ['concreteRowsDigest', expectedConcreteRowsDigest],
    ['rowPackDigest', expectedRowPackDigest],
    ['declaredRowPackDigest', envelope.LocalPackages.RowPackDigest],
    ['localPackagePackDigest', expectedLocalDigest],
  ];

  for (const [field, expected] of checks) {
    if (!sameDigestHex0(envelope.Linkage[field], expected)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected,
        actual: envelope.Linkage[field],
      });
    }
  }

  if (envelope.Linkage.packageCount !== envelope.LocalPackages.Packages.length) {
    return validationReject0(['Linkage', 'packageCount'], 'Linkage packageCount mismatch', {
      expected: envelope.LocalPackages.Packages.length,
      actual: envelope.Linkage.packageCount,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedLocalPackagesLinkage0NF',
    present: true,
    concreteRowsDigest: expectedConcreteRowsDigest,
    rowPackDigest: expectedRowPackDigest,
    localPackagePackDigest: expectedLocalDigest,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteMaterializedLocalPackagesFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_LOCAL_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_LOCAL_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_LOCAL_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized LocalPackages contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedLocalPackagesNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function scanFixtureMarkers0(value, path, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      CONCRETE_LOCAL_SYNTHETIC_MARKER0,
      ...CONCRETE_LOCAL_FORBIDDEN_MARKERS0,
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
    scanFixtureMarkers0(value[key], [...path, key], hits);
  }
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function resolveRowPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowPack0'
    ? value
    : value.RowPack ?? value.rowPack ?? value.ConcreteRowPack ?? null;
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
