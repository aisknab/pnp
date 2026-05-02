import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckLocalPackages0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
  makeSyntheticLocalPackages0,
} from './pcc-local-packages0.mjs';

import {
  CheckMaterializedRows0,
  makeMaterializedRows0,
} from './pcc-rows-materialized0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_LOCAL_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedLocalPackagesConfig0(overrides = {}) {
  return {
    kind: 'MaterializedLocalPackagesConfig0',
    version: CHECKER_VERSION,
    checkRows: true,
    checkLocalPackages: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    checkLinkage: true,
    ...overrides,
  };
}

export function makeMaterializedLocalPackagePack0({
  RowPack = null,
  overrides = {},
} = {}) {
  const rowPack = RowPack ?? makeMaterializedRows0().RowPack;

  return makeSyntheticLocalPackages0({
    SchedHash: rowPack.SchedHash,
    IfaceHash: rowPack.IfaceHash,
    RowPackDigest: digestCanonical0(rowPack),
    PiLocalPackages: {
      kind: 'PiLocalPackages0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-local-package-pack',
      note: 'materialized local package proof references',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'RowPack',
          digest: digestCanonical0(rowPack),
        },
      ],
    },
    ...overrides,
  });
}

export function makeMaterializedLocalPackages0({
  RowPack = null,
  LocalPackages = null,
  overrides = {},
} = {}) {
  const rowPack = resolveRowPack0(RowPack) ?? makeMaterializedRows0().RowPack;
  const localPackages = LocalPackages ?? makeMaterializedLocalPackagePack0({
    RowPack: rowPack,
  });

  const linkage = {
    kind: 'MaterializedLocalPackagesLinkage0',
    version: CHECKER_VERSION,
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
    kind: 'MaterializedLocalPackages0',
    version: CHECKER_VERSION,
    RowPack: rowPack,
    LocalPackages: localPackages,
    Linkage: linkage,
    PiMaterializedLocalPackages: {
      kind: 'PiMaterializedLocalPackages0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'RowPack',
          digest: linkage.rowPackDigest,
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

export async function CheckMaterializedLocalPackages0(input, config = makeMaterializedLocalPackagesConfig0()) {
  const checker = 'CheckMaterializedLocalPackages0';
  const ledger = [];
  const cfg = makeMaterializedLocalPackagesConfig0(config);
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

  const shape = validateShape0(envelope, cfg);

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
    const rowsRecord = await CheckMaterializedRows0(makeMaterializedRows0({
      RowPack: envelope.RowPack,
    }));
    const rows = recordToValidation0(rowsRecord, ['RowPack']);

    ledger.push({
      phase: 'CheckMaterializedRows0',
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

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoFixtureMarkers0({
      LocalPackages: envelope.LocalPackages,
      PiMaterializedLocalPackages: envelope.PiMaterializedLocalPackages ?? null,
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

  const localRecord = await CheckLocalPackages0(envelope.LocalPackages);
  const localNF = localRecord.NF ?? localRecord.nf ?? {};

  const nf = {
    kind: 'MaterializedLocalPackages0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    localPackagesDigest: localRecord.Digest ?? localRecord.digest,
    localPackagesObjectDigest: digestCanonical0(envelope.LocalPackages),
    rowPackDigest: digestCanonical0(envelope.RowPack),
    declaredRowPackDigest: envelope.LocalPackages.RowPackDigest,
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    packageCount: localNF.packageCount ?? envelope.LocalPackages.Packages.length,
    familyCount: localNF.familyCount ?? LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    families: localNF.families ?? LOCAL_PACKAGE_REQUIRED_FAMILIES0,
    globalTheorems: localNF.globalTheorems ?? [],
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedLocalPackagesFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedLocalPackagesFiles0 requires a non-empty output directory');
  }

  const envelope = makeMaterializedLocalPackages0(options);
  const checked = await CheckMaterializedLocalPackages0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedLocalPackages0.json');
  const rowPackPath = path.join(outDir, 'RowPack0.json');
  const localPackagesPath = path.join(outDir, 'LocalPackagePack0.json');
  const checkPath = path.join(outDir, 'MaterializedLocalPackages0.check.json');

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

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'LocalPackagePack0') {
    return makeMaterializedLocalPackages0({
      LocalPackages: input,
    });
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedLocalPackagesConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedLocalPackagesConfig0') {
    return validationReject0(['kind'], 'MaterializedLocalPackagesConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedLocalPackagesConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkRows',
    'checkLocalPackages',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedLocalPackagesConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedLocalPackagesConfig0NF',
  });
}

function validateShape0(envelope, config) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedLocalPackages0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedLocalPackages0') {
    return validationReject0(['kind'], 'MaterializedLocalPackages0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedLocalPackages0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (config.checkRows === true && !isPlainObject(envelope.RowPack)) {
    return validationReject0(['RowPack'], 'MaterializedLocalPackages0 must include RowPack when checkRows=true', {
      actual: typeof envelope.RowPack,
    });
  }

  if (!isPlainObject(envelope.LocalPackages)) {
    return validationReject0(['LocalPackages'], 'MaterializedLocalPackages0 must include a LocalPackages object', {
      actual: typeof envelope.LocalPackages,
    });
  }

  if (envelope.LocalPackages.kind !== 'LocalPackagePack0') {
    return validationReject0(['LocalPackages', 'kind'], 'LocalPackages kind must be LocalPackagePack0', {
      actual: envelope.LocalPackages.kind,
    });
  }

  if (!Array.isArray(envelope.LocalPackages.Packages)) {
    return validationReject0(['LocalPackages', 'Packages'], 'LocalPackages Packages must be an array', {
      actual: typeof envelope.LocalPackages.Packages,
    });
  }

  return validationAccept0({
    kind: 'MaterializedLocalPackagesShape0NF',
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
    kind: 'MaterializedLocalPackagesJson0NF',
    byteLength: bytes.length,
    localPackagesDigest: digestCanonical0(value),
  });
}

function validateNoFixtureMarkers0(value) {
  const hit = firstFixtureMarker0(value, ['MaterializedLocalPackages0']);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized LocalPackages must not contain fixture-marker text', hit);
  }

  return validationAccept0({
    kind: 'MaterializedLocalPackagesNoFixtureMarkers0NF',
  });
}

function validateLinkage0(envelope) {
  if (!isPlainObject(envelope.RowPack)) {
    return validationReject0(['RowPack'], 'RowPack must be present for LocalPackages linkage', {
      actual: typeof envelope.RowPack,
    });
  }

  const expectedRowPackDigest = digestCanonical0(envelope.RowPack);

  if (!sameDigestHex0(envelope.LocalPackages.RowPackDigest, expectedRowPackDigest)) {
    return validationReject0(['LocalPackages', 'RowPackDigest'], 'LocalPackages RowPackDigest must match RowPack canonical object digest', {
      expected: expectedRowPackDigest,
      actual: envelope.LocalPackages.RowPackDigest,
    });
  }

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedLocalPackagesLinkage0NF',
      present: false,
      rowPackDigest: expectedRowPackDigest,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedLocalPackages0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  if (!sameDigestHex0(envelope.Linkage.rowPackDigest, expectedRowPackDigest)) {
    return validationReject0(['Linkage', 'rowPackDigest'], 'Linkage rowPackDigest must match RowPack canonical object digest', {
      expected: expectedRowPackDigest,
      actual: envelope.Linkage.rowPackDigest,
    });
  }

  const expectedLocalDigest = digestCanonical0(envelope.LocalPackages);

  if (!sameDigestHex0(envelope.Linkage.localPackagePackDigest, expectedLocalDigest)) {
    return validationReject0(['Linkage', 'localPackagePackDigest'], 'Linkage localPackagePackDigest must match LocalPackages canonical object digest', {
      expected: expectedLocalDigest,
      actual: envelope.Linkage.localPackagePackDigest,
    });
  }

  if (envelope.Linkage.familyCount !== LOCAL_PACKAGE_REQUIRED_FAMILIES0.length) {
    return validationReject0(['Linkage', 'familyCount'], 'Linkage familyCount mismatch', {
      expected: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
      actual: envelope.Linkage.familyCount,
    });
  }

  return validationAccept0({
    kind: 'MaterializedLocalPackagesLinkage0NF',
    present: true,
    rowPackDigest: expectedRowPackDigest,
    localPackagePackDigest: expectedLocalDigest,
  });
}

function firstFixtureMarker0(value, path) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_LOCAL_FORBIDDEN_MARKERS0) {
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

    for (const marker of MATERIALIZED_LOCAL_FORBIDDEN_MARKERS0) {
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

function resolveRowPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowPack0'
    ? value
    : value.RowPack ?? value.rowPack ?? null;
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
