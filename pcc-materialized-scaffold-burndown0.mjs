import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckFinalCertificatePublicStatus0,
  makeFinalCertificatePublicStatus0,
} from './pcc-final-certificate-public-status0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_SCAFFOLD_BURNDOWN_PHASES0 = Object.freeze([
  'CheckMaterializedScaffoldBurndownInput0',
  'CheckFinalCertificatePublicStatus0',
  'RecomputeMaterializedScaffoldInventory0',
  'CheckMaterializedScaffoldPolicy0',
  'CheckMaterializedScaffoldJson0',
  'CheckMaterializedScaffoldLinkage0',
  'EmitMaterializedScaffoldBurndown0',
]);

export const MATERIALIZED_SCAFFOLD_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export const MATERIALIZED_SCAFFOLD_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedScaffoldBurndownConfig0(overrides = {}) {
  return {
    kind: 'MaterializedScaffoldBurndownConfig0',
    version: CHECKER_VERSION,
    mode: 'audit',
    checkFinalCertificatePublicStatus: true,
    checkInventory: true,
    checkPolicy: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    forbiddenMarkers: [...MATERIALIZED_SCAFFOLD_FORBIDDEN_MARKERS0],
    finalCertificatePublicStatusConfig: {
      checkReleaseAuditRecord: false,
    },
    ...overrides,
  };
}

export async function makeMaterializedScaffoldBurndown0({
  FinalCertificatePublicStatusEnvelope = null,
  overrides = {},
} = {}) {
  const target = FinalCertificatePublicStatusEnvelope ?? await makeFinalCertificatePublicStatus0();
  const inventory = makeMaterializedScaffoldInventory0(target);

  const linkage = {
    kind: 'MaterializedScaffoldBurndownLinkage0',
    version: CHECKER_VERSION,
    targetDigest: digestCanonical0(target),
    inventoryDigest: digestCanonical0(inventory),
    markerHitCount: inventory.hitCount,
    syntheticMarkerCount: inventory.syntheticMarkerCount,
    forbiddenMarkerCount: inventory.forbiddenMarkerCount,
  };

  return {
    kind: 'MaterializedScaffoldBurndown0',
    version: CHECKER_VERSION,
    TargetKind: target.kind ?? null,
    FinalCertificatePublicStatusEnvelope: target,
    Inventory: inventory,
    Linkage: linkage,
    PiMaterializedScaffoldBurndown: {
      kind: 'PiMaterializedScaffoldBurndown0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'FinalCertificatePublicStatusEnvelope',
          digest: linkage.targetDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'MaterializedScaffoldInventory',
          digest: linkage.inventoryDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeMaterializedScaffoldInventory0(value, {
  rootPath = ['FinalCertificatePublicStatusEnvelope'],
  markers = MATERIALIZED_SCAFFOLD_MARKERS0,
} = {}) {
  const hits = [];

  scanMarkerValues0(value, rootPath, hits, markers);

  const byMarker = Object.fromEntries(markers.map((marker) => [
    marker,
    hits.filter((hit) => hit.marker === marker).length,
  ]));

  const byTopPath = {};

  for (const hit of hits) {
    const top = String(hit.path[1] ?? hit.path[0] ?? '<root>');
    byTopPath[top] = (byTopPath[top] ?? 0) + 1;
  }

  return {
    kind: 'MaterializedScaffoldInventory0',
    version: CHECKER_VERSION,
    markerSet: [...markers],
    hitCount: hits.length,
    syntheticMarkerCount: hits.filter((hit) => hit.marker === 'synthetic').length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== 'synthetic').length,
    byMarker,
    byTopPath,
    hits,
  };
}

export async function CheckMaterializedScaffoldBurndown0(
  input,
  config = makeMaterializedScaffoldBurndownConfig0(),
) {
  const checker = 'CheckMaterializedScaffoldBurndown0';
  const ledger = [];
  const cfg = makeMaterializedScaffoldBurndownConfig0(config);
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
    phase: 'CheckMaterializedScaffoldBurndownInput0',
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

  if (cfg.checkFinalCertificatePublicStatus === true) {
    const statusRecord = await CheckFinalCertificatePublicStatus0(
      envelope.FinalCertificatePublicStatusEnvelope,
      cfg.finalCertificatePublicStatusConfig ?? {},
    );
    const status = recordToValidation0(statusRecord, ['FinalCertificatePublicStatusEnvelope']);

    ledger.push({
      phase: 'CheckFinalCertificatePublicStatus0',
      status: status.ok ? 'pass' : 'fail',
      digest: statusRecord.Digest ?? statusRecord.digest ?? digestCanonical0(statusRecord),
    });

    if (!status.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalCertificatePublicStatus`,
        path: status.path,
        witness: status.witness,
        ledger,
      });
    }
  } else {
    ledger.push({
      phase: 'CheckFinalCertificatePublicStatus0',
      status: 'pass',
      digest: digestCanonical0({
        skipped: true,
      }),
    });
  }

  const recomputedInventory = makeMaterializedScaffoldInventory0(
    envelope.FinalCertificatePublicStatusEnvelope,
  );

  if (cfg.checkInventory === true) {
    const inventory = validateInventory0(envelope.Inventory, recomputedInventory);

    ledger.push({
      phase: 'RecomputeMaterializedScaffoldInventory0',
      status: inventory.ok ? 'pass' : 'fail',
      digest: digestCanonical0(inventory.nf ?? inventory.witness ?? null),
    });

    if (!inventory.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.inventory`,
        path: inventory.path,
        witness: inventory.witness,
        ledger,
      });
    }
  } else {
    ledger.push({
      phase: 'RecomputeMaterializedScaffoldInventory0',
      status: 'pass',
      digest: digestCanonical0({
        skipped: true,
        recomputedInventoryDigest: digestCanonical0(recomputedInventory),
      }),
    });
  }

  if (cfg.checkPolicy === true) {
    const policy = validateScaffoldPolicy0(recomputedInventory, cfg);

    ledger.push({
      phase: 'CheckMaterializedScaffoldPolicy0',
      status: policy.ok ? 'pass' : 'fail',
      digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
    });

    if (!policy.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.policy`,
        path: policy.path,
        witness: policy.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

    ledger.push({
      phase: 'CheckMaterializedScaffoldJson0',
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
    const linkage = validateLinkage0(envelope, recomputedInventory);

    ledger.push({
      phase: 'CheckMaterializedScaffoldLinkage0',
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

  const nf = {
    kind: 'MaterializedScaffoldBurndown0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_SCAFFOLD_BURNDOWN_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,
    mode: cfg.mode,
    status: recomputedInventory.hitCount === 0 ? 'clean' : 'scaffolded',
    strictReady: recomputedInventory.hitCount === 0,
    targetKind: envelope.FinalCertificatePublicStatusEnvelope.kind ?? null,
    targetDigest: digestCanonical0(envelope.FinalCertificatePublicStatusEnvelope),
    inventoryDigest: digestCanonical0(recomputedInventory),
    markerSet: [...MATERIALIZED_SCAFFOLD_MARKERS0],
    markerHitCount: recomputedInventory.hitCount,
    syntheticMarkerCount: recomputedInventory.syntheticMarkerCount,
    forbiddenMarkerCount: recomputedInventory.forbiddenMarkerCount,
    byMarker: recomputedInventory.byMarker,
    byTopPath: recomputedInventory.byTopPath,
    firstHit: recomputedInventory.hits[0] ?? null,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
    forbiddenMarkers: cfg.forbiddenMarkers,
  };

  ledger.push({
    phase: 'EmitMaterializedScaffoldBurndown0',
    status: 'pass',
    digest: digestCanonical0(nf),
  });

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedScaffoldBurndownFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedScaffoldBurndownFiles0 requires a non-empty output directory');
  }

  const envelope = await makeMaterializedScaffoldBurndown0(options);
  const checked = await CheckMaterializedScaffoldBurndown0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedScaffoldBurndown0.json');
  const inventoryPath = path.join(outDir, 'MaterializedScaffoldInventory0.json');
  const targetPath = path.join(outDir, 'FinalCertificatePublicStatus0.json');
  const checkPath = path.join(outDir, 'MaterializedScaffoldBurndown0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(inventoryPath, envelope.Inventory);
  await writeJsonFile0(targetPath, envelope.FinalCertificatePublicStatusEnvelope);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      inventoryPath,
      targetPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'FinalCertificatePublicStatus0') {
    const inventory = makeMaterializedScaffoldInventory0(input);

    return {
      kind: 'MaterializedScaffoldBurndown0',
      version: CHECKER_VERSION,
      TargetKind: input.kind,
      FinalCertificatePublicStatusEnvelope: input,
      Inventory: inventory,
      Linkage: {
        kind: 'MaterializedScaffoldBurndownLinkage0',
        version: CHECKER_VERSION,
        targetDigest: digestCanonical0(input),
        inventoryDigest: digestCanonical0(inventory),
        markerHitCount: inventory.hitCount,
        syntheticMarkerCount: inventory.syntheticMarkerCount,
        forbiddenMarkerCount: inventory.forbiddenMarkerCount,
      },
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedScaffoldBurndownConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedScaffoldBurndownConfig0') {
    return validationReject0(['kind'], 'MaterializedScaffoldBurndownConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedScaffoldBurndownConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (!['audit', 'strict'].includes(config.mode)) {
    return validationReject0(['mode'], 'MaterializedScaffoldBurndownConfig0 mode must be audit or strict', {
      actual: config.mode,
    });
  }

  for (const field of [
    'checkFinalCertificatePublicStatus',
    'checkInventory',
    'checkPolicy',
    'checkJsonMaterialized',
    'checkLinkage',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedScaffoldBurndownConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!Array.isArray(config.forbiddenMarkers) || !config.forbiddenMarkers.every((entry) => typeof entry === 'string')) {
    return validationReject0(['forbiddenMarkers'], 'forbiddenMarkers must be an array of strings', {
      actual: config.forbiddenMarkers,
    });
  }

  if (!isPlainObject(config.finalCertificatePublicStatusConfig)) {
    return validationReject0(['finalCertificatePublicStatusConfig'], 'finalCertificatePublicStatusConfig must be an object', {
      actual: typeof config.finalCertificatePublicStatusConfig,
    });
  }

  return validationAccept0({
    kind: 'MaterializedScaffoldBurndownConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedScaffoldBurndown0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedScaffoldBurndown0') {
    return validationReject0(['kind'], 'MaterializedScaffoldBurndown0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedScaffoldBurndown0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.FinalCertificatePublicStatusEnvelope)) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope'], 'MaterializedScaffoldBurndown0 must include FinalCertificatePublicStatusEnvelope', {
      actual: typeof envelope.FinalCertificatePublicStatusEnvelope,
    });
  }

  if (!isPlainObject(envelope.Inventory)) {
    return validationReject0(['Inventory'], 'MaterializedScaffoldBurndown0 must include Inventory', {
      actual: typeof envelope.Inventory,
    });
  }

  return validationAccept0({
    kind: 'MaterializedScaffoldBurndownShape0NF',
  });
}

function validateInventory0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['Inventory'], 'MaterializedScaffoldBurndown inventory must match recomputed marker inventory', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
      expectedHitCount: expected.hitCount,
      actualHitCount: actual?.hitCount ?? null,
    });
  }

  return validationAccept0({
    kind: 'MaterializedScaffoldInventoryMatch0NF',
    inventoryDigest: digestCanonical0(expected),
    hitCount: expected.hitCount,
  });
}

function validateScaffoldPolicy0(inventory, config) {
  if (config.rejectFixtureMarkers !== true) {
    return validationAccept0({
      kind: 'MaterializedScaffoldPolicySkipped0NF',
      skipped: true,
    });
  }

  const disallowed = inventory.hits.filter((hit) => {
    if (config.mode === 'strict') {
      return true;
    }

    if (hit.marker === 'synthetic' && config.allowSyntheticScaffoldMarker === true) {
      return false;
    }

    return config.forbiddenMarkers.includes(hit.marker);
  });

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'materialized scaffold marker is not allowed by current policy', {
      hit: disallowed[0],
      disallowedHitCount: disallowed.length,
      mode: config.mode,
      allowSyntheticScaffoldMarker: config.allowSyntheticScaffoldMarker,
    });
  }

  return validationAccept0({
    kind: 'MaterializedScaffoldPolicy0NF',
    mode: config.mode,
    hitCount: inventory.hitCount,
    syntheticMarkerCount: inventory.syntheticMarkerCount,
    forbiddenMarkerCount: inventory.forbiddenMarkerCount,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['MaterializedScaffoldBurndown0'], 'MaterializedScaffoldBurndown0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['MaterializedScaffoldBurndown0'], 'MaterializedScaffoldBurndown0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedScaffoldJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, inventory) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedScaffoldLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedScaffoldBurndown0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    targetDigest: digestCanonical0(envelope.FinalCertificatePublicStatusEnvelope),
    inventoryDigest: digestCanonical0(inventory),
    markerHitCount: inventory.hitCount,
    syntheticMarkerCount: inventory.syntheticMarkerCount,
    forbiddenMarkerCount: inventory.forbiddenMarkerCount,
  };

  for (const [field, value] of Object.entries(expected)) {
    if (isDigestLike0(value)) {
      if (!sameDigestHex0(envelope.Linkage[field], value)) {
        return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
          expected: value,
          actual: envelope.Linkage[field],
        });
      }

      continue;
    }

    if (envelope.Linkage[field] !== value) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: value,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedScaffoldLinkage0NF',
    present: true,
    ...expected,
  });
}

function scanMarkerValues0(value, path, hits, markers) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of markers) {
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
      scanMarkerValues0(value[index], [...path, index], hits, markers);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    scanMarkerValues0(value[key], [...path, key], hits, markers);
  }
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function isDigestLike0(value) {
  return (
    isPlainObject(value) &&
    typeof value.hex === 'string' &&
    /^[0-9a-f]{64}$/.test(value.hex)
  );
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
