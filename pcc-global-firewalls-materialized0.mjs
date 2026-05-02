import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckBounds0,
  CheckGlobalFirewalls0,
  CheckImportGraph0,
  CheckNoHiddenMin0,
  GLOBAL_FIREWALL_PHASES0,
  makeSyntheticGlobalFirewalls0,
} from './pcc-global-firewalls0.mjs';

import {
  CheckMaterializedLocalPackages0,
  makeMaterializedLocalPackages0,
} from './pcc-local-packages-materialized0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_FIREWALL_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedGlobalFirewallsConfig0(overrides = {}) {
  return {
    kind: 'MaterializedGlobalFirewallsConfig0',
    version: CHECKER_VERSION,
    checkLocalPackages: true,
    checkGlobalFirewalls: true,
    checkSubphases: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    checkLinkage: true,
    ...overrides,
  };
}

export function makeMaterializedGlobalFirewallsPack0({
  LocalPackages = null,
  overrides = {},
} = {}) {
  const localPackages = resolveLocalPackages0(LocalPackages);
  const localSchedHash = localPackages?.SchedHash ?? null;
  const localIfaceHash = localPackages?.IfaceHash ?? null;

  const base = makeSyntheticGlobalFirewalls0();

  const bounds = {
    ...base.Bounds,
    families: base.Bounds.families.map((entry) => ({
      ...entry,
      scheduleHash: localSchedHash?.hex ?? 'materialized-schedule',
    })),
    PiBounds: {
      kind: 'PiBounds0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-global-bounds',
      note: 'materialized global bounds proof references',
      refs: [],
    },
  };

  return {
    ...base,
    SchedHash: localSchedHash ?? base.SchedHash,
    IfaceHash: localIfaceHash ?? base.IfaceHash,
    Bounds: bounds,
    PiFirewalls: {
      kind: 'PiFirewalls0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-global-firewalls',
      note: 'materialized global firewall proof references',
      refs: [],
    },
    ...overrides,
  };
}

export function makeMaterializedGlobalFirewalls0({
  LocalPackagesEnvelope = null,
  GlobalFirewalls = null,
  overrides = {},
} = {}) {
  const localPackagesEnvelope = LocalPackagesEnvelope ?? makeMaterializedLocalPackages0();
  const localPackages = resolveLocalPackages0(localPackagesEnvelope);

  const globalFirewalls = GlobalFirewalls ?? makeMaterializedGlobalFirewallsPack0({
    LocalPackages: localPackagesEnvelope,
  });

  const linkage = {
    kind: 'MaterializedGlobalFirewallsLinkage0',
    version: CHECKER_VERSION,
    localPackagesDigest: digestCanonical0(localPackages),
    globalFirewallsDigest: digestCanonical0(globalFirewalls),
    importGraphDigest: digestCanonical0(globalFirewalls.ImportGraph),
    noHiddenMinDigest: digestCanonical0(globalFirewalls.NoHiddenMinScan),
    boundsDigest: digestCanonical0(globalFirewalls.Bounds),
    schedHash: globalFirewalls.SchedHash,
    ifaceHash: globalFirewalls.IfaceHash,
    phaseOrder: [...GLOBAL_FIREWALL_PHASES0],
  };

  return {
    kind: 'MaterializedGlobalFirewalls0',
    version: CHECKER_VERSION,
    LocalPackagesEnvelope: localPackagesEnvelope,
    GlobalFirewalls: globalFirewalls,
    Linkage: linkage,
    PiMaterializedGlobalFirewalls: {
      kind: 'PiMaterializedGlobalFirewalls0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'LocalPackages',
          digest: linkage.localPackagesDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'GlobalFirewalls',
          digest: linkage.globalFirewallsDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckMaterializedGlobalFirewalls0(input, config = makeMaterializedGlobalFirewallsConfig0()) {
  const checker = 'CheckMaterializedGlobalFirewalls0';
  const ledger = [];
  const cfg = makeMaterializedGlobalFirewallsConfig0(config);
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

  if (cfg.checkLocalPackages === true) {
    const localRecord = await CheckMaterializedLocalPackages0(envelope.LocalPackagesEnvelope);
    const local = recordToValidation0(localRecord, ['LocalPackagesEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedLocalPackages0',
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

  if (cfg.checkGlobalFirewalls === true) {
    const firewallRecord = await CheckGlobalFirewalls0(envelope.GlobalFirewalls);
    const firewalls = recordToValidation0(firewallRecord, ['GlobalFirewalls']);

    ledger.push({
      phase: 'CheckGlobalFirewalls0',
      status: firewalls.ok ? 'pass' : 'fail',
      digest: firewallRecord.Digest ?? firewallRecord.digest ?? digestCanonical0(firewallRecord),
    });

    if (!firewalls.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GlobalFirewalls`,
        path: firewalls.path,
        witness: firewalls.witness,
        ledger,
      });
    }
  }

  if (cfg.checkSubphases === true) {
    const subphaseResult = await validateSubphases0(envelope.GlobalFirewalls);

    ledger.push({
      phase: 'subphases',
      status: subphaseResult.ok ? 'pass' : 'fail',
      digest: digestCanonical0(subphaseResult.nf ?? subphaseResult.witness ?? null),
    });

    if (!subphaseResult.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.subphases`,
        path: subphaseResult.path,
        witness: subphaseResult.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope.GlobalFirewalls);

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
      GlobalFirewalls: envelope.GlobalFirewalls,
      PiMaterializedGlobalFirewalls: envelope.PiMaterializedGlobalFirewalls ?? null,
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

  const firewallRecord = await CheckGlobalFirewalls0(envelope.GlobalFirewalls);
  const firewallNF = firewallRecord.NF ?? firewallRecord.nf ?? {};
  const localPackages = resolveLocalPackages0(envelope.LocalPackagesEnvelope);

  const nf = {
    kind: 'MaterializedGlobalFirewalls0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    localPackagesDigest: digestCanonical0(localPackages),
    globalFirewallsDigest: firewallRecord.Digest ?? firewallRecord.digest,
    globalFirewallsObjectDigest: digestCanonical0(envelope.GlobalFirewalls),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    phases: firewallNF.phases ?? GLOBAL_FIREWALL_PHASES0,
    familyCount: firewallNF.familyCount ?? null,
    forbiddenImportEdges: firewallNF.forbiddenImportEdges ?? [],
    forbiddenExecutableSymbols: firewallNF.forbiddenExecutableSymbols ?? [],
    importGraphDigest: firewallNF.importGraphDigest ?? digestCanonical0(envelope.GlobalFirewalls.ImportGraph),
    noHiddenMinDigest: firewallNF.noHiddenMinDigest ?? digestCanonical0(envelope.GlobalFirewalls.NoHiddenMinScan),
    boundsDigest: firewallNF.boundsDigest ?? digestCanonical0(envelope.GlobalFirewalls.Bounds),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedGlobalFirewallsFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedGlobalFirewallsFiles0 requires a non-empty output directory');
  }

  const envelope = makeMaterializedGlobalFirewalls0(options);
  const checked = await CheckMaterializedGlobalFirewalls0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedGlobalFirewalls0.json');
  const localPackagesPath = path.join(outDir, 'LocalPackagePack0.json');
  const globalFirewallsPath = path.join(outDir, 'GlobalFirewalls0.json');
  const importGraphPath = path.join(outDir, 'ImportGraph0.json');
  const noHiddenMinPath = path.join(outDir, 'NoHiddenMinScan0.json');
  const boundsPath = path.join(outDir, 'Bounds0.json');
  const checkPath = path.join(outDir, 'MaterializedGlobalFirewalls0.check.json');

  const localPackages = resolveLocalPackages0(envelope.LocalPackagesEnvelope);

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(localPackagesPath, localPackages);
  await writeJsonFile0(globalFirewallsPath, envelope.GlobalFirewalls);
  await writeJsonFile0(importGraphPath, envelope.GlobalFirewalls.ImportGraph);
  await writeJsonFile0(noHiddenMinPath, envelope.GlobalFirewalls.NoHiddenMinScan);
  await writeJsonFile0(boundsPath, envelope.GlobalFirewalls.Bounds);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      localPackagesPath,
      globalFirewallsPath,
      importGraphPath,
      noHiddenMinPath,
      boundsPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'GlobalFirewalls0') {
    return makeMaterializedGlobalFirewalls0({
      GlobalFirewalls: input,
    });
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedGlobalFirewallsConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedGlobalFirewallsConfig0') {
    return validationReject0(['kind'], 'MaterializedGlobalFirewallsConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedGlobalFirewallsConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkLocalPackages',
    'checkGlobalFirewalls',
    'checkSubphases',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedGlobalFirewallsConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedGlobalFirewallsConfig0NF',
  });
}

function validateShape0(envelope, config) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedGlobalFirewalls0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedGlobalFirewalls0') {
    return validationReject0(['kind'], 'MaterializedGlobalFirewalls0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedGlobalFirewalls0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (config.checkLocalPackages === true && !isPlainObject(envelope.LocalPackagesEnvelope)) {
    return validationReject0(['LocalPackagesEnvelope'], 'MaterializedGlobalFirewalls0 must include LocalPackagesEnvelope when checkLocalPackages=true', {
      actual: typeof envelope.LocalPackagesEnvelope,
    });
  }

  if (!isPlainObject(envelope.GlobalFirewalls)) {
    return validationReject0(['GlobalFirewalls'], 'MaterializedGlobalFirewalls0 must include GlobalFirewalls', {
      actual: typeof envelope.GlobalFirewalls,
    });
  }

  if (envelope.GlobalFirewalls.kind !== 'GlobalFirewalls0') {
    return validationReject0(['GlobalFirewalls', 'kind'], 'GlobalFirewalls kind must be GlobalFirewalls0', {
      actual: envelope.GlobalFirewalls.kind,
    });
  }

  return validationAccept0({
    kind: 'MaterializedGlobalFirewallsShape0NF',
  });
}

async function validateSubphases0(globalFirewalls) {
  const phases = [
    ['ImportGraph', await CheckImportGraph0(globalFirewalls.ImportGraph)],
    ['NoHiddenMinScan', await CheckNoHiddenMin0(globalFirewalls.NoHiddenMinScan)],
    ['Bounds', await CheckBounds0(globalFirewalls.Bounds)],
  ];

  const phaseDigests = [];

  for (const [pathName, record] of phases) {
    if (isRejectRecord0(record)) {
      return validationReject0(['GlobalFirewalls', pathName], `${record.checker} rejected`, {
        inner: compactReject0(record),
      });
    }

    phaseDigests.push({
      pathName,
      checker: record.checker,
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });
  }

  return validationAccept0({
    kind: 'MaterializedGlobalFirewallSubphases0NF',
    phaseDigests,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['GlobalFirewalls'], 'GlobalFirewalls must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['GlobalFirewalls'], 'GlobalFirewalls canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedGlobalFirewallsJson0NF',
    byteLength: bytes.length,
    globalFirewallsDigest: digestCanonical0(value),
  });
}

function validateNoFixtureMarkers0(value) {
  const hit = firstFixtureMarker0(value, ['MaterializedGlobalFirewalls0']);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized GlobalFirewalls must not contain fixture-marker text', hit);
  }

  return validationAccept0({
    kind: 'MaterializedGlobalFirewallsNoFixtureMarkers0NF',
  });
}

function validateLinkage0(envelope) {
  const localPackages = resolveLocalPackages0(envelope.LocalPackagesEnvelope);

  if (!isPlainObject(localPackages)) {
    return validationReject0(['LocalPackagesEnvelope', 'LocalPackages'], 'LocalPackages must be present for GlobalFirewalls linkage', {
      actual: typeof localPackages,
    });
  }

  if (!sameDigestHex0(envelope.GlobalFirewalls.SchedHash, localPackages.SchedHash)) {
    return validationReject0(['GlobalFirewalls', 'SchedHash'], 'GlobalFirewalls SchedHash must match LocalPackages SchedHash', {
      expected: localPackages.SchedHash,
      actual: envelope.GlobalFirewalls.SchedHash,
    });
  }

  if (!sameDigestHex0(envelope.GlobalFirewalls.IfaceHash, localPackages.IfaceHash)) {
    return validationReject0(['GlobalFirewalls', 'IfaceHash'], 'GlobalFirewalls IfaceHash must match LocalPackages IfaceHash', {
      expected: localPackages.IfaceHash,
      actual: envelope.GlobalFirewalls.IfaceHash,
    });
  }

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedGlobalFirewallsLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedGlobalFirewalls0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expectedGlobalDigest = digestCanonical0(envelope.GlobalFirewalls);

  if (!sameDigestHex0(envelope.Linkage.globalFirewallsDigest, expectedGlobalDigest)) {
    return validationReject0(['Linkage', 'globalFirewallsDigest'], 'Linkage globalFirewallsDigest must match GlobalFirewalls canonical object digest', {
      expected: expectedGlobalDigest,
      actual: envelope.Linkage.globalFirewallsDigest,
    });
  }

  const expectedLocalDigest = digestCanonical0(localPackages);

  if (!sameDigestHex0(envelope.Linkage.localPackagesDigest, expectedLocalDigest)) {
    return validationReject0(['Linkage', 'localPackagesDigest'], 'Linkage localPackagesDigest must match LocalPackages canonical object digest', {
      expected: expectedLocalDigest,
      actual: envelope.Linkage.localPackagesDigest,
    });
  }

  if (!Array.isArray(envelope.Linkage.phaseOrder)) {
    return validationReject0(['Linkage', 'phaseOrder'], 'Linkage phaseOrder must be an array', {
      actual: typeof envelope.Linkage.phaseOrder,
    });
  }

  for (let index = 0; index < GLOBAL_FIREWALL_PHASES0.length; index += 1) {
    if (envelope.Linkage.phaseOrder[index] !== GLOBAL_FIREWALL_PHASES0[index]) {
      return validationReject0(['Linkage', 'phaseOrder', index], 'Linkage phaseOrder mismatch', {
        expected: GLOBAL_FIREWALL_PHASES0[index],
        actual: envelope.Linkage.phaseOrder[index],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedGlobalFirewallsLinkage0NF',
    present: true,
    localPackagesDigest: expectedLocalDigest,
    globalFirewallsDigest: expectedGlobalDigest,
  });
}

function firstFixtureMarker0(value, path) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_FIREWALL_FORBIDDEN_MARKERS0) {
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

    for (const marker of MATERIALIZED_FIREWALL_FORBIDDEN_MARKERS0) {
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

function resolveLocalPackages0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  if (value.kind === 'LocalPackagePack0') {
    return value;
  }

  return (
    value.LocalPackages ??
    value.localPackages ??
    value.LocalPackagePack ??
    value.localPackagePack ??
    null
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
