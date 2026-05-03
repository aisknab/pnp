import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGlobalFirewalls0,
  CheckImportGraph0,
  CheckNoHiddenMin0,
  CheckBounds0,
  GLOBAL_FIREWALL_PHASES0,
} from './pcc-global-firewalls0.mjs';

import {
  CheckMaterializedGlobalFirewalls0,
  makeMaterializedGlobalFirewalls0,
  makeMaterializedGlobalFirewallsPack0,
} from './pcc-global-firewalls-materialized0.mjs';

import {
  CheckConcreteMaterializedLocalPackages0,
  makeConcreteMaterializedLocalPackages0,
} from './pcc-local-packages-concrete-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_FIREWALL_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_FIREWALL_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteMaterializedGlobalFirewallsConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedGlobalFirewallsConfig0',
    version: CHECKER_VERSION,
    checkConcreteLocalPackages: true,
    checkMaterializedGlobalFirewalls: true,
    checkGlobalFirewalls: true,
    checkSubphases: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    ...overrides,
  };
}

export async function makeConcreteMaterializedGlobalFirewalls0({
  ConcreteLocalPackagesEnvelope = null,
  GlobalFirewalls = null,
  overrides = {},
} = {}) {
  const concreteLocalPackagesEnvelope = ConcreteLocalPackagesEnvelope ?? await makeConcreteMaterializedLocalPackages0();
  const localPackages = resolveLocalPackages0(concreteLocalPackagesEnvelope);

  if (!isPlainObject(localPackages)) {
    throw new TypeError('makeConcreteMaterializedGlobalFirewalls0 requires concrete LocalPackages');
  }

  const globalFirewalls = GlobalFirewalls ?? makeMaterializedGlobalFirewallsPack0({
    LocalPackages: concreteLocalPackagesEnvelope,
  });

  const linkage = {
    kind: 'ConcreteMaterializedGlobalFirewallsLinkage0',
    version: CHECKER_VERSION,
    concreteLocalPackagesDigest: digestCanonical0(concreteLocalPackagesEnvelope),
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
    kind: 'ConcreteMaterializedGlobalFirewalls0',
    version: CHECKER_VERSION,
    ConcreteLocalPackagesEnvelope: concreteLocalPackagesEnvelope,
    LocalPackages: localPackages,
    GlobalFirewalls: globalFirewalls,
    Linkage: linkage,
    PiConcreteMaterializedGlobalFirewalls: {
      kind: 'PiConcreteMaterializedGlobalFirewalls0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteLocalPackagesEnvelope',
          digest: linkage.concreteLocalPackagesDigest,
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

export async function CheckConcreteMaterializedGlobalFirewalls0(
  input,
  config = makeConcreteMaterializedGlobalFirewallsConfig0(),
) {
  const checker = 'CheckConcreteMaterializedGlobalFirewalls0';
  const ledger = [];
  const cfg = makeConcreteMaterializedGlobalFirewallsConfig0(config);
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

  if (cfg.checkConcreteLocalPackages === true) {
    const localRecord = await CheckConcreteMaterializedLocalPackages0(envelope.ConcreteLocalPackagesEnvelope);
    const local = recordToValidation0(localRecord, ['ConcreteLocalPackagesEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedLocalPackages0',
      status: local.ok ? 'pass' : 'fail',
      digest: localRecord.Digest ?? localRecord.digest ?? digestCanonical0(localRecord),
    });

    if (!local.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteLocalPackages`,
        path: local.path,
        witness: local.witness,
        ledger,
      });
    }
  }

  if (cfg.checkMaterializedGlobalFirewalls === true) {
    const materializedEnvelope = makeMaterializedGlobalFirewalls0({
      LocalPackagesEnvelope: envelope.ConcreteLocalPackagesEnvelope,
      GlobalFirewalls: envelope.GlobalFirewalls,
    });

    const materializedRecord = await CheckMaterializedGlobalFirewalls0(materializedEnvelope, {
      checkLocalPackages: false,
    });
    const materialized = recordToValidation0(materializedRecord, ['GlobalFirewalls']);

    ledger.push({
      phase: 'CheckMaterializedGlobalFirewalls0',
      status: materialized.ok ? 'pass' : 'fail',
      digest: materializedRecord.Digest ?? materializedRecord.digest ?? digestCanonical0(materializedRecord),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedGlobalFirewalls`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }
  }

  if (cfg.checkGlobalFirewalls === true) {
    const globalRecord = await CheckGlobalFirewalls0(envelope.GlobalFirewalls);
    const global = recordToValidation0(globalRecord, ['GlobalFirewalls']);

    ledger.push({
      phase: 'CheckGlobalFirewalls0',
      status: global.ok ? 'pass' : 'fail',
      digest: globalRecord.Digest ?? globalRecord.digest ?? digestCanonical0(globalRecord),
    });

    if (!global.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GlobalFirewalls`,
        path: global.path,
        witness: global.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope.GlobalFirewalls, ['GlobalFirewalls']);

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

  const globalRecord = await CheckGlobalFirewalls0(envelope.GlobalFirewalls);
  const globalNF = globalRecord.NF ?? globalRecord.nf ?? {};

  const nf = {
    kind: 'ConcreteMaterializedGlobalFirewalls0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    concreteLocalPackages: true,
    concreteLocalPackagesEnvelopeKind: envelope.ConcreteLocalPackagesEnvelope.kind,
    globalFirewallsDigest: globalRecord.Digest ?? globalRecord.digest,
    globalFirewallsObjectDigest: digestCanonical0(envelope.GlobalFirewalls),
    concreteLocalPackagesDigest: digestCanonical0(envelope.ConcreteLocalPackagesEnvelope),
    localPackagesDigest: digestCanonical0(envelope.LocalPackages),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    phases: globalNF.phases ?? GLOBAL_FIREWALL_PHASES0,
    familyCount: globalNF.familyCount ?? null,
    forbiddenImportEdges: globalNF.forbiddenImportEdges ?? [],
    forbiddenExecutableSymbols: globalNF.forbiddenExecutableSymbols ?? [],
    importGraphDigest: globalNF.importGraphDigest ?? digestCanonical0(envelope.GlobalFirewalls.ImportGraph),
    noHiddenMinDigest: globalNF.noHiddenMinDigest ?? digestCanonical0(envelope.GlobalFirewalls.NoHiddenMinScan),
    boundsDigest: globalNF.boundsDigest ?? digestCanonical0(envelope.GlobalFirewalls.Bounds),
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

export async function writeConcreteMaterializedGlobalFirewallsFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedGlobalFirewallsFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedGlobalFirewalls0(options);
  const checked = await CheckConcreteMaterializedGlobalFirewalls0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedGlobalFirewalls0.json');
  const localPackagesPath = path.join(outDir, 'ConcreteLocalPackagePack0.json');
  const globalFirewallsPath = path.join(outDir, 'ConcreteGlobalFirewalls0.json');
  const importGraphPath = path.join(outDir, 'ConcreteImportGraph0.json');
  const noHiddenMinPath = path.join(outDir, 'ConcreteNoHiddenMinScan0.json');
  const boundsPath = path.join(outDir, 'ConcreteBounds0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedGlobalFirewalls0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(localPackagesPath, envelope.LocalPackages);
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

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'GlobalFirewalls0') {
    return {
      kind: 'ConcreteMaterializedGlobalFirewalls0',
      version: CHECKER_VERSION,
      ConcreteLocalPackagesEnvelope: null,
      LocalPackages: null,
      GlobalFirewalls: input,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedGlobalFirewallsConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedGlobalFirewallsConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedGlobalFirewallsConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedGlobalFirewallsConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteLocalPackages',
    'checkMaterializedGlobalFirewalls',
    'checkGlobalFirewalls',
    'checkSubphases',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedGlobalFirewallsConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGlobalFirewallsConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedGlobalFirewalls0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedGlobalFirewalls0') {
    return validationReject0(['kind'], 'ConcreteMaterializedGlobalFirewalls0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedGlobalFirewalls0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ConcreteLocalPackagesEnvelope)) {
    return validationReject0(['ConcreteLocalPackagesEnvelope'], 'ConcreteMaterializedGlobalFirewalls0 must include ConcreteLocalPackagesEnvelope', {
      actual: typeof envelope.ConcreteLocalPackagesEnvelope,
    });
  }

  if (!isPlainObject(envelope.LocalPackages)) {
    return validationReject0(['LocalPackages'], 'ConcreteMaterializedGlobalFirewalls0 must include LocalPackages', {
      actual: typeof envelope.LocalPackages,
    });
  }

  if (!isPlainObject(envelope.GlobalFirewalls)) {
    return validationReject0(['GlobalFirewalls'], 'ConcreteMaterializedGlobalFirewalls0 must include GlobalFirewalls', {
      actual: typeof envelope.GlobalFirewalls,
    });
  }

  if (envelope.GlobalFirewalls.kind !== 'GlobalFirewalls0') {
    return validationReject0(['GlobalFirewalls', 'kind'], 'GlobalFirewalls kind must be GlobalFirewalls0', {
      actual: envelope.GlobalFirewalls.kind,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGlobalFirewallsShape0NF',
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
    kind: 'ConcreteMaterializedGlobalFirewallSubphases0NF',
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
    kind: 'ConcreteMaterializedGlobalFirewallsJson0NF',
    byteLength: bytes.length,
    globalFirewallsDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope) {
  const expectedConcreteLocalPackagesDigest = digestCanonical0(envelope.ConcreteLocalPackagesEnvelope);
  const expectedLocalPackagesDigest = digestCanonical0(envelope.LocalPackages);
  const expectedGlobalDigest = digestCanonical0(envelope.GlobalFirewalls);

  if (!sameDigestHex0(envelope.GlobalFirewalls.SchedHash, envelope.LocalPackages.SchedHash)) {
    return validationReject0(['GlobalFirewalls', 'SchedHash'], 'GlobalFirewalls SchedHash must match concrete LocalPackages SchedHash', {
      expected: envelope.LocalPackages.SchedHash,
      actual: envelope.GlobalFirewalls.SchedHash,
    });
  }

  if (!sameDigestHex0(envelope.GlobalFirewalls.IfaceHash, envelope.LocalPackages.IfaceHash)) {
    return validationReject0(['GlobalFirewalls', 'IfaceHash'], 'GlobalFirewalls IfaceHash must match concrete LocalPackages IfaceHash', {
      expected: envelope.LocalPackages.IfaceHash,
      actual: envelope.GlobalFirewalls.IfaceHash,
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.ConcreteLocalPackagesEnvelope.LocalPackages), expectedLocalPackagesDigest)) {
    return validationReject0(['ConcreteLocalPackagesEnvelope', 'LocalPackages'], 'ConcreteLocalPackagesEnvelope LocalPackages must match top-level LocalPackages', {
      expected: expectedLocalPackagesDigest,
      actual: digestCanonical0(envelope.ConcreteLocalPackagesEnvelope.LocalPackages),
    });
  }

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteMaterializedGlobalFirewallsLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedGlobalFirewalls0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const checks = [
    ['concreteLocalPackagesDigest', expectedConcreteLocalPackagesDigest],
    ['localPackagesDigest', expectedLocalPackagesDigest],
    ['globalFirewallsDigest', expectedGlobalDigest],
    ['importGraphDigest', digestCanonical0(envelope.GlobalFirewalls.ImportGraph)],
    ['noHiddenMinDigest', digestCanonical0(envelope.GlobalFirewalls.NoHiddenMinScan)],
    ['boundsDigest', digestCanonical0(envelope.GlobalFirewalls.Bounds)],
  ];

  for (const [field, expected] of checks) {
    if (!sameDigestHex0(envelope.Linkage[field], expected)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected,
        actual: envelope.Linkage[field],
      });
    }
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
    kind: 'ConcreteMaterializedGlobalFirewallsLinkage0NF',
    present: true,
    concreteLocalPackagesDigest: expectedConcreteLocalPackagesDigest,
    localPackagesDigest: expectedLocalPackagesDigest,
    globalFirewallsDigest: expectedGlobalDigest,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteMaterializedGlobalFirewallsFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_FIREWALL_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_FIREWALL_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_FIREWALL_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized GlobalFirewalls contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGlobalFirewallsNoForbiddenFixtureMarkers0NF',
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
      CONCRETE_FIREWALL_SYNTHETIC_MARKER0,
      ...CONCRETE_FIREWALL_FORBIDDEN_MARKERS0,
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
