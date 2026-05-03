import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedBoot0,
  makeMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

import {
  CheckMaterializedKBundle0,
  makeMaterializedKBundle0,
} from './pcc-k-materialized0.mjs';

import {
  CheckConcreteMaterializedRows0,
  makeConcreteMaterializedRows0,
} from './pcc-rows-concrete-materialized0.mjs';

import {
  CheckConcreteMaterializedLocalPackages0,
  makeConcreteMaterializedLocalPackages0,
} from './pcc-local-packages-concrete-materialized0.mjs';

import {
  CheckConcreteMaterializedGlobalFirewalls0,
  makeConcreteMaterializedGlobalFirewalls0,
} from './pcc-global-firewalls-concrete-materialized0.mjs';

import {
  CheckMaterializedGlobalProofDAG0,
  makeMaterializedGlobalProofDAG0,
} from './pcc-global-proof-dag-materialized0.mjs';

import {
  CheckGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_GLOBAL_DAG_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_GLOBAL_DAG_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteMaterializedGlobalProofDAGConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedGlobalProofDAGConfig0',
    version: CHECKER_VERSION,
    checkBoot: true,
    checkKBundle: true,
    checkConcreteRows: true,
    checkConcreteLocalPackages: true,
    checkConcreteGlobalFirewalls: true,
    checkMaterializedGlobalProofDAG: true,
    checkGlobalProofDAG: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    ...overrides,
  };
}

export async function makeConcreteMaterializedGlobalProofDAG0({
  Boot0 = null,
  KBundleEnvelope = null,
  ConcreteRowsEnvelope = null,
  ConcreteLocalPackagesEnvelope = null,
  ConcreteGlobalFirewallsEnvelope = null,
  MaterializedGlobalProofDAGEnvelope = null,
  GlobalProofDAG = null,
  overrides = {},
} = {}) {
  const boot0 = Boot0 ?? await makeMaterializedBoot0();

  const kBundleEnvelope = KBundleEnvelope ?? await makeMaterializedKBundle0({
    Boot0: boot0,
  });

  const concreteRowsEnvelope = ConcreteRowsEnvelope ?? await makeConcreteMaterializedRows0({
    Boot0: boot0,
  });

  const concreteLocalPackagesEnvelope = ConcreteLocalPackagesEnvelope ?? await makeConcreteMaterializedLocalPackages0({
    ConcreteRowsEnvelope: concreteRowsEnvelope,
  });

  const concreteGlobalFirewallsEnvelope = ConcreteGlobalFirewallsEnvelope ?? await makeConcreteMaterializedGlobalFirewalls0({
    ConcreteLocalPackagesEnvelope: concreteLocalPackagesEnvelope,
  });

  const materializedGlobalProofDAGEnvelope = MaterializedGlobalProofDAGEnvelope ?? await makeMaterializedGlobalProofDAG0({
    Boot0: boot0,
    KBundle: kBundleEnvelope,
    GlobalProofDAG,
  });

  const globalProofDAG = resolveGlobalProofDAG0(materializedGlobalProofDAGEnvelope);

  const linkage = {
    kind: 'ConcreteMaterializedGlobalProofDAGLinkage0',
    version: CHECKER_VERSION,
    bootDigest: digestCanonical0(boot0),
    kBundleDigest: digestCanonical0(kBundleEnvelope),
    concreteRowsDigest: digestCanonical0(concreteRowsEnvelope),
    concreteLocalPackagesDigest: digestCanonical0(concreteLocalPackagesEnvelope),
    concreteGlobalFirewallsDigest: digestCanonical0(concreteGlobalFirewallsEnvelope),
    materializedGlobalProofDAGDigest: digestCanonical0(materializedGlobalProofDAGEnvelope),
    globalProofDAGDigest: digestCanonical0(globalProofDAG),
    kImplDigest: digestCanonical0(resolveKImpl0(kBundleEnvelope)),
    rowPackDigest: digestCanonical0(resolveRowPack0(concreteRowsEnvelope)),
    localPackagesDigest: digestCanonical0(resolveLocalPackages0(concreteLocalPackagesEnvelope)),
    globalFirewallsDigest: digestCanonical0(resolveGlobalFirewalls0(concreteGlobalFirewallsEnvelope)),
    ifaceHash: globalProofDAG?.IfaceHash ?? null,
    schedHash: globalProofDAG?.SchedHash ?? null,
  };

  return {
    kind: 'ConcreteMaterializedGlobalProofDAG0',
    version: CHECKER_VERSION,
    Boot0: boot0,
    KBundleEnvelope: kBundleEnvelope,
    ConcreteRowsEnvelope: concreteRowsEnvelope,
    ConcreteLocalPackagesEnvelope: concreteLocalPackagesEnvelope,
    ConcreteGlobalFirewallsEnvelope: concreteGlobalFirewallsEnvelope,
    MaterializedGlobalProofDAGEnvelope: materializedGlobalProofDAGEnvelope,
    GlobalProofDAG: globalProofDAG,
    Linkage: linkage,
    PiConcreteMaterializedGlobalProofDAG: {
      kind: 'PiConcreteMaterializedGlobalProofDAG0',
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
          target: 'ConcreteLocalPackagesEnvelope',
          digest: linkage.concreteLocalPackagesDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteGlobalFirewallsEnvelope',
          digest: linkage.concreteGlobalFirewallsDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'GlobalProofDAG',
          digest: linkage.globalProofDAGDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckConcreteMaterializedGlobalProofDAG0(
  input,
  config = makeConcreteMaterializedGlobalProofDAGConfig0(),
) {
  const checker = 'CheckConcreteMaterializedGlobalProofDAG0';
  const ledger = [];
  const cfg = makeConcreteMaterializedGlobalProofDAGConfig0(config);
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
    const record = await CheckMaterializedBoot0(envelope.Boot0);
    const result = recordToValidation0(record, ['Boot0']);

    ledger.push({
      phase: 'CheckMaterializedBoot0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.Boot0`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkKBundle === true) {
    const record = await CheckMaterializedKBundle0(envelope.KBundleEnvelope);
    const result = recordToValidation0(record, ['KBundleEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedKBundle0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.KBundle`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkConcreteRows === true) {
    const record = await CheckConcreteMaterializedRows0(envelope.ConcreteRowsEnvelope);
    const result = recordToValidation0(record, ['ConcreteRowsEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedRows0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteRows`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkConcreteLocalPackages === true) {
    const record = await CheckConcreteMaterializedLocalPackages0(envelope.ConcreteLocalPackagesEnvelope);
    const result = recordToValidation0(record, ['ConcreteLocalPackagesEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedLocalPackages0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteLocalPackages`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkConcreteGlobalFirewalls === true) {
    const record = await CheckConcreteMaterializedGlobalFirewalls0(envelope.ConcreteGlobalFirewallsEnvelope);
    const result = recordToValidation0(record, ['ConcreteGlobalFirewallsEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedGlobalFirewalls0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteGlobalFirewalls`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkMaterializedGlobalProofDAG === true) {
    const record = await CheckMaterializedGlobalProofDAG0(envelope.MaterializedGlobalProofDAGEnvelope);
    const result = recordToValidation0(record, ['MaterializedGlobalProofDAGEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedGlobalProofDAG0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedGlobalProofDAG`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkGlobalProofDAG === true) {
    const record = await CheckGlobalProofDAG0(envelope.GlobalProofDAG);
    const result = recordToValidation0(record, ['GlobalProofDAG']);

    ledger.push({
      phase: 'CheckGlobalProofDAG0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GlobalProofDAG`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope.GlobalProofDAG);

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

  const markerInventory = collectFixtureMarkers0(envelope.GlobalProofDAG, ['GlobalProofDAG']);

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

  const dagRecord = await CheckGlobalProofDAG0(envelope.GlobalProofDAG);
  const dagNF = dagRecord.NF ?? dagRecord.nf ?? {};
  const kimpl = resolveKImpl0(envelope.KBundleEnvelope);
  const rowPack = resolveRowPack0(envelope.ConcreteRowsEnvelope);
  const localPackages = resolveLocalPackages0(envelope.ConcreteLocalPackagesEnvelope);
  const globalFirewalls = resolveGlobalFirewalls0(envelope.ConcreteGlobalFirewallsEnvelope);

  const nf = {
    kind: 'ConcreteMaterializedGlobalProofDAG0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    concreteRows: true,
    concreteLocalPackages: true,
    concreteGlobalFirewalls: true,
    globalProofDAGDigest: dagRecord.Digest ?? dagRecord.digest,
    globalProofDAGObjectDigest: digestCanonical0(envelope.GlobalProofDAG),
    materializedGlobalProofDAGDigest: digestCanonical0(envelope.MaterializedGlobalProofDAGEnvelope),
    kImplDigest: digestCanonical0(kimpl),
    rowPackDigest: digestCanonical0(rowPack),
    localPackagesDigest: digestCanonical0(localPackages),
    globalFirewallsDigest: digestCanonical0(globalFirewalls),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    nodeCount: dagNF.nodeCount ?? envelope.GlobalProofDAG.Nodes.length,
    finalTheorems: dagNF.finalTheorems ?? [],
    ifaceHash: envelope.GlobalProofDAG.IfaceHash,
    schedHash: envelope.GlobalProofDAG.SchedHash,
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

export async function writeConcreteMaterializedGlobalProofDAGFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedGlobalProofDAGFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedGlobalProofDAG0(options);
  const checked = await CheckConcreteMaterializedGlobalProofDAG0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedGlobalProofDAG0.json');
  const globalProofDAGPath = path.join(outDir, 'ConcreteGlobalProofDAG0.json');
  const materializedDAGPath = path.join(outDir, 'MaterializedGlobalProofDAG0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedGlobalProofDAG0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(globalProofDAGPath, envelope.GlobalProofDAG);
  await writeJsonFile0(materializedDAGPath, envelope.MaterializedGlobalProofDAGEnvelope);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      globalProofDAGPath,
      materializedDAGPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'GlobalProofDAG0') {
    return {
      kind: 'ConcreteMaterializedGlobalProofDAG0',
      version: CHECKER_VERSION,
      Boot0: null,
      KBundleEnvelope: null,
      ConcreteRowsEnvelope: null,
      ConcreteLocalPackagesEnvelope: null,
      ConcreteGlobalFirewallsEnvelope: null,
      MaterializedGlobalProofDAGEnvelope: null,
      GlobalProofDAG: input,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedGlobalProofDAGConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedGlobalProofDAGConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedGlobalProofDAGConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedGlobalProofDAGConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkBoot',
    'checkKBundle',
    'checkConcreteRows',
    'checkConcreteLocalPackages',
    'checkConcreteGlobalFirewalls',
    'checkMaterializedGlobalProofDAG',
    'checkGlobalProofDAG',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedGlobalProofDAGConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGlobalProofDAGConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedGlobalProofDAG0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedGlobalProofDAG0') {
    return validationReject0(['kind'], 'ConcreteMaterializedGlobalProofDAG0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedGlobalProofDAG0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  for (const field of [
    'Boot0',
    'KBundleEnvelope',
    'ConcreteRowsEnvelope',
    'ConcreteLocalPackagesEnvelope',
    'ConcreteGlobalFirewallsEnvelope',
    'MaterializedGlobalProofDAGEnvelope',
    'GlobalProofDAG',
  ]) {
    if (!isPlainObject(envelope[field])) {
      return validationReject0([field], `ConcreteMaterializedGlobalProofDAG0 must include ${field}`, {
        actual: typeof envelope[field],
      });
    }
  }

  if (envelope.GlobalProofDAG.kind !== 'GlobalProofDAG0') {
    return validationReject0(['GlobalProofDAG', 'kind'], 'GlobalProofDAG kind must be GlobalProofDAG0', {
      actual: envelope.GlobalProofDAG.kind,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGlobalProofDAGShape0NF',
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['GlobalProofDAG'], 'GlobalProofDAG must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['GlobalProofDAG'], 'GlobalProofDAG canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteGlobalProofDAGJson0NF',
    byteLength: bytes.length,
    globalProofDAGDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope) {
  const kimpl = resolveKImpl0(envelope.KBundleEnvelope);
  const rowPack = resolveRowPack0(envelope.ConcreteRowsEnvelope);
  const localPackages = resolveLocalPackages0(envelope.ConcreteLocalPackagesEnvelope);
  const globalFirewalls = resolveGlobalFirewalls0(envelope.ConcreteGlobalFirewallsEnvelope);
  const dag = envelope.GlobalProofDAG;

  if (!isPlainObject(kimpl)) {
    return validationReject0(['KBundleEnvelope', 'KImpl'], 'KBundleEnvelope must expose KImpl', {
      actual: typeof kimpl,
    });
  }

  if (!sameDigestHex0(dag.IfaceHash, kimpl.IfaceHash)) {
    return validationReject0(['GlobalProofDAG', 'IfaceHash'], 'GlobalProofDAG IfaceHash must match KImpl IfaceHash', {
      expected: kimpl.IfaceHash,
      actual: dag.IfaceHash,
    });
  }

  if (!sameDigestHex0(dag.SchedHash, kimpl.SchedHash)) {
    return validationReject0(['GlobalProofDAG', 'SchedHash'], 'GlobalProofDAG SchedHash must match KImpl SchedHash', {
      expected: kimpl.SchedHash,
      actual: dag.SchedHash,
    });
  }

  if (!sameDigestHex0(dag.IfaceHash, rowPack.IfaceHash)) {
    return validationReject0(['GlobalProofDAG', 'IfaceHash'], 'GlobalProofDAG IfaceHash must match concrete RowPack IfaceHash', {
      expected: rowPack.IfaceHash,
      actual: dag.IfaceHash,
    });
  }

  if (!sameDigestHex0(globalFirewalls.IfaceHash, localPackages.IfaceHash)) {
    return validationReject0(['ConcreteGlobalFirewallsEnvelope', 'GlobalFirewalls', 'IfaceHash'], 'GlobalFirewalls IfaceHash must match LocalPackages IfaceHash', {
      expected: localPackages.IfaceHash,
      actual: globalFirewalls.IfaceHash,
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.MaterializedGlobalProofDAGEnvelope.GlobalProofDAG), digestCanonical0(dag))) {
    return validationReject0(['MaterializedGlobalProofDAGEnvelope', 'GlobalProofDAG'], 'MaterializedGlobalProofDAGEnvelope must contain the top-level GlobalProofDAG object', {
      expected: digestCanonical0(dag),
      actual: digestCanonical0(envelope.MaterializedGlobalProofDAGEnvelope.GlobalProofDAG),
    });
  }

  const expected = {
    bootDigest: digestCanonical0(envelope.Boot0),
    kBundleDigest: digestCanonical0(envelope.KBundleEnvelope),
    concreteRowsDigest: digestCanonical0(envelope.ConcreteRowsEnvelope),
    concreteLocalPackagesDigest: digestCanonical0(envelope.ConcreteLocalPackagesEnvelope),
    concreteGlobalFirewallsDigest: digestCanonical0(envelope.ConcreteGlobalFirewallsEnvelope),
    materializedGlobalProofDAGDigest: digestCanonical0(envelope.MaterializedGlobalProofDAGEnvelope),
    globalProofDAGDigest: digestCanonical0(dag),
    kImplDigest: digestCanonical0(kimpl),
    rowPackDigest: digestCanonical0(rowPack),
    localPackagesDigest: digestCanonical0(localPackages),
    globalFirewallsDigest: digestCanonical0(globalFirewalls),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteGlobalProofDAGLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedGlobalProofDAG0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteGlobalProofDAGLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteGlobalProofDAGFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_GLOBAL_DAG_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_GLOBAL_DAG_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_GLOBAL_DAG_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized GlobalProofDAG contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteGlobalProofDAGNoForbiddenFixtureMarkers0NF',
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
      CONCRETE_GLOBAL_DAG_SYNTHETIC_MARKER0,
      ...CONCRETE_GLOBAL_DAG_FORBIDDEN_MARKERS0,
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

function resolveGlobalProofDAG0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'GlobalProofDAG0'
    ? value
    : value.GlobalProofDAG ?? value.globalProofDAG ?? null;
}

function resolveKImpl0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return (
    value.KImpl ??
    value.kimpl ??
    value.KBundle?.KImpl ??
    value.KBundle?.kimpl ??
    value.Bundle?.KImpl ??
    value.bundle?.KImpl ??
    null
  );
}

function resolveRowPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowPack0'
    ? value
    : value.RowPack ?? value.rowPack ?? null;
}

function resolveLocalPackages0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'LocalPackagePack0'
    ? value
    : value.LocalPackages ?? value.localPackages ?? value.LocalPackagePack ?? null;
}

function resolveGlobalFirewalls0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'GlobalFirewalls0'
    ? value
    : value.GlobalFirewalls ?? value.globalFirewalls ?? null;
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
