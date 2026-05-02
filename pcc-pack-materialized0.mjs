import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckPackSufficiency0,
  PCCPACK_REQUIRED_FIELDS0,
  PACK_SUFFICIENCY_PHASES0,
  makeSyntheticPackSufficiencyTheorem0,
} from './pcc-pack-sufficiency0.mjs';

import {
  CheckMaterializedBoot0,
  makeMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

import {
  CheckMaterializedKBundle0,
  makeMaterializedKBundle0,
} from './pcc-k-materialized0.mjs';

import {
  CheckMaterializedHard0,
  makeMaterializedHard0,
} from './pcc-hard-materialized0.mjs';

import {
  CheckMaterializedRows0,
  makeMaterializedRows0,
} from './pcc-rows-materialized0.mjs';

import {
  CheckConcreteMaterializedRows0,
  makeConcreteMaterializedRows0,
} from './pcc-rows-concrete-materialized0.mjs';

import {
  CheckMaterializedGlobalProofDAG0,
  makeMaterializedGlobalProofDAG0,
} from './pcc-global-proof-dag-materialized0.mjs';

import {
  CheckMaterializedLocalPackages0,
  makeMaterializedLocalPackages0,
} from './pcc-local-packages-materialized0.mjs';

import {
  CheckConcreteMaterializedLocalPackages0,
  makeConcreteMaterializedLocalPackages0,
} from './pcc-local-packages-concrete-materialized0.mjs';

import {
  CheckMaterializedGlobalFirewalls0,
  makeMaterializedGlobalFirewalls0,
} from './pcc-global-firewalls-materialized0.mjs';

import {
  CheckMaterializedFinalIntegration0,
  makeMaterializedFinalIntegrationEnvelope0,
} from './pcc-final-integration-materialized0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_PACK_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const MATERIALIZED_PACK_SYNTHETIC_MARKER0 = 'synthetic';

export function makeMaterializedPCCPackConfig0(overrides = {}) {
  return {
    kind: 'MaterializedPCCPackConfig0',
    version: CHECKER_VERSION,
    checkMaterializedComponents: true,
    checkPackSufficiency: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    ...overrides,
  };
}

export async function makeMaterializedPCCPack0({
  Boot0 = null,
  KBundleEnvelope = null,
  HardEnvelope = null,
  RowsEnvelope = null,
  GlobalProofDAGEnvelope = null,
  LocalPackagesEnvelope = null,
  GlobalFirewallsEnvelope = null,
  FinalIntegrationEnvelope = null,
  PCCPack = null,
  overrides = {},
} = {}) {
  const boot0 = resolveBoot0(Boot0) ?? await makeMaterializedBoot0();

  const kBundleEnvelope = KBundleEnvelope ?? await makeMaterializedKBundle0({
    Boot0: boot0,
  });
  const kBundle = resolveKBundle0(kBundleEnvelope);

  const hardEnvelope = HardEnvelope ?? makeMaterializedHard0();
  const hardCheck = resolveHardCheck0(hardEnvelope);

  const rowsEnvelope = RowsEnvelope ?? await makeConcreteMaterializedRows0({
    Boot0: boot0,
  });
  const rowPack = resolveRowPack0(rowsEnvelope);

  const globalProofDAGEnvelope = GlobalProofDAGEnvelope ?? await makeMaterializedGlobalProofDAG0({
    Boot0: boot0,
    KBundle: kBundleEnvelope,
  });
  const globalProofDAG = resolveGlobalProofDAG0(globalProofDAGEnvelope);

  const localPackagesEnvelope = LocalPackagesEnvelope ?? await makeConcreteMaterializedLocalPackages0({
    ConcreteRowsEnvelope: rowsEnvelope,
  });
  const localPackages = resolveLocalPackages0(localPackagesEnvelope);

  const globalFirewallsEnvelope = GlobalFirewallsEnvelope ?? makeMaterializedGlobalFirewalls0({
    LocalPackagesEnvelope: localPackagesEnvelope,
  });
  const globalFirewalls = resolveGlobalFirewalls0(globalFirewallsEnvelope);

  const finalIntegrationEnvelope = FinalIntegrationEnvelope ?? makeMaterializedFinalIntegrationEnvelope0();
  const gpack = resolveGPack0(finalIntegrationEnvelope);
  const rowFamG = resolveRowFamG0(finalIntegrationEnvelope);
  const finalIntegration = resolveFinalIntegration0(finalIntegrationEnvelope);
  const finalTheorem = resolveFinalTheorem0(finalIntegrationEnvelope);
  const rowFamFinal = resolveRowFamFinal0(finalIntegrationEnvelope);

  const pccPack = PCCPack ?? makePCCPack0({
    Boot0: boot0,
    KBundle: kBundle,
    HardCheck: hardCheck,
    RowPack: rowPack,
    GlobalProofDAG: globalProofDAG,
    LocalPackages: localPackages,
    GlobalFirewalls: globalFirewalls,
    GPack: gpack,
    RowFamG: rowFamG,
    FinalIntegration: finalIntegration,
    FinalTheorem: finalTheorem,
    RowFamFinal: rowFamFinal,
  });

  const linkage = {
    kind: 'MaterializedPCCPackLinkage0',
    version: CHECKER_VERSION,
    pccPackDigest: digestCanonical0(pccPack),
    bootDigest: digestCanonical0(boot0),
    kBundleDigest: digestCanonical0(kBundle),
    hardCheckDigest: digestCanonical0(hardCheck),
    rowPackDigest: digestCanonical0(rowPack),
    globalProofDAGDigest: digestCanonical0(globalProofDAG),
    localPackagesDigest: digestCanonical0(localPackages),
    globalFirewallsDigest: digestCanonical0(globalFirewalls),
    gpackDigest: digestCanonical0(gpack),
    rowFamGDigest: digestCanonical0(rowFamG),
    finalIntegrationDigest: digestCanonical0(finalIntegration),
    finalTheoremDigest: digestCanonical0(finalTheorem),
    rowFamFinalDigest: digestCanonical0(rowFamFinal),
    phaseOrder: [...PACK_SUFFICIENCY_PHASES0],
    requiredArtefacts: [...PCCPACK_REQUIRED_FIELDS0],
  };

  return {
    kind: 'MaterializedPCCPack0',
    version: CHECKER_VERSION,
    MaterializedBoot0: boot0,
    KBundleEnvelope: kBundleEnvelope,
    HardEnvelope: hardEnvelope,
    RowsEnvelope: rowsEnvelope,
    GlobalProofDAGEnvelope: globalProofDAGEnvelope,
    LocalPackagesEnvelope: localPackagesEnvelope,
    GlobalFirewallsEnvelope: globalFirewallsEnvelope,
    FinalIntegrationEnvelope: finalIntegrationEnvelope,
    PCCPack: pccPack,
    Linkage: linkage,
    PiMaterializedPCCPack: {
      kind: 'PiMaterializedPCCPack0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'PCCPack',
          digest: linkage.pccPackDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'PackSufficiencyTheorem',
          digest: digestCanonical0(pccPack.PackSufficiencyTheorem),
        },
      ],
    },
    ...overrides,
  };
}

export function makePCCPack0({
  Boot0,
  KBundle,
  HardCheck,
  RowPack,
  GlobalProofDAG,
  LocalPackages,
  GlobalFirewalls,
  GPack,
  RowFamG,
  FinalIntegration,
  FinalTheorem,
  RowFamFinal,
  overrides = {},
} = {}) {
  const artefacts = {
    Boot0,
    KBundle,
    HardCheck,
    RowPack,
    GlobalProofDAG,
    LocalPackages,
    GlobalFirewalls,
    GPack,
    RowFamG,
    FinalIntegration,
    FinalTheorem,
    RowFamFinal,
  };

  const artefactDigests = Object.fromEntries(
    Object.entries(artefacts).map(([name, value]) => [
      name,
      digestCanonical0(value),
    ]),
  );

  const coreMaterial = {
    kind: 'PCCCorePackage0MaterialDigestMap0',
    version: CHECKER_VERSION,
    generatedBy: 'GeneratePCCPack',
    excludesAcceptRun: true,
    artefactDigests,
  };

  const Core = {
    kind: 'PCCCorePackage0',
    version: CHECKER_VERSION,
    generatedBy: 'GeneratePCCPack',
    excludesAcceptRun: true,
    includesAcceptRun: false,
    generatorUntrusted: true,
    materializedOutputOnly: true,
    canonicalByteEquality: true,
    noDigestOnlyEquality: true,
    artefactDigests,
    canonicalBytes: {
      alg: 'canonical-json-v0',
      digest: digestCanonical0(coreMaterial),
    },
  };

  const Manifest = {
    kind: 'PCCPackManifest0',
    version: CHECKER_VERSION,
    phaseOrder: [...PACK_SUFFICIENCY_PHASES0],
    requiredArtefacts: [...PCCPACK_REQUIRED_FIELDS0],
    checker: 'CheckPCCPackexp',
    finalVerdictExcluded: true,
    acceptRunExcluded: true,
    publicConclusionOnlyAfterAcceptRun: true,
  };

  const PackSufficiencyTheorem = makeSyntheticPackSufficiencyTheorem0({
    PiPackSufficiency: {
      kind: 'PiPackSufficiency0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-pack-sufficiency',
      note: 'materialized pack sufficiency proof references',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'Core',
          digest: digestCanonical0(Core),
        },
        {
          kind: 'MaterializedRef0',
          target: 'Manifest',
          digest: digestCanonical0(Manifest),
        },
      ],
    },
  });

  return {
    kind: 'PCCPack0',
    version: CHECKER_VERSION,
    Core,
    Manifest,
    Boot0,
    KBundle,
    HardCheck,
    RowPack,
    GlobalProofDAG,
    LocalPackages,
    GlobalFirewalls,
    GPack,
    RowFamG,
    FinalIntegration,
    FinalTheorem,
    RowFamFinal,
    PackSufficiencyTheorem,
    PiPackSufficiency: {
      kind: 'PiPackSufficiencyRun0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-pcc-pack',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'PackSufficiencyTheorem',
          digest: digestCanonical0(PackSufficiencyTheorem),
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckMaterializedPCCPack0(input, config = makeMaterializedPCCPackConfig0()) {
  const checker = 'CheckMaterializedPCCPack0';
  const ledger = [];
  const cfg = makeMaterializedPCCPackConfig0(config);
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

  if (cfg.checkMaterializedComponents === true) {
    const componentResult = await validateMaterializedComponents0(envelope);

    ledger.push({
      phase: 'materializedComponents',
      status: componentResult.ok ? 'pass' : 'fail',
      digest: digestCanonical0(componentResult.nf ?? componentResult.witness ?? null),
    });

    if (!componentResult.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.components`,
        path: componentResult.path,
        witness: componentResult.witness,
        ledger,
      });
    }
  }

  if (cfg.checkPackSufficiency === true) {
    const packRecord = await CheckPackSufficiency0(envelope.PCCPack);
    const pack = recordToValidation0(packRecord, ['PCCPack']);

    ledger.push({
      phase: 'CheckPackSufficiency0',
      status: pack.ok ? 'pass' : 'fail',
      digest: packRecord.Digest ?? packRecord.digest ?? digestCanonical0(packRecord),
    });

    if (!pack.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPackSufficiency0`,
        path: pack.path,
        witness: pack.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope.PCCPack);

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

  const markerInventory = collectFixtureMarkers0(envelope.PCCPack, ['PCCPack']);

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

  const packRecord = await CheckPackSufficiency0(envelope.PCCPack);
  const packNF = packRecord.NF ?? packRecord.nf ?? {};

  const nf = {
    kind: 'MaterializedPCCPack0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    checkPCCPackChecker: 'CheckPCCPackexp',
    pccPackDigest: packRecord.Digest ?? packRecord.digest,
    pccPackObjectDigest: digestCanonical0(envelope.PCCPack),
    coreDigest: digestCanonical0(envelope.PCCPack.Core),
    manifestDigest: digestCanonical0(envelope.PCCPack.Manifest),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    phaseOrder: packNF.phaseOrder ?? PACK_SUFFICIENCY_PHASES0,
    theoremIds: packNF.theoremIds ?? [],
    publicConclusion: packNF.publicConclusion ?? null,
    generatedPackageAssumption: packNF.generatedPackageAssumption ?? null,
    rowsEnvelopeKind: envelope.RowsEnvelope?.kind ?? null,
    concreteRows: isPlainObject(envelope.RowsEnvelope) && envelope.RowsEnvelope.kind === 'ConcreteMaterializedRows0',
    localPackagesEnvelopeKind: envelope.LocalPackagesEnvelope?.kind ?? null,
    concreteLocalPackages: isPlainObject(envelope.LocalPackagesEnvelope) && envelope.LocalPackagesEnvelope.kind === 'ConcreteMaterializedLocalPackages0',
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

export async function writeMaterializedPCCPackFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedPCCPackFiles0 requires a non-empty output directory');
  }

  const envelope = await makeMaterializedPCCPack0(options);
  const checked = await CheckMaterializedPCCPack0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedPCCPack0.json');
  const pccPackPath = path.join(outDir, 'PCCPack0.json');
  const corePath = path.join(outDir, 'PCCCorePackage0.json');
  const manifestPath = path.join(outDir, 'PCCPackManifest0.json');
  const theoremPath = path.join(outDir, 'PackSufficiencyTheorem0.json');
  const checkPath = path.join(outDir, 'MaterializedPCCPack0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(pccPackPath, envelope.PCCPack);
  await writeJsonFile0(corePath, envelope.PCCPack.Core);
  await writeJsonFile0(manifestPath, envelope.PCCPack.Manifest);
  await writeJsonFile0(theoremPath, envelope.PCCPack.PackSufficiencyTheorem);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      pccPackPath,
      corePath,
      manifestPath,
      theoremPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'PCCPack0') {
    return {
      kind: 'MaterializedPCCPack0',
      version: CHECKER_VERSION,
      MaterializedBoot0: input.Boot0,
      KBundleEnvelope: input.KBundle,
      HardEnvelope: {
        HardCheck: input.HardCheck,
      },
      RowsEnvelope: {
        RowPack: input.RowPack,
      },
      GlobalProofDAGEnvelope: {
        GlobalProofDAG: input.GlobalProofDAG,
      },
      LocalPackagesEnvelope: {
        LocalPackages: input.LocalPackages,
        RowPack: input.RowPack,
      },
      GlobalFirewallsEnvelope: {
        GlobalFirewalls: input.GlobalFirewalls,
        LocalPackagesEnvelope: {
          LocalPackages: input.LocalPackages,
          RowPack: input.RowPack,
        },
      },
      FinalIntegrationEnvelope: {
        GPack: input.GPack,
        RowFamG: input.RowFamG,
        FinalIntegration: input.FinalIntegration,
        FinalTheorem: input.FinalTheorem,
        RowFamFinal: input.RowFamFinal,
      },
      PCCPack: input,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedPCCPackConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedPCCPackConfig0') {
    return validationReject0(['kind'], 'MaterializedPCCPackConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedPCCPackConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkMaterializedComponents',
    'checkPackSufficiency',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedPCCPackConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedPCCPack0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedPCCPack0') {
    return validationReject0(['kind'], 'MaterializedPCCPack0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedPCCPack0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.PCCPack)) {
    return validationReject0(['PCCPack'], 'MaterializedPCCPack0 must include a PCCPack object', {
      actual: typeof envelope.PCCPack,
    });
  }

  if (envelope.PCCPack.kind !== 'PCCPack0') {
    return validationReject0(['PCCPack', 'kind'], 'PCCPack kind must be PCCPack0', {
      actual: envelope.PCCPack.kind,
    });
  }

  for (const field of PCCPACK_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(envelope.PCCPack, field)) {
      return validationReject0(['PCCPack', field], 'PCCPack is missing a required artefact', {
        field,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackShape0NF',
  });
}

async function checkMaterializedLocalPackagesEnvelope0(value) {
  if (isPlainObject(value) && value.kind === 'ConcreteMaterializedLocalPackages0') {
    return CheckConcreteMaterializedLocalPackages0(value);
  }

  return CheckMaterializedLocalPackages0(value);
}

async function checkMaterializedRowsEnvelope0(value) {
  if (isPlainObject(value) && value.kind === 'ConcreteMaterializedRows0') {
    return CheckConcreteMaterializedRows0(value);
  }

  return CheckMaterializedRows0(value);
}

async function validateMaterializedComponents0(envelope) {
  const componentChecks = [
    ['MaterializedBoot0', await CheckMaterializedBoot0(resolveBoot0(envelope.MaterializedBoot0) ?? envelope.PCCPack.Boot0)],
    ['KBundleEnvelope', await CheckMaterializedKBundle0(envelope.KBundleEnvelope)],
    ['HardEnvelope', await CheckMaterializedHard0(envelope.HardEnvelope)],
    ['RowsEnvelope', await checkMaterializedRowsEnvelope0(envelope.RowsEnvelope)],
    ['GlobalProofDAGEnvelope', await CheckMaterializedGlobalProofDAG0(envelope.GlobalProofDAGEnvelope)],
    ['LocalPackagesEnvelope', await checkMaterializedLocalPackagesEnvelope0(envelope.LocalPackagesEnvelope)],
    ['GlobalFirewallsEnvelope', await CheckMaterializedGlobalFirewalls0(envelope.GlobalFirewallsEnvelope)],
    ['FinalIntegrationEnvelope', await CheckMaterializedFinalIntegration0(envelope.FinalIntegrationEnvelope)],
  ];

  const componentDigests = [];

  for (const [pathName, record] of componentChecks) {
    if (isRejectRecord0(record)) {
      return validationReject0([pathName], `${record.checker} rejected`, {
        inner: compactReject0(record),
      });
    }

    componentDigests.push({
      pathName,
      checker: record.checker,
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackComponents0NF',
    componentDigests,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['PCCPack'], 'PCCPack must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['PCCPack'], 'PCCPack canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackJson0NF',
    byteLength: bytes.length,
    pccPackDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'MaterializedPCCPackFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === MATERIALIZED_PACK_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== MATERIALIZED_PACK_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== MATERIALIZED_PACK_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'materialized PCCPack contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  const pack = envelope.PCCPack;

  const expected = {
    pccPackDigest: digestCanonical0(pack),
    bootDigest: digestCanonical0(pack.Boot0),
    kBundleDigest: digestCanonical0(pack.KBundle),
    hardCheckDigest: digestCanonical0(pack.HardCheck),
    rowPackDigest: digestCanonical0(pack.RowPack),
    globalProofDAGDigest: digestCanonical0(pack.GlobalProofDAG),
    localPackagesDigest: digestCanonical0(pack.LocalPackages),
    globalFirewallsDigest: digestCanonical0(pack.GlobalFirewalls),
    gpackDigest: digestCanonical0(pack.GPack),
    rowFamGDigest: digestCanonical0(pack.RowFamG),
    finalIntegrationDigest: digestCanonical0(pack.FinalIntegration),
    finalTheoremDigest: digestCanonical0(pack.FinalTheorem),
    rowFamFinalDigest: digestCanonical0(pack.RowFamFinal),
  };

  const resolved = {
    bootDigest: digestCanonical0(resolveBoot0(envelope.MaterializedBoot0) ?? null),
    kBundleDigest: digestCanonical0(resolveKBundle0(envelope.KBundleEnvelope) ?? null),
    hardCheckDigest: digestCanonical0(resolveHardCheck0(envelope.HardEnvelope) ?? null),
    rowPackDigest: digestCanonical0(resolveRowPack0(envelope.RowsEnvelope) ?? null),
    globalProofDAGDigest: digestCanonical0(resolveGlobalProofDAG0(envelope.GlobalProofDAGEnvelope) ?? null),
    localPackagesDigest: digestCanonical0(resolveLocalPackages0(envelope.LocalPackagesEnvelope) ?? null),
    globalFirewallsDigest: digestCanonical0(resolveGlobalFirewalls0(envelope.GlobalFirewallsEnvelope) ?? null),
    gpackDigest: digestCanonical0(resolveGPack0(envelope.FinalIntegrationEnvelope) ?? null),
    rowFamGDigest: digestCanonical0(resolveRowFamG0(envelope.FinalIntegrationEnvelope) ?? null),
    finalIntegrationDigest: digestCanonical0(resolveFinalIntegration0(envelope.FinalIntegrationEnvelope) ?? null),
    finalTheoremDigest: digestCanonical0(resolveFinalTheorem0(envelope.FinalIntegrationEnvelope) ?? null),
    rowFamFinalDigest: digestCanonical0(resolveRowFamFinal0(envelope.FinalIntegrationEnvelope) ?? null),
  };

  for (const [field, expectedDigest] of Object.entries(resolved)) {
    if (!sameDigestHex0(expected[field], expectedDigest)) {
      return validationReject0(['PCCPack', field.replace(/Digest$/, '')], `PCCPack ${field} does not match materialized component envelope`, {
        expected: expectedDigest,
        actual: expected[field],
      });
    }
  }

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedPCCPackLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedPCCPack0 Linkage must be an object when present', {
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

  if (!Array.isArray(envelope.Linkage.phaseOrder)) {
    return validationReject0(['Linkage', 'phaseOrder'], 'Linkage phaseOrder must be an array', {
      actual: typeof envelope.Linkage.phaseOrder,
    });
  }

  for (let index = 0; index < PACK_SUFFICIENCY_PHASES0.length; index += 1) {
    if (envelope.Linkage.phaseOrder[index] !== PACK_SUFFICIENCY_PHASES0[index]) {
      return validationReject0(['Linkage', 'phaseOrder', index], 'Linkage phaseOrder mismatch', {
        expected: PACK_SUFFICIENCY_PHASES0[index],
        actual: envelope.Linkage.phaseOrder[index],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackLinkage0NF',
    present: true,
    ...expected,
  });
}

function scanFixtureMarkers0(value, path, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      MATERIALIZED_PACK_SYNTHETIC_MARKER0,
      ...MATERIALIZED_PACK_FORBIDDEN_MARKERS0,
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

function resolveBoot0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'Boot0'
    ? value
    : value.Boot0 ?? value.boot0 ?? value.MaterializedBoot0 ?? null;
}

function resolveKBundle0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  if (
    value.KImpl !== undefined ||
    value.K0 !== undefined ||
    value.PSigma !== undefined ||
    value.SigmaRegistry !== undefined ||
    value.ReflectionRegistry !== undefined
  ) {
    return value;
  }

  return value.KBundle ?? value.kBundle ?? value.bundle ?? null;
}

function resolveHardCheck0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'HardCheck0'
    ? value
    : value.HardCheck ?? value.hardCheck ?? null;
}

function resolveRowPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowPack0'
    ? value
    : value.RowPack ?? value.rowPack ?? null;
}

function resolveGlobalProofDAG0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'GlobalProofDAG0'
    ? value
    : value.GlobalProofDAG ?? value.globalProofDAG ?? null;
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

function resolveGPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'GPack0'
    ? value
    : value.GPack ?? value.gpack ?? null;
}

function resolveRowFamG0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowFamG0'
    ? value
    : value.RowFamG ?? value.rowFamG ?? null;
}

function resolveFinalIntegration0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'FinalIntegration0'
    ? value
    : value.FinalIntegration ?? value.finalIntegration ?? null;
}

function resolveFinalTheorem0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'FinalTheorem0'
    ? value
    : value.FinalTheorem ?? value.finalTheorem ?? null;
}

function resolveRowFamFinal0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowFamFinal0'
    ? value
    : value.RowFamFinal ?? value.rowFamFinal ?? null;
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
