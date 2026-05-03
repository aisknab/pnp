import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedFinalIntegration0,
  makeMaterializedFinalIntegrationEnvelope0,
} from './pcc-final-integration-materialized0.mjs';

import {
  CheckConcreteMaterializedGlobalProofDAG0,
  makeConcreteMaterializedGlobalProofDAG0,
} from './pcc-global-proof-dag-concrete-materialized0.mjs';

import {
  GPACK_REQUIRED_FIELDS0,
  GPACK_ROWFAMG_REQUIRED_ROWS0,
} from './pcc-gpack0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_FINAL_INTEGRATION_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_FINAL_INTEGRATION_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteMaterializedFinalIntegrationConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedFinalIntegrationConfig0',
    version: CHECKER_VERSION,
    checkConcreteGlobalProofDAG: true,
    checkMaterializedFinalIntegration: true,
    checkConcreteLinks: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    concreteGlobalProofDAGConfig: {},
    materializedFinalIntegrationConfig: {},
    ...overrides,
  };
}

export async function makeConcreteMaterializedFinalIntegration0({
  ConcreteGlobalProofDAGEnvelope = null,
  FinalIntegrationEnvelope = null,
  overrides = {},
} = {}) {
  const concreteGlobalProofDAGEnvelope =
    ConcreteGlobalProofDAGEnvelope ?? await makeConcreteMaterializedGlobalProofDAG0();

  const finalIntegrationEnvelope =
    FinalIntegrationEnvelope ?? makeMaterializedFinalIntegrationEnvelope0();

  const concreteLinks = makeConcreteFinalIntegrationLinks0({
    concreteGlobalProofDAGEnvelope,
    finalIntegrationEnvelope,
  });

  const linkage = {
    kind: 'ConcreteMaterializedFinalIntegrationLinkage0',
    version: CHECKER_VERSION,
    concreteGlobalProofDAGDigest: digestCanonical0(concreteGlobalProofDAGEnvelope),
    materializedFinalIntegrationDigest: digestCanonical0(finalIntegrationEnvelope),
    gpackDigest: digestCanonical0(finalIntegrationEnvelope.GPack),
    rowFamGDigest: digestCanonical0(finalIntegrationEnvelope.RowFamG),
    finalIntegrationDigest: digestCanonical0(finalIntegrationEnvelope.FinalIntegration),
    finalTheoremDigest: digestCanonical0(finalIntegrationEnvelope.FinalTheorem),
    rowFamFinalDigest: digestCanonical0(finalIntegrationEnvelope.RowFamFinal),
    concreteLinksDigest: digestCanonical0(concreteLinks),
  };

  return {
    kind: 'ConcreteMaterializedFinalIntegration0',
    version: CHECKER_VERSION,

    ConcreteGlobalProofDAGEnvelope: concreteGlobalProofDAGEnvelope,
    FinalIntegrationEnvelope: finalIntegrationEnvelope,

    GPack: finalIntegrationEnvelope.GPack,
    RowFamG: finalIntegrationEnvelope.RowFamG,
    FinalIntegration: finalIntegrationEnvelope.FinalIntegration,
    FinalTheorem: finalIntegrationEnvelope.FinalTheorem,
    RowFamFinal: finalIntegrationEnvelope.RowFamFinal,

    ConcreteLinks: concreteLinks,
    Linkage: linkage,

    PiConcreteMaterializedFinalIntegration: {
      kind: 'PiConcreteMaterializedFinalIntegration0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteGlobalProofDAGEnvelope',
          digest: linkage.concreteGlobalProofDAGDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalIntegrationEnvelope',
          digest: linkage.materializedFinalIntegrationDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteFinalIntegrationLinks',
          digest: linkage.concreteLinksDigest,
        },
      ],
    },

    ...overrides,
  };
}

export function makeConcreteFinalIntegrationLinks0({
  concreteGlobalProofDAGEnvelope,
  finalIntegrationEnvelope,
}) {
  const concreteDAGNF = concreteGlobalProofDAGEnvelope?.ConcreteChain ??
    concreteGlobalProofDAGEnvelope?.ProofInventory ??
    null;

  const gpack = finalIntegrationEnvelope?.GPack ?? null;
  const rowFamG = finalIntegrationEnvelope?.RowFamG ?? null;
  const finalIntegration = finalIntegrationEnvelope?.FinalIntegration ?? null;
  const finalTheorem = finalIntegrationEnvelope?.FinalTheorem ?? null;
  const rowFamFinal = finalIntegrationEnvelope?.RowFamFinal ?? null;

  const gpackDigest = digestCanonical0(gpack);
  const finalIntegrationDigest = digestCanonical0(finalIntegration);
  const finalTheoremDigest = digestCanonical0(finalTheorem);

  return {
    kind: 'ConcreteFinalIntegrationLinks0',
    version: CHECKER_VERSION,

    concreteGlobalProofDAG: concreteGlobalProofDAGEnvelope?.kind === 'ConcreteMaterializedGlobalProofDAG0',
    concreteKBundle: concreteGlobalProofDAGEnvelope?.KBundleEnvelope?.kind === 'ConcreteMaterializedKBundle0',
    concreteRows: concreteGlobalProofDAGEnvelope?.ConcreteRowsEnvelope?.kind === 'ConcreteMaterializedRows0',
    concreteLocalPackages: concreteGlobalProofDAGEnvelope?.ConcreteLocalPackagesEnvelope?.kind === 'ConcreteMaterializedLocalPackages0',
    concreteGlobalFirewalls: concreteGlobalProofDAGEnvelope?.ConcreteGlobalFirewallsEnvelope?.kind === 'ConcreteMaterializedGlobalFirewalls0',

    kBundleKernelRuleCoverageComplete:
      concreteGlobalProofDAGEnvelope?.KBundleEnvelope?.ProofInventory?.kernelRuleCoverageComplete === true,
    kBundleSigmaProofRefsResolve:
      concreteGlobalProofDAGEnvelope?.KBundleEnvelope?.ProofInventory?.sigmaProofRefsResolve === true,
    kBundleReflectionProofRefsResolve:
      concreteGlobalProofDAGEnvelope?.KBundleEnvelope?.ProofInventory?.reflectionProofRefsResolve === true,

    gpackDigest,
    rowFamGDigest: digestCanonical0(rowFamG),
    finalIntegrationDigest,
    finalTheoremDigest,
    rowFamFinalDigest: digestCanonical0(rowFamFinal),

    gpackRequiredFields: [...GPACK_REQUIRED_FIELDS0],
    gpackFieldCoverageComplete: GPACK_REQUIRED_FIELDS0.every((field) => (
      Object.prototype.hasOwnProperty.call(gpack ?? {}, field)
    )),

    rowFamGRequiredRows: [...GPACK_ROWFAMG_REQUIRED_ROWS0],
    rowFamGCoverageComplete: GPACK_ROWFAMG_REQUIRED_ROWS0.every((rowKind) => (
      Array.isArray(rowFamG?.rows) &&
      rowFamG.rows.some((row) => row?.rowKind === rowKind)
    )),

    finalIntegrationUsesGPack: sameDigestHex0(
      digestCanonical0(finalIntegration?.GPack ?? null),
      gpackDigest,
    ),

    rowFamGUsesGPack: sameDigestHex0(
      digestCanonical0(rowFamG?.GPack ?? null),
      gpackDigest,
    ),

    finalTheoremUsesFinalIntegration: sameDigestHex0(
      digestCanonical0(finalTheorem?.FinalIntegration ?? null),
      finalIntegrationDigest,
    ),

    rowFamFinalUsesFinalTheorem: sameDigestHex0(
      digestCanonical0(rowFamFinal?.FinalTheorem ?? null),
      finalTheoremDigest,
    ),

    finalMatchUsesGPack: sameDigestHex0(
      finalIntegration?.FinalMatch?.PG?.gpackDigest ?? null,
      gpackDigest,
    ),

    satDecisionUsesGPack: sameDigestHex0(
      finalIntegration?.SATDecision?.LockedWord?.gpackDigest ?? null,
      gpackDigest,
    ),

    concreteGlobalProofDAGDigest: digestCanonical0(concreteGlobalProofDAGEnvelope),
    concreteGlobalProofDAGNF: concreteDAGNF === null ? null : digestCanonical0(concreteDAGNF),
  };
}

export async function CheckConcreteMaterializedFinalIntegration0(
  input,
  config = makeConcreteMaterializedFinalIntegrationConfig0(),
) {
  const checker = 'CheckConcreteMaterializedFinalIntegration0';
  const ledger = [];
  const cfg = makeConcreteMaterializedFinalIntegrationConfig0(config);
  const envelope = input;

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

  if (cfg.checkConcreteGlobalProofDAG === true) {
    const dagRecord = await CheckConcreteMaterializedGlobalProofDAG0(
      envelope.ConcreteGlobalProofDAGEnvelope,
      cfg.concreteGlobalProofDAGConfig ?? {},
    );
    const dag = recordToValidation0(dagRecord, ['ConcreteGlobalProofDAGEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedGlobalProofDAG0',
      status: dag.ok ? 'pass' : 'fail',
      digest: dagRecord.Digest ?? dagRecord.digest ?? digestCanonical0(dagRecord),
    });

    if (!dag.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteGlobalProofDAG`,
        path: dag.path,
        witness: dag.witness,
        ledger,
      });
    }
  }

  if (cfg.checkMaterializedFinalIntegration === true) {
    const finalRecord = await CheckMaterializedFinalIntegration0(
      envelope.FinalIntegrationEnvelope,
      cfg.materializedFinalIntegrationConfig ?? {},
    );
    const final = recordToValidation0(finalRecord, ['FinalIntegrationEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedFinalIntegration0',
      status: final.ok ? 'pass' : 'fail',
      digest: finalRecord.Digest ?? finalRecord.digest ?? digestCanonical0(finalRecord),
    });

    if (!final.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedFinalIntegration`,
        path: final.path,
        witness: final.witness,
        ledger,
      });
    }
  }

  const recomputedLinks = makeConcreteFinalIntegrationLinks0({
    concreteGlobalProofDAGEnvelope: envelope.ConcreteGlobalProofDAGEnvelope,
    finalIntegrationEnvelope: envelope.FinalIntegrationEnvelope,
  });

  if (cfg.checkConcreteLinks === true) {
    const links = validateConcreteLinks0(envelope.ConcreteLinks, recomputedLinks);

    ledger.push({
      phase: 'concreteLinks',
      status: links.ok ? 'pass' : 'fail',
      digest: digestCanonical0(links.nf ?? links.witness ?? null),
    });

    if (!links.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.concreteLinks`,
        path: links.path,
        witness: links.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

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

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteMaterializedFinalIntegration0']);

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
    const linkage = validateLinkage0(envelope, recomputedLinks);

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

  const nf = {
    kind: 'ConcreteMaterializedFinalIntegration0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    concreteGlobalProofDAG: recomputedLinks.concreteGlobalProofDAG,
    concreteKBundle: recomputedLinks.concreteKBundle,
    concreteRows: recomputedLinks.concreteRows,
    concreteLocalPackages: recomputedLinks.concreteLocalPackages,
    concreteGlobalFirewalls: recomputedLinks.concreteGlobalFirewalls,

    kBundleKernelRuleCoverageComplete: recomputedLinks.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: recomputedLinks.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: recomputedLinks.kBundleReflectionProofRefsResolve,

    gpackFieldCoverageComplete: recomputedLinks.gpackFieldCoverageComplete,
    rowFamGCoverageComplete: recomputedLinks.rowFamGCoverageComplete,
    finalIntegrationUsesGPack: recomputedLinks.finalIntegrationUsesGPack,
    rowFamGUsesGPack: recomputedLinks.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: recomputedLinks.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: recomputedLinks.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: recomputedLinks.finalMatchUsesGPack,
    satDecisionUsesGPack: recomputedLinks.satDecisionUsesGPack,

    concreteGlobalProofDAGDigest: digestCanonical0(envelope.ConcreteGlobalProofDAGEnvelope),
    materializedFinalIntegrationDigest: digestCanonical0(envelope.FinalIntegrationEnvelope),
    gpackDigest: recomputedLinks.gpackDigest,
    rowFamGDigest: recomputedLinks.rowFamGDigest,
    finalIntegrationDigest: recomputedLinks.finalIntegrationDigest,
    finalTheoremDigest: recomputedLinks.finalTheoremDigest,
    rowFamFinalDigest: recomputedLinks.rowFamFinalDigest,
    concreteLinksDigest: digestCanonical0(recomputedLinks),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

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

export async function writeConcreteMaterializedFinalIntegrationFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedFinalIntegrationFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedFinalIntegration0(options);
  const checked = await CheckConcreteMaterializedFinalIntegration0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedFinalIntegration0.json');
  const finalIntegrationEnvelopePath = path.join(outDir, 'MaterializedFinalIntegration0.json');
  const concreteGlobalProofDAGPath = path.join(outDir, 'ConcreteMaterializedGlobalProofDAG0.json');
  const gpackPath = path.join(outDir, 'GPack0.json');
  const finalTheoremPath = path.join(outDir, 'FinalTheorem0.json');
  const linksPath = path.join(outDir, 'ConcreteFinalIntegrationLinks0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedFinalIntegration0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(finalIntegrationEnvelopePath, envelope.FinalIntegrationEnvelope);
  await writeJsonFile0(concreteGlobalProofDAGPath, envelope.ConcreteGlobalProofDAGEnvelope);
  await writeJsonFile0(gpackPath, envelope.GPack);
  await writeJsonFile0(finalTheoremPath, envelope.FinalTheorem);
  await writeJsonFile0(linksPath, envelope.ConcreteLinks);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      finalIntegrationEnvelopePath,
      concreteGlobalProofDAGPath,
      gpackPath,
      finalTheoremPath,
      linksPath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedFinalIntegrationConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedFinalIntegrationConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedFinalIntegrationConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedFinalIntegrationConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteGlobalProofDAG',
    'checkMaterializedFinalIntegration',
    'checkConcreteLinks',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedFinalIntegrationConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concreteGlobalProofDAGConfig)) {
    return validationReject0(['concreteGlobalProofDAGConfig'], 'concreteGlobalProofDAGConfig must be an object', {
      actual: typeof config.concreteGlobalProofDAGConfig,
    });
  }

  if (!isPlainObject(config.materializedFinalIntegrationConfig)) {
    return validationReject0(['materializedFinalIntegrationConfig'], 'materializedFinalIntegrationConfig must be an object', {
      actual: typeof config.materializedFinalIntegrationConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedFinalIntegrationConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedFinalIntegration0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedFinalIntegration0') {
    return validationReject0(['kind'], 'ConcreteMaterializedFinalIntegration0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  for (const field of [
    'ConcreteGlobalProofDAGEnvelope',
    'FinalIntegrationEnvelope',
    'GPack',
    'RowFamG',
    'FinalIntegration',
    'FinalTheorem',
    'RowFamFinal',
    'ConcreteLinks',
  ]) {
    if (!isPlainObject(envelope[field])) {
      return validationReject0([field], `ConcreteMaterializedFinalIntegration0 must include ${field}`, {
        actual: typeof envelope[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedFinalIntegrationShape0NF',
  });
}

function validateConcreteLinks0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['ConcreteLinks'], 'ConcreteFinalIntegrationLinks0 must match recomputed concrete links', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  for (const field of [
    'concreteGlobalProofDAG',
    'concreteKBundle',
    'concreteRows',
    'concreteLocalPackages',
    'concreteGlobalFirewalls',
    'kBundleKernelRuleCoverageComplete',
    'kBundleSigmaProofRefsResolve',
    'kBundleReflectionProofRefsResolve',
    'gpackFieldCoverageComplete',
    'rowFamGCoverageComplete',
    'finalIntegrationUsesGPack',
    'rowFamGUsesGPack',
    'finalTheoremUsesFinalIntegration',
    'rowFamFinalUsesFinalTheorem',
    'finalMatchUsesGPack',
    'satDecisionUsesGPack',
  ]) {
    if (expected[field] !== true) {
      return validationReject0(['ConcreteLinks', field], `ConcreteFinalIntegrationLinks0 must certify ${field}`, {
        actual: expected[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteFinalIntegrationLinks0NF',
    concreteLinksDigest: digestCanonical0(expected),
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteMaterializedFinalIntegration0'], 'ConcreteMaterializedFinalIntegration0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteMaterializedFinalIntegration0'], 'ConcreteMaterializedFinalIntegration0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedFinalIntegrationJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, concreteLinks) {
  const expected = {
    concreteGlobalProofDAGDigest: digestCanonical0(envelope.ConcreteGlobalProofDAGEnvelope),
    materializedFinalIntegrationDigest: digestCanonical0(envelope.FinalIntegrationEnvelope),
    gpackDigest: digestCanonical0(envelope.GPack),
    rowFamGDigest: digestCanonical0(envelope.RowFamG),
    finalIntegrationDigest: digestCanonical0(envelope.FinalIntegration),
    finalTheoremDigest: digestCanonical0(envelope.FinalTheorem),
    rowFamFinalDigest: digestCanonical0(envelope.RowFamFinal),
    concreteLinksDigest: digestCanonical0(concreteLinks),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteMaterializedFinalIntegrationLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedFinalIntegration0 Linkage must be an object when present', {
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
    kind: 'ConcreteMaterializedFinalIntegrationLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteMaterializedFinalIntegrationFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_FINAL_INTEGRATION_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_FINAL_INTEGRATION_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_FINAL_INTEGRATION_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized final integration contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedFinalIntegrationNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function scanFixtureMarkers0(value, pathNow, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      CONCRETE_FINAL_INTEGRATION_SYNTHETIC_MARKER0,
      ...CONCRETE_FINAL_INTEGRATION_FORBIDDEN_MARKERS0,
    ]) {
      if (lower.includes(marker)) {
        hits.push({
          path: pathNow,
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
      scanFixtureMarkers0(value[index], [...pathNow, index], hits);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    scanFixtureMarkers0(value[key], [...pathNow, key], hits);
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
