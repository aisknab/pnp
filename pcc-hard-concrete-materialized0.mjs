import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckHard0,
  HARD_ALLOWED_PROOF_REF_KINDS0,
  HARD_CHECKER_FIELDS0,
  HARD_CHECKER_IDS0,
  HARD_FORBIDDEN_IMPORT_EDGES0,
  HARD_FORBIDDEN_SYMBOLS0,
  HARD_NO_MIN_EXPANSION_STAGES0,
  HARD_OCCURRENCE_CLASSES0,
  HARD_ROUTE_PRIORITY0,
  HARD_ROWKEY_FIELDS0,
} from './pcc-hard0.mjs';

import {
  CheckMaterializedHard0,
  makeMaterializedHard0,
} from './pcc-hard-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_HARD_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_HARD_SYNTHETIC_MARKER0 = 'synthetic';

const REQUIRED_DESCRIPTOR_FLAGS0 = Object.freeze([
  'total',
  'deterministic',
  'canonical',
  'hashIndependent',
  'modeSafe',
  'polynomial',
  'noUnknown',
]);

export function makeConcreteMaterializedHardConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedHardConfig0',
    version: CHECKER_VERSION,
    checkMaterializedHard: true,
    checkHard: true,
    checkCoverage: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    materializedHardConfig: {},
    ...overrides,
  };
}

export function makeConcreteMaterializedHard0({
  MaterializedHardEnvelope = null,
  HardCheck = null,
  overrides = {},
} = {}) {
  const materializedHardEnvelope = MaterializedHardEnvelope ?? makeMaterializedHard0(
    HardCheck === null ? {} : { HardCheck },
  );

  const hardCheck = resolveHardCheck0(materializedHardEnvelope);
  const coverage = makeConcreteHardCoverage0(materializedHardEnvelope);

  const linkage = {
    kind: 'ConcreteMaterializedHardLinkage0',
    version: CHECKER_VERSION,
    materializedHardDigest: digestCanonical0(materializedHardEnvelope),
    hardCheckDigest: digestCanonical0(hardCheck),
    coverageDigest: digestCanonical0(coverage),
    checkerCount: coverage.checkerCount,
    rowKeyFieldCount: coverage.rowKeyFieldCount,
    forbiddenSymbolCount: coverage.forbiddenSymbolCount,
    forbiddenImportEdgeCount: coverage.forbiddenImportEdgeCount,
  };

  return {
    kind: 'ConcreteMaterializedHardCheck0',
    version: CHECKER_VERSION,
    MaterializedHardEnvelope: materializedHardEnvelope,
    HardCheck: hardCheck,
    Coverage: coverage,
    Linkage: linkage,
    PiConcreteMaterializedHardCheck: {
      kind: 'PiConcreteMaterializedHardCheck0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'MaterializedHardEnvelope',
          digest: linkage.materializedHardDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteHardCoverage',
          digest: linkage.coverageDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeConcreteHardCoverage0(materializedHardEnvelope) {
  const hard = resolveHardCheck0(materializedHardEnvelope);
  const checkerEntries = [];
  const missingCheckerFields = [];
  const wrongCheckerIds = [];
  const descriptorFlagFailures = [];
  const unknownOutputFailures = [];
  const returnShapeFailures = [];

  for (const field of HARD_CHECKER_FIELDS0) {
    const descriptor = hard?.[field] ?? null;
    const expectedCheckerId = HARD_CHECKER_IDS0[field] ?? null;

    if (!isPlainObject(descriptor)) {
      missingCheckerFields.push(field);
      checkerEntries.push({
        field,
        expectedCheckerId,
        checkerId: null,
        descriptorDigest: null,
      });
      continue;
    }

    if (descriptor.checkerId !== expectedCheckerId) {
      wrongCheckerIds.push({
        field,
        expectedCheckerId,
        actualCheckerId: descriptor.checkerId ?? null,
      });
    }

    for (const flag of REQUIRED_DESCRIPTOR_FLAGS0) {
      if (descriptor[flag] !== true) {
        descriptorFlagFailures.push({
          field,
          flag,
          actual: descriptor[flag] ?? null,
        });
      }
    }

    if (
      descriptor.unknownOutput === true ||
      descriptor.unknownOutputs === true ||
      Object.prototype.hasOwnProperty.call(descriptor.returns ?? {}, 'unknown')
    ) {
      unknownOutputFailures.push(field);
    }

    if (!arrayContainsAll0(descriptor.returns?.accept, ['NF', 'Digest', 'Ledger'])) {
      returnShapeFailures.push({
        field,
        side: 'accept',
      });
    }

    if (!arrayContainsAll0(descriptor.returns?.reject, ['Coord', 'Path', 'Witness', 'Digest'])) {
      returnShapeFailures.push({
        field,
        side: 'reject',
      });
    }

    checkerEntries.push({
      field,
      expectedCheckerId,
      checkerId: descriptor.checkerId ?? null,
      descriptorDigest: digestCanonical0(descriptor),
    });
  }

  const rowKeyFields = hard?.RowKeyCheck?.rowKeyFields ?? [];
  const routePriority = hard?.RouteCheck?.priority ?? [];
  const proofRefKinds = hard?.ProofRefCheck?.allowedRefKinds ?? [];
  const noMinStages = hard?.NoMinCheck?.expansionStages ?? [];
  const occurrenceClasses = hard?.NoMinCheck?.occurrenceClasses ?? [];
  const forbiddenSymbols = hard?.NoMinCheck?.forbiddenSymbols ?? [];
  const forbiddenImportEdges = hard?.ImportCheck?.forbiddenEdges ?? [];

  const forbiddenImportEdgeKeys = new Set(
    Array.isArray(forbiddenImportEdges)
      ? forbiddenImportEdges.map((edge) => edgeKey0(edge))
      : [],
  );

  const expectedForbiddenImportEdgeKeys = HARD_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge));

  return {
    kind: 'ConcreteHardCoverage0',
    version: CHECKER_VERSION,

    checkerCount: checkerEntries.length,
    expectedCheckerFields: [...HARD_CHECKER_FIELDS0],
    checkerEntries,
    missingCheckerFields,
    wrongCheckerIds,
    descriptorFlagFailures,
    unknownOutputFailures,
    returnShapeFailures,
    checkerCoverageComplete:
      missingCheckerFields.length === 0 &&
      wrongCheckerIds.length === 0 &&
      descriptorFlagFailures.length === 0 &&
      unknownOutputFailures.length === 0 &&
      returnShapeFailures.length === 0,

    rowKeyFieldCount: Array.isArray(rowKeyFields) ? rowKeyFields.length : null,
    rowKeyFields,
    expectedRowKeyFields: [...HARD_ROWKEY_FIELDS0],
    rowKeyCoverageComplete: sameArray0(rowKeyFields, HARD_ROWKEY_FIELDS0),

    routePriority,
    expectedRoutePriority: [...HARD_ROUTE_PRIORITY0],
    routePriorityComplete: sameArray0(routePriority, HARD_ROUTE_PRIORITY0),

    proofRefKinds,
    expectedProofRefKinds: [...HARD_ALLOWED_PROOF_REF_KINDS0],
    proofRefPolicyComplete: arrayContainsAll0(proofRefKinds, HARD_ALLOWED_PROOF_REF_KINDS0),

    hashDisciplineComplete:
      hard?.HashCheck?.hashAsIndexOnly === true &&
      (
        hard?.HashCheck?.fullKeyCompareAfterHash === true ||
        hard?.HashCheck?.canonicalByteCompareAfterHash === true
      ) &&
      hard?.HashCheck?.digestEqualityIsNotObjectEquality === true,

    noMinStages,
    expectedNoMinStages: [...HARD_NO_MIN_EXPANSION_STAGES0],
    noMinStageCoverageComplete: arrayContainsAll0(noMinStages, HARD_NO_MIN_EXPANSION_STAGES0),

    occurrenceClasses,
    expectedOccurrenceClasses: [...HARD_OCCURRENCE_CLASSES0],
    noMinOccurrenceCoverageComplete: arrayContainsAll0(occurrenceClasses, HARD_OCCURRENCE_CLASSES0),

    forbiddenSymbolCount: Array.isArray(forbiddenSymbols) ? forbiddenSymbols.length : null,
    forbiddenSymbols,
    expectedForbiddenSymbols: [...HARD_FORBIDDEN_SYMBOLS0],
    noMinForbiddenSymbolCoverageComplete: arrayContainsAll0(forbiddenSymbols, HARD_FORBIDDEN_SYMBOLS0),
    noMinAliasCoverageComplete: hard?.NoMinCheck?.rejectsAliases === true,
    noMinExecutableOnly: hard?.NoMinCheck?.rejectsExecutableOnly === true,
    noMinCoverageComplete:
      arrayContainsAll0(noMinStages, HARD_NO_MIN_EXPANSION_STAGES0) &&
      arrayContainsAll0(occurrenceClasses, HARD_OCCURRENCE_CLASSES0) &&
      arrayContainsAll0(forbiddenSymbols, HARD_FORBIDDEN_SYMBOLS0) &&
      hard?.NoMinCheck?.rejectsAliases === true &&
      hard?.NoMinCheck?.rejectsExecutableOnly === true,

    forbiddenImportEdgeCount: Array.isArray(forbiddenImportEdges) ? forbiddenImportEdges.length : null,
    forbiddenImportEdges,
    expectedForbiddenImportEdges: deepClone0(HARD_FORBIDDEN_IMPORT_EDGES0),
    missingForbiddenImportEdges: expectedForbiddenImportEdgeKeys.filter((key) => !forbiddenImportEdgeKeys.has(key)),
    importPolicyComplete:
      hard?.ImportCheck?.acyclic === true &&
      expectedForbiddenImportEdgeKeys.every((key) => forbiddenImportEdgeKeys.has(key)),

    reflectionPolicyComplete:
      hard?.ReflectionCheck?.exact === true &&
      hard?.ReflectionCheck?.publicConclusion === true &&
      hard?.ReflectionCheck?.replayable === true,

    boundsPolicyComplete:
      hard?.BoundsCheck?.polynomialBounds === true &&
      hard?.BoundsCheck?.finiteSchedules === true &&
      hard?.BoundsCheck?.noPrivateSchedule === true,

    diagnosticsPolicyComplete:
      hard?.DiagCheck?.uniqueFirstFailure === true &&
      hard?.DiagCheck?.replayable === true &&
      hard?.DiagCheck?.noUnknownOutput === true,
  };
}

export async function CheckConcreteMaterializedHard0(
  input,
  config = makeConcreteMaterializedHardConfig0(),
) {
  const checker = 'CheckConcreteMaterializedHard0';
  const ledger = [];
  const cfg = makeConcreteMaterializedHardConfig0(config);
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

  if (cfg.checkMaterializedHard === true) {
    const record = await CheckMaterializedHard0(
      envelope.MaterializedHardEnvelope,
      cfg.materializedHardConfig ?? {},
    );
    const result = recordToValidation0(record, ['MaterializedHardEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedHard0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedHard`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkHard === true) {
    const record = await CheckHard0(envelope.HardCheck);
    const result = recordToValidation0(record, ['HardCheck']);

    ledger.push({
      phase: 'CheckHard0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.HardCheck`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const recomputedCoverage = makeConcreteHardCoverage0(envelope.MaterializedHardEnvelope);

  if (cfg.checkCoverage === true) {
    const coverage = validateCoverage0(envelope.Coverage, recomputedCoverage);

    ledger.push({
      phase: 'coverage',
      status: coverage.ok ? 'pass' : 'fail',
      digest: digestCanonical0(coverage.nf ?? coverage.witness ?? null),
    });

    if (!coverage.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.coverage`,
        path: coverage.path,
        witness: coverage.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteMaterializedHardCheck0']);

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
    const linkage = validateLinkage0(envelope, recomputedCoverage);

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
    kind: 'ConcreteMaterializedHardCheck0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    materializedHardDigest: digestCanonical0(envelope.MaterializedHardEnvelope),
    hardCheckDigest: digestCanonical0(envelope.HardCheck),
    coverageDigest: digestCanonical0(recomputedCoverage),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    checkerCount: recomputedCoverage.checkerCount,
    checkerCoverageComplete: recomputedCoverage.checkerCoverageComplete,
    rowKeyCoverageComplete: recomputedCoverage.rowKeyCoverageComplete,
    routePriorityComplete: recomputedCoverage.routePriorityComplete,
    proofRefPolicyComplete: recomputedCoverage.proofRefPolicyComplete,
    hashDisciplineComplete: recomputedCoverage.hashDisciplineComplete,
    noMinCoverageComplete: recomputedCoverage.noMinCoverageComplete,
    importPolicyComplete: recomputedCoverage.importPolicyComplete,
    reflectionPolicyComplete: recomputedCoverage.reflectionPolicyComplete,
    boundsPolicyComplete: recomputedCoverage.boundsPolicyComplete,
    diagnosticsPolicyComplete: recomputedCoverage.diagnosticsPolicyComplete,

    rowKeyFieldCount: recomputedCoverage.rowKeyFieldCount,
    forbiddenSymbolCount: recomputedCoverage.forbiddenSymbolCount,
    forbiddenImportEdgeCount: recomputedCoverage.forbiddenImportEdgeCount,

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

export async function writeConcreteMaterializedHardFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedHardFiles0 requires a non-empty output directory');
  }

  const envelope = makeConcreteMaterializedHard0(options);
  const checked = await CheckConcreteMaterializedHard0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedHardCheck0.json');
  const materializedHardPath = path.join(outDir, 'MaterializedHardCheck0.json');
  const hardCheckPath = path.join(outDir, 'HardCheck0.json');
  const coveragePath = path.join(outDir, 'ConcreteHardCoverage0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedHardCheck0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(materializedHardPath, envelope.MaterializedHardEnvelope);
  await writeJsonFile0(hardCheckPath, envelope.HardCheck);
  await writeJsonFile0(coveragePath, envelope.Coverage);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      materializedHardPath,
      hardCheckPath,
      coveragePath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'MaterializedHardCheck0') {
    return makeConcreteMaterializedHard0({
      MaterializedHardEnvelope: input,
    });
  }

  if (isPlainObject(input) && input.kind === 'HardCheck0') {
    return makeConcreteMaterializedHard0({
      HardCheck: input,
    });
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedHardConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedHardConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedHardConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedHardConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkMaterializedHard',
    'checkHard',
    'checkCoverage',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedHardConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.materializedHardConfig)) {
    return validationReject0(['materializedHardConfig'], 'materializedHardConfig must be an object', {
      actual: typeof config.materializedHardConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedHardConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedHardCheck0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedHardCheck0') {
    return validationReject0(['kind'], 'ConcreteMaterializedHardCheck0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  for (const field of [
    'MaterializedHardEnvelope',
    'HardCheck',
    'Coverage',
  ]) {
    if (!isPlainObject(envelope[field])) {
      return validationReject0([field], `ConcreteMaterializedHardCheck0 must include ${field}`, {
        actual: typeof envelope[field],
      });
    }
  }

  if (!sameDigestHex0(digestCanonical0(resolveHardCheck0(envelope.MaterializedHardEnvelope)), digestCanonical0(envelope.HardCheck))) {
    return validationReject0(['HardCheck'], 'top-level HardCheck must match MaterializedHardEnvelope.HardCheck', {
      expected: digestCanonical0(resolveHardCheck0(envelope.MaterializedHardEnvelope)),
      actual: digestCanonical0(envelope.HardCheck),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedHardShape0NF',
  });
}

function validateCoverage0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['Coverage'], 'ConcreteHardCoverage0 must match recomputed hard-checker coverage', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  for (const field of [
    'checkerCoverageComplete',
    'rowKeyCoverageComplete',
    'routePriorityComplete',
    'proofRefPolicyComplete',
    'hashDisciplineComplete',
    'noMinCoverageComplete',
    'importPolicyComplete',
    'reflectionPolicyComplete',
    'boundsPolicyComplete',
    'diagnosticsPolicyComplete',
  ]) {
    if (expected[field] !== true) {
      return validationReject0(['Coverage', field], `ConcreteHardCoverage0 must certify ${field}`, {
        actual: expected[field],
        missingCheckerFields: expected.missingCheckerFields,
        wrongCheckerIds: expected.wrongCheckerIds,
        descriptorFlagFailures: expected.descriptorFlagFailures,
        missingForbiddenImportEdges: expected.missingForbiddenImportEdges,
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteHardCoverage0NF',
    coverageDigest: digestCanonical0(expected),
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteMaterializedHardCheck0'], 'ConcreteMaterializedHardCheck0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteMaterializedHardCheck0'], 'ConcreteMaterializedHardCheck0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedHardJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, coverage) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteMaterializedHardLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedHardCheck0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    materializedHardDigest: digestCanonical0(envelope.MaterializedHardEnvelope),
    hardCheckDigest: digestCanonical0(envelope.HardCheck),
    coverageDigest: digestCanonical0(coverage),
  };

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  for (const [field, expectedValue] of Object.entries({
    checkerCount: coverage.checkerCount,
    rowKeyFieldCount: coverage.rowKeyFieldCount,
    forbiddenSymbolCount: coverage.forbiddenSymbolCount,
    forbiddenImportEdgeCount: coverage.forbiddenImportEdgeCount,
  })) {
    if (envelope.Linkage[field] !== expectedValue) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedValue,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedHardLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteMaterializedHardFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_HARD_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_HARD_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_HARD_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized HardCheck contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedHardNoForbiddenFixtureMarkers0NF',
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
      CONCRETE_HARD_SYNTHETIC_MARKER0,
      ...CONCRETE_HARD_FORBIDDEN_MARKERS0,
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

function resolveHardCheck0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'HardCheck0'
    ? value
    : value.HardCheck ?? value.hardCheck ?? null;
}

function edgeKey0(edge) {
  return Array.isArray(edge)
    ? edge.join('->')
    : `${edge?.from ?? edge?.src ?? edge?.source ?? ''}->${edge?.to ?? edge?.dst ?? edge?.target ?? ''}`;
}

function arrayContainsAll0(actual, required) {
  return Array.isArray(actual) && required.every((entry) => actual.includes(entry));
}

function sameArray0(actual, expected) {
  return (
    Array.isArray(actual) &&
    Array.isArray(expected) &&
    actual.length === expected.length &&
    actual.every((entry, index) => entry === expected[index])
  );
}

function deepClone0(value) {
  return JSON.parse(JSON.stringify(value));
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
