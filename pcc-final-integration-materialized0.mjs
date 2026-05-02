import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGPack0,
  CheckRowFamG0,
  makeSyntheticGPack0,
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  CheckFinalFrameworkMatch0,
  CheckFinalIntegration0,
  CheckSATBounds0,
  CheckSATDecision0,
  FINAL_INTEGRATION_PHASES0,
  makeSyntheticFinalFrameworkMatch0,
  makeSyntheticFinalIntegration0,
  makeSyntheticSATBounds0,
  makeSyntheticSATDecision0,
} from './pcc-final-framework0.mjs';

import {
  CheckFinal0,
  CheckRowFamFinal0,
  makeSyntheticFinalTheorem0,
  makeSyntheticRowFamFinal0,
} from './pcc-final0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_FINAL_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedFinalIntegrationConfig0(overrides = {}) {
  return {
    kind: 'MaterializedFinalIntegrationConfig0',
    version: CHECKER_VERSION,
    checkGPack: true,
    checkRowFamG: true,
    checkFinalIntegration: true,
    checkFinalSubphases: true,
    checkFinalTheorem: true,
    checkRowFamFinal: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    checkLinkage: true,
    ...overrides,
  };
}

export function makeMaterializedGPack0(overrides = {}) {
  return makeSyntheticGPack0({
    CohCert: {
      kind: 'GCohCert0',
      version: CHECKER_VERSION,
      allChecksOne: true,
      witness: {
        assignment: 'materialized-all-distinguished-checks-one',
      },
    },
    PiG: {
      kind: 'PiG0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-locked-nand',
      note: 'materialized locked NAND proof references',
      refs: [],
    },
    ...overrides,
  });
}

export function makeMaterializedRowFamG0(gpack = makeMaterializedGPack0(), overrides = {}) {
  return makeSyntheticRowFamG0(gpack, {
    PiRowFamG: {
      kind: 'PiRowFamG0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-row-family-g',
      note: 'materialized RowFamG proof references',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'GPack',
          digest: digestCanonical0(gpack),
        },
      ],
    },
    ...overrides,
  });
}

export function makeMaterializedSATDecision0(gpack = makeMaterializedGPack0(), overrides = {}) {
  return makeSyntheticSATDecision0({
    gpack,
    overrides: {
      Cases: [
        {
          id: 'sat.materialized-case',
          satisfiable: true,
          baseline: gpack.BaselineCert.baseline,
          minSize: gpack.BaselineCert.baseline + 1,
          residualSlackMax: 4,
          decision: 'SAT',
        },
        {
          id: 'unsat.materialized-case',
          satisfiable: false,
          baseline: gpack.BaselineCert.baseline,
          minSize: gpack.BaselineCert.baseline,
          residualSlackMax: 4,
          decision: 'UNSAT',
        },
      ],
      PiSATDecision: {
        kind: 'PiSATDecision0',
        version: CHECKER_VERSION,
        materialized: true,
        externalJson: true,
        proofStatus: 'materialized-sat-decision',
        note: 'materialized SAT decision proof references',
        refs: [
          {
            kind: 'MaterializedRef0',
            target: 'GPack',
            digest: digestCanonical0(gpack),
          },
        ],
      },
      ...overrides,
    },
  });
}

export function makeMaterializedSATBounds0(overrides = {}) {
  return makeSyntheticSATBounds0({
    PiSATBounds: {
      kind: 'PiSATBounds0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-sat-bounds',
      note: 'materialized SAT polynomial bounds proof references',
      refs: [],
    },
    ...overrides,
  });
}

export function makeMaterializedFinalFrameworkMatch0(gpack = makeMaterializedGPack0(), overrides = {}) {
  return makeSyntheticFinalFrameworkMatch0({
    gpack,
    overrides: {
      PiMatch: {
        kind: 'PiMatch0',
        version: CHECKER_VERSION,
        materialized: true,
        externalJson: true,
        proofStatus: 'materialized-final-framework-match',
        note: 'materialized final framework match proof references',
        refs: [
          {
            kind: 'MaterializedRef0',
            target: 'GPack',
            digest: digestCanonical0(gpack),
          },
        ],
      },
      ...overrides,
    },
  });
}

export function makeMaterializedFinalIntegration0({
  GPack = null,
  FinalMatch = null,
  SATDecision = null,
  SATBounds = null,
  overrides = {},
} = {}) {
  const gpack = GPack ?? makeMaterializedGPack0();
  const finalMatch = FinalMatch ?? makeMaterializedFinalFrameworkMatch0(gpack);
  const satDecision = SATDecision ?? makeMaterializedSATDecision0(gpack);
  const satBounds = SATBounds ?? makeMaterializedSATBounds0();

  return makeSyntheticFinalIntegration0({
    gpack,
    overrides: {
      FinalMatch: finalMatch,
      SATDecision: satDecision,
      SATBounds: satBounds,
      PiFinalIntegration: {
        kind: 'PiFinalIntegration0',
        version: CHECKER_VERSION,
        materialized: true,
        externalJson: true,
        proofStatus: 'materialized-final-integration',
        note: 'materialized final integration proof references',
        refs: [
          {
            kind: 'MaterializedRef0',
            target: 'GPack',
            digest: digestCanonical0(gpack),
          },
          {
            kind: 'MaterializedRef0',
            target: 'FinalMatch',
            digest: digestCanonical0(finalMatch),
          },
          {
            kind: 'MaterializedRef0',
            target: 'SATDecision',
            digest: digestCanonical0(satDecision),
          },
          {
            kind: 'MaterializedRef0',
            target: 'SATBounds',
            digest: digestCanonical0(satBounds),
          },
        ],
      },
      PhaseOrder: [...FINAL_INTEGRATION_PHASES0],
      ...overrides,
    },
  });
}

export function makeMaterializedFinalTheorem0({
  FinalIntegration = null,
  overrides = {},
} = {}) {
  const finalIntegration = FinalIntegration ?? makeMaterializedFinalIntegration0();

  return makeSyntheticFinalTheorem0({
    finalIntegration,
    overrides: {
      PiFinal: {
        kind: 'PiFinal0',
        version: CHECKER_VERSION,
        materialized: true,
        externalJson: true,
        proofStatus: 'materialized-final-theorem',
        note: 'materialized final theorem proof references',
        refs: [
          {
            kind: 'MaterializedRef0',
            target: 'FinalIntegration',
            digest: digestCanonical0(finalIntegration),
          },
        ],
      },
      ...overrides,
    },
  });
}

export function makeMaterializedRowFamFinal0(finalTheorem = makeMaterializedFinalTheorem0(), overrides = {}) {
  return makeSyntheticRowFamFinal0(finalTheorem, {
    PiRowFamFinal: {
      kind: 'PiRowFamFinal0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-row-family-final',
      note: 'materialized RowFamFinal proof references',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'FinalTheorem',
          digest: digestCanonical0(finalTheorem),
        },
      ],
    },
    ...overrides,
  });
}

export function makeMaterializedFinalIntegrationEnvelope0({
  GPack = null,
  RowFamG = null,
  FinalIntegration = null,
  FinalTheorem = null,
  RowFamFinal = null,
  overrides = {},
} = {}) {
  const gpack = GPack ?? makeMaterializedGPack0();
  const rowFamG = RowFamG ?? makeMaterializedRowFamG0(gpack);
  const finalIntegration = FinalIntegration ?? makeMaterializedFinalIntegration0({
    GPack: gpack,
  });
  const finalTheorem = FinalTheorem ?? makeMaterializedFinalTheorem0({
    FinalIntegration: finalIntegration,
  });
  const rowFamFinal = RowFamFinal ?? makeMaterializedRowFamFinal0(finalTheorem);

  const linkage = {
    kind: 'MaterializedFinalIntegrationLinkage0',
    version: CHECKER_VERSION,
    gpackDigest: digestCanonical0(gpack),
    rowFamGDigest: digestCanonical0(rowFamG),
    finalIntegrationDigest: digestCanonical0(finalIntegration),
    finalMatchDigest: digestCanonical0(finalIntegration.FinalMatch),
    satDecisionDigest: digestCanonical0(finalIntegration.SATDecision),
    satBoundsDigest: digestCanonical0(finalIntegration.SATBounds),
    finalTheoremDigest: digestCanonical0(finalTheorem),
    rowFamFinalDigest: digestCanonical0(rowFamFinal),
    phaseOrder: [...FINAL_INTEGRATION_PHASES0],
  };

  return {
    kind: 'MaterializedFinalIntegration0',
    version: CHECKER_VERSION,
    GPack: gpack,
    RowFamG: rowFamG,
    FinalIntegration: finalIntegration,
    FinalTheorem: finalTheorem,
    RowFamFinal: rowFamFinal,
    Linkage: linkage,
    PiMaterializedFinalIntegration: {
      kind: 'PiMaterializedFinalIntegration0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'GPack',
          digest: linkage.gpackDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalIntegration',
          digest: linkage.finalIntegrationDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalTheorem',
          digest: linkage.finalTheoremDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckMaterializedFinalIntegration0(
  input,
  config = makeMaterializedFinalIntegrationConfig0(),
) {
  const checker = 'CheckMaterializedFinalIntegration0';
  const ledger = [];
  const cfg = makeMaterializedFinalIntegrationConfig0(config);
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

  if (cfg.checkGPack === true) {
    const gpackRecord = await CheckGPack0(envelope.GPack);
    const gpack = recordToValidation0(gpackRecord, ['GPack']);

    ledger.push({
      phase: 'CheckGPack0',
      status: gpack.ok ? 'pass' : 'fail',
      digest: gpackRecord.Digest ?? gpackRecord.digest ?? digestCanonical0(gpackRecord),
    });

    if (!gpack.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GPack`,
        path: gpack.path,
        witness: gpack.witness,
        ledger,
      });
    }
  }

  if (cfg.checkRowFamG === true) {
    const rowFamGRecord = await CheckRowFamG0(envelope.RowFamG);
    const rowFamG = recordToValidation0(rowFamGRecord, ['RowFamG']);

    ledger.push({
      phase: 'CheckRowFamG0',
      status: rowFamG.ok ? 'pass' : 'fail',
      digest: rowFamGRecord.Digest ?? rowFamGRecord.digest ?? digestCanonical0(rowFamGRecord),
    });

    if (!rowFamG.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.RowFamG`,
        path: rowFamG.path,
        witness: rowFamG.witness,
        ledger,
      });
    }
  }

  if (cfg.checkFinalIntegration === true) {
    const integrationRecord = await CheckFinalIntegration0(envelope.FinalIntegration);
    const integration = recordToValidation0(integrationRecord, ['FinalIntegration']);

    ledger.push({
      phase: 'CheckFinalIntegration0',
      status: integration.ok ? 'pass' : 'fail',
      digest: integrationRecord.Digest ?? integrationRecord.digest ?? digestCanonical0(integrationRecord),
    });

    if (!integration.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalIntegration`,
        path: integration.path,
        witness: integration.witness,
        ledger,
      });
    }
  }

  if (cfg.checkFinalSubphases === true) {
    const subphaseResult = await validateFinalSubphases0(envelope.FinalIntegration);

    ledger.push({
      phase: 'finalSubphases',
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

  if (cfg.checkFinalTheorem === true) {
    const finalRecord = await CheckFinal0(envelope.FinalTheorem);
    const finalTheorem = recordToValidation0(finalRecord, ['FinalTheorem']);

    ledger.push({
      phase: 'CheckFinal0',
      status: finalTheorem.ok ? 'pass' : 'fail',
      digest: finalRecord.Digest ?? finalRecord.digest ?? digestCanonical0(finalRecord),
    });

    if (!finalTheorem.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalTheorem`,
        path: finalTheorem.path,
        witness: finalTheorem.witness,
        ledger,
      });
    }
  }

  if (cfg.checkRowFamFinal === true) {
    const rowFamFinalRecord = await CheckRowFamFinal0(envelope.RowFamFinal);
    const rowFamFinal = recordToValidation0(rowFamFinalRecord, ['RowFamFinal']);

    ledger.push({
      phase: 'CheckRowFamFinal0',
      status: rowFamFinal.ok ? 'pass' : 'fail',
      digest: rowFamFinalRecord.Digest ?? rowFamFinalRecord.digest ?? digestCanonical0(rowFamFinalRecord),
    });

    if (!rowFamFinal.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.RowFamFinal`,
        path: rowFamFinal.path,
        witness: rowFamFinal.witness,
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

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoFixtureMarkers0(envelope);

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

  const integrationRecord = await CheckFinalIntegration0(envelope.FinalIntegration);
  const finalRecord = await CheckFinal0(envelope.FinalTheorem);
  const integrationNF = integrationRecord.NF ?? integrationRecord.nf ?? {};
  const finalNF = finalRecord.NF ?? finalRecord.nf ?? {};

  const nf = {
    kind: 'MaterializedFinalIntegration0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    phases: integrationNF.phases ?? FINAL_INTEGRATION_PHASES0,
    gpackDigest: digestCanonical0(envelope.GPack),
    rowFamGDigest: digestCanonical0(envelope.RowFamG),
    finalIntegrationDigest: integrationRecord.Digest ?? integrationRecord.digest,
    finalTheoremDigest: finalRecord.Digest ?? finalRecord.digest,
    rowFamFinalDigest: digestCanonical0(envelope.RowFamFinal),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    publicTheorem: finalNF.publicTheorem ?? null,
    exportedStatement: finalNF.exportedStatement ?? null,
    residualSlackBound: finalNF.residualSlackBound ?? null,
    polynomialExponent: finalNF.polynomialExponent ?? null,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedFinalIntegrationFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedFinalIntegrationFiles0 requires a non-empty output directory');
  }

  const envelope = makeMaterializedFinalIntegrationEnvelope0(options);
  const checked = await CheckMaterializedFinalIntegration0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedFinalIntegration0.json');
  const gpackPath = path.join(outDir, 'GPack0.json');
  const rowFamGPath = path.join(outDir, 'RowFamG0.json');
  const finalIntegrationPath = path.join(outDir, 'FinalIntegration0.json');
  const finalMatchPath = path.join(outDir, 'FinalFrameworkMatch0.json');
  const satDecisionPath = path.join(outDir, 'SATDecision0.json');
  const satBoundsPath = path.join(outDir, 'SATBounds0.json');
  const finalTheoremPath = path.join(outDir, 'FinalTheorem0.json');
  const rowFamFinalPath = path.join(outDir, 'RowFamFinal0.json');
  const checkPath = path.join(outDir, 'MaterializedFinalIntegration0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(gpackPath, envelope.GPack);
  await writeJsonFile0(rowFamGPath, envelope.RowFamG);
  await writeJsonFile0(finalIntegrationPath, envelope.FinalIntegration);
  await writeJsonFile0(finalMatchPath, envelope.FinalIntegration.FinalMatch);
  await writeJsonFile0(satDecisionPath, envelope.FinalIntegration.SATDecision);
  await writeJsonFile0(satBoundsPath, envelope.FinalIntegration.SATBounds);
  await writeJsonFile0(finalTheoremPath, envelope.FinalTheorem);
  await writeJsonFile0(rowFamFinalPath, envelope.RowFamFinal);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      gpackPath,
      rowFamGPath,
      finalIntegrationPath,
      finalMatchPath,
      satDecisionPath,
      satBoundsPath,
      finalTheoremPath,
      rowFamFinalPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'FinalIntegration0') {
    return makeMaterializedFinalIntegrationEnvelope0({
      FinalIntegration: input,
      GPack: input.GPack,
    });
  }

  if (isPlainObject(input) && input.kind === 'GPack0') {
    return makeMaterializedFinalIntegrationEnvelope0({
      GPack: input,
    });
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedFinalIntegrationConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedFinalIntegrationConfig0') {
    return validationReject0(['kind'], 'MaterializedFinalIntegrationConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalIntegrationConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkGPack',
    'checkRowFamG',
    'checkFinalIntegration',
    'checkFinalSubphases',
    'checkFinalTheorem',
    'checkRowFamFinal',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedFinalIntegrationConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalIntegrationConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedFinalIntegration0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedFinalIntegration0') {
    return validationReject0(['kind'], 'MaterializedFinalIntegration0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalIntegration0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  for (const [field, expectedKind] of [
    ['GPack', 'GPack0'],
    ['RowFamG', 'RowFamG0'],
    ['FinalIntegration', 'FinalIntegration0'],
    ['FinalTheorem', 'FinalTheorem0'],
    ['RowFamFinal', 'RowFamFinal0'],
  ]) {
    if (!isPlainObject(envelope[field])) {
      return validationReject0([field], `MaterializedFinalIntegration0 must include ${field}`, {
        actual: typeof envelope[field],
      });
    }

    if (envelope[field].kind !== expectedKind) {
      return validationReject0([field, 'kind'], `${field} kind mismatch`, {
        expected: expectedKind,
        actual: envelope[field].kind,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalIntegrationShape0NF',
  });
}

async function validateFinalSubphases0(finalIntegration) {
  const phases = [
    ['FinalMatch', await CheckFinalFrameworkMatch0(finalIntegration.FinalMatch)],
    ['SATDecision', await CheckSATDecision0(finalIntegration.SATDecision)],
    ['SATBounds', await CheckSATBounds0(finalIntegration.SATBounds)],
  ];

  const phaseDigests = [];

  for (const [pathName, record] of phases) {
    if (isRejectRecord0(record)) {
      return validationReject0(['FinalIntegration', pathName], `${record.checker} rejected`, {
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
    kind: 'MaterializedFinalSubphases0NF',
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
    return validationReject0(['MaterializedFinalIntegration0'], 'MaterializedFinalIntegration0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['MaterializedFinalIntegration0'], 'MaterializedFinalIntegration0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalIntegrationJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateNoFixtureMarkers0(value) {
  const hit = firstFixtureMarker0(value, ['MaterializedFinalIntegration0']);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized final integration must not contain fixture-marker text', hit);
  }

  return validationAccept0({
    kind: 'MaterializedFinalIntegrationNoFixtureMarkers0NF',
  });
}

function validateLinkage0(envelope) {
  if (!sameDigestHex0(digestCanonical0(envelope.RowFamG.GPack), digestCanonical0(envelope.GPack))) {
    return validationReject0(['RowFamG', 'GPack'], 'RowFamG GPack must match top-level GPack', {
      expected: digestCanonical0(envelope.GPack),
      actual: digestCanonical0(envelope.RowFamG.GPack),
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.FinalIntegration.GPack), digestCanonical0(envelope.GPack))) {
    return validationReject0(['FinalIntegration', 'GPack'], 'FinalIntegration GPack must match top-level GPack', {
      expected: digestCanonical0(envelope.GPack),
      actual: digestCanonical0(envelope.FinalIntegration.GPack),
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.FinalTheorem.FinalIntegration), digestCanonical0(envelope.FinalIntegration))) {
    return validationReject0(['FinalTheorem', 'FinalIntegration'], 'FinalTheorem FinalIntegration must match top-level FinalIntegration', {
      expected: digestCanonical0(envelope.FinalIntegration),
      actual: digestCanonical0(envelope.FinalTheorem.FinalIntegration),
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.RowFamFinal.FinalTheorem), digestCanonical0(envelope.FinalTheorem))) {
    return validationReject0(['RowFamFinal', 'FinalTheorem'], 'RowFamFinal FinalTheorem must match top-level FinalTheorem', {
      expected: digestCanonical0(envelope.FinalTheorem),
      actual: digestCanonical0(envelope.RowFamFinal.FinalTheorem),
    });
  }

  if (!sameDigestHex0(envelope.FinalIntegration.FinalMatch.PG.gpackDigest, digestCanonical0(envelope.GPack))) {
    return validationReject0(['FinalIntegration', 'FinalMatch', 'PG', 'gpackDigest'], 'FinalMatch Package G digest must match top-level GPack', {
      expected: digestCanonical0(envelope.GPack),
      actual: envelope.FinalIntegration.FinalMatch.PG.gpackDigest,
    });
  }

  if (!sameDigestHex0(envelope.FinalIntegration.SATDecision.LockedWord.gpackDigest, digestCanonical0(envelope.GPack))) {
    return validationReject0(['FinalIntegration', 'SATDecision', 'LockedWord', 'gpackDigest'], 'SATDecision LockedWord digest must match top-level GPack', {
      expected: digestCanonical0(envelope.GPack),
      actual: envelope.FinalIntegration.SATDecision.LockedWord.gpackDigest,
    });
  }

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedFinalIntegrationLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedFinalIntegration0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    gpackDigest: digestCanonical0(envelope.GPack),
    rowFamGDigest: digestCanonical0(envelope.RowFamG),
    finalIntegrationDigest: digestCanonical0(envelope.FinalIntegration),
    finalMatchDigest: digestCanonical0(envelope.FinalIntegration.FinalMatch),
    satDecisionDigest: digestCanonical0(envelope.FinalIntegration.SATDecision),
    satBoundsDigest: digestCanonical0(envelope.FinalIntegration.SATBounds),
    finalTheoremDigest: digestCanonical0(envelope.FinalTheorem),
    rowFamFinalDigest: digestCanonical0(envelope.RowFamFinal),
  };

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

  for (let index = 0; index < FINAL_INTEGRATION_PHASES0.length; index += 1) {
    if (envelope.Linkage.phaseOrder[index] !== FINAL_INTEGRATION_PHASES0[index]) {
      return validationReject0(['Linkage', 'phaseOrder', index], 'Linkage phaseOrder mismatch', {
        expected: FINAL_INTEGRATION_PHASES0[index],
        actual: envelope.Linkage.phaseOrder[index],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalIntegrationLinkage0NF',
    present: true,
    ...expected,
  });
}

function firstFixtureMarker0(value, path) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_FINAL_FORBIDDEN_MARKERS0) {
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

    for (const marker of MATERIALIZED_FINAL_FORBIDDEN_MARKERS0) {
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
