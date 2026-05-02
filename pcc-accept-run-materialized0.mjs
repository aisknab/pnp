import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  ACCEPT_RUN_PHASES0,
  CheckAcceptRun0,
  EmitFinalVerdict0,
  ReplayAcceptRun0,
} from './pcc-accept-run0.mjs';

import {
  CheckMaterializedPCCPack0,
  makeMaterializedPCCPack0,
} from './pcc-pack-materialized0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_ACCEPT_RUN_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const MATERIALIZED_ACCEPT_RUN_SYNTHETIC_MARKER0 = 'synthetic';

export function makeMaterializedGeneratedAcceptRunConfig0(overrides = {}) {
  return {
    kind: 'MaterializedGeneratedAcceptRunConfig0',
    version: CHECKER_VERSION,
    checkMaterializedPCCPack: true,
    checkAcceptRun: true,
    checkReplay: true,
    checkFinalVerdict: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    pccPackConfig: {},
    ...overrides,
  };
}

export function makeGeneratePCCPackOutput0(pccPack, overrides = {}) {
  const outputCoreBytes = stableStringify0(pccPack.Core);
  const outputPackBytes = stableStringify0(pccPack);

  return {
    kind: 'GeneratePCCPackOutput0',
    version: CHECKER_VERSION,
    generator: 'GeneratePCCPack',
    deterministic: true,
    untrusted: true,
    materializedOutputOnly: true,
    canonicalJson: true,
    canonicalByteEquality: true,
    outputCoreBytes,
    outputPackBytes,
    outputCoreDigest: digestCanonical0(outputCoreBytes),
    outputPackDigest: digestCanonical0(outputPackBytes),
    pccPackObjectDigest: digestCanonical0(pccPack),
    coreObjectDigest: digestCanonical0(pccPack.Core),
    ...overrides,
  };
}

export function makeMaterializedAcceptRun0({
  pccPack,
  generatedPackage = null,
  runId = 'materialized-generated-accept-run.0',
  verdict = 'accept',
  rejectLog = [],
  overrides = {},
} = {}) {
  const generated = generatedPackage ?? makeGeneratePCCPackOutput0(pccPack);
  const accepted = verdict === 'accept';

  return {
    kind: 'AcceptRun0',
    version: CHECKER_VERSION,

    RunID: runId,

    GenCall: {
      kind: 'GenCall0',
      version: CHECKER_VERSION,
      generator: 'GeneratePCCPack',
      args: [],
      deterministic: true,
      untrusted: true,
      materializedOutputOnly: true,
      canonicalByteEquality: true,
      outputCoreBytes: generated.outputCoreBytes,
      outputPackBytes: generated.outputPackBytes,
      outputCoreDigest: generated.outputCoreDigest,
      outputPackDigest: generated.outputPackDigest,
    },

    Pgen: pccPack,

    Env: {
      kind: 'AcceptEnv0',
      version: CHECKER_VERSION,
      deterministic: true,
      platform: 'node-esm',
      noNetwork: true,
      noClockDependency: true,
      noRandomness: true,
      canonicalJson: true,
    },

    PhaseOrder: [...ACCEPT_RUN_PHASES0],

    Transcript: {
      kind: 'AcceptTranscript0',
      version: CHECKER_VERSION,
      phaseOrder: [...ACCEPT_RUN_PHASES0],
      entries: ACCEPT_RUN_PHASES0.map((phase, index) => ({
        index,
        phase,
        replayed: true,
      })),
    },

    AuditLogs: {
      kind: 'AcceptAuditLogs0',
      version: CHECKER_VERSION,
      canonicalByteComparisons: [
        {
          left: 'GenCall.outputCoreBytes',
          right: 'Pgen.Core',
          method: 'canonical-bytes',
          equal: true,
        },
        {
          left: 'GenCall.outputPackBytes',
          right: 'Pgen',
          method: 'canonical-bytes',
          equal: true,
        },
      ],
      digestComparisonsOnly: false,
      replayable: true,
    },

    RejectLog: [...rejectLog],

    Verdict: {
      kind: 'FinalVerdict0',
      version: CHECKER_VERSION,
      verdict,
      conditional: accepted,
      noClaimBeforeAccept: true,
      publicConclusionEmitted: accepted,
      rejectionOnly: !accepted,
      publicConclusion: accepted
        ? {
            antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
            consequent: 'P = NP',
          }
        : null,
    },

    PiRun: {
      kind: 'PiAcceptRun0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-generated-accept-run',
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'Pgen',
          digest: digestCanonical0(pccPack),
        },
        {
          kind: 'MaterializedRef0',
          target: 'GeneratePCCPackOutput0',
          digest: digestCanonical0(generated),
        },
      ],
    },

    ...overrides,
  };
}

export async function makeMaterializedGeneratedAcceptRun0({
  MaterializedPCCPack = null,
  GeneratedPackage = null,
  AcceptRun = null,
  overrides = {},
} = {}) {
  const materializedPCCPack = MaterializedPCCPack ?? await makeMaterializedPCCPack0();
  const pccPack = resolvePCCPack0(materializedPCCPack);

  const generatedPackage = GeneratedPackage ?? makeGeneratePCCPackOutput0(pccPack);
  const acceptRun = AcceptRun ?? makeMaterializedAcceptRun0({
    pccPack,
    generatedPackage,
  });

  const linkage = {
    kind: 'MaterializedGeneratedAcceptRunLinkage0',
    version: CHECKER_VERSION,
    materializedPCCPackDigest: digestCanonical0(materializedPCCPack),
    pccPackDigest: digestCanonical0(pccPack),
    generatedPackageDigest: digestCanonical0(generatedPackage),
    acceptRunDigest: digestCanonical0(acceptRun),
    outputCoreDigest: digestCanonical0(generatedPackage.outputCoreBytes),
    outputPackDigest: digestCanonical0(generatedPackage.outputPackBytes),
    phaseOrder: [...ACCEPT_RUN_PHASES0],
  };

  return {
    kind: 'MaterializedGeneratedAcceptRun0',
    version: CHECKER_VERSION,
    MaterializedPCCPack: materializedPCCPack,
    GeneratedPackage: generatedPackage,
    AcceptRun: acceptRun,
    Linkage: linkage,
    PiMaterializedGeneratedAcceptRun: {
      kind: 'PiMaterializedGeneratedAcceptRun0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'MaterializedPCCPack',
          digest: linkage.materializedPCCPackDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'GeneratedPackage',
          digest: linkage.generatedPackageDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'AcceptRun',
          digest: linkage.acceptRunDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckMaterializedGeneratedAcceptRun0(
  input,
  config = makeMaterializedGeneratedAcceptRunConfig0(),
) {
  const checker = 'CheckMaterializedGeneratedAcceptRun0';
  const ledger = [];
  const cfg = makeMaterializedGeneratedAcceptRunConfig0(config);
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

  if (cfg.checkMaterializedPCCPack === true) {
    const pccPackRecord = await CheckMaterializedPCCPack0(
      envelope.MaterializedPCCPack,
      cfg.pccPackConfig ?? {},
    );
    const pccPack = recordToValidation0(pccPackRecord, ['MaterializedPCCPack']);

    ledger.push({
      phase: 'CheckMaterializedPCCPack0',
      status: pccPack.ok ? 'pass' : 'fail',
      digest: pccPackRecord.Digest ?? pccPackRecord.digest ?? digestCanonical0(pccPackRecord),
    });

    if (!pccPack.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedPCCPack`,
        path: pccPack.path,
        witness: pccPack.witness,
        ledger,
      });
    }
  }

  if (cfg.checkAcceptRun === true) {
    const acceptRunRecord = await CheckAcceptRun0(envelope.AcceptRun);
    const acceptRun = recordToValidation0(acceptRunRecord, ['AcceptRun']);

    ledger.push({
      phase: 'CheckAcceptRun0',
      status: acceptRun.ok ? 'pass' : 'fail',
      digest: acceptRunRecord.Digest ?? acceptRunRecord.digest ?? digestCanonical0(acceptRunRecord),
    });

    if (!acceptRun.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.AcceptRun`,
        path: acceptRun.path,
        witness: acceptRun.witness,
        ledger,
      });
    }
  }

  if (cfg.checkReplay === true) {
    const replayRecord = await ReplayAcceptRun0(envelope.AcceptRun);
    const replay = recordToValidation0(replayRecord, ['AcceptRun']);

    ledger.push({
      phase: 'ReplayAcceptRun0',
      status: replay.ok ? 'pass' : 'fail',
      digest: replayRecord.Digest ?? replayRecord.digest ?? digestCanonical0(replayRecord),
    });

    if (!replay.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ReplayAcceptRun0`,
        path: replay.path,
        witness: replay.witness,
        ledger,
      });
    }
  }

  if (cfg.checkFinalVerdict === true) {
    const finalRecord = await EmitFinalVerdict0(envelope.AcceptRun);
    const finalVerdict = recordToValidation0(finalRecord, ['AcceptRun']);

    ledger.push({
      phase: 'EmitFinalVerdict0',
      status: finalVerdict.ok ? 'pass' : 'fail',
      digest: finalRecord.Digest ?? finalRecord.digest ?? digestCanonical0(finalRecord),
    });

    if (!finalVerdict.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.EmitFinalVerdict0`,
        path: finalVerdict.path,
        witness: finalVerdict.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['MaterializedGeneratedAcceptRun0']);

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

  const acceptRunRecord = await CheckAcceptRun0(envelope.AcceptRun);
  const replayRecord = await ReplayAcceptRun0(envelope.AcceptRun);
  const finalRecord = await EmitFinalVerdict0(envelope.AcceptRun);
  const acceptNF = acceptRunRecord.NF ?? acceptRunRecord.nf ?? {};
  const finalNF = finalRecord.NF ?? finalRecord.nf ?? {};
  const pccPack = resolvePCCPack0(envelope.MaterializedPCCPack);

  const nf = {
    kind: 'MaterializedGeneratedAcceptRun0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    generator: 'GeneratePCCPack',
    runId: envelope.AcceptRun.RunID,
    verdict: acceptNF.verdict ?? envelope.AcceptRun.Verdict.verdict,
    replayAccepted: acceptNF.replayAccepted ?? true,
    publicConclusionEmitted: finalNF.publicConclusionEmitted ?? false,
    publicConclusion: finalNF.publicConclusion ?? null,
    pccPackDigest: digestCanonical0(pccPack),
    generatedPackageDigest: digestCanonical0(envelope.GeneratedPackage),
    acceptRunDigest: acceptRunRecord.Digest ?? acceptRunRecord.digest,
    replayDigest: replayRecord.Digest ?? replayRecord.digest,
    finalVerdictDigest: finalRecord.Digest ?? finalRecord.digest,
    outputCoreDigest: digestCanonical0(envelope.GeneratedPackage.outputCoreBytes),
    outputPackDigest: digestCanonical0(envelope.GeneratedPackage.outputPackBytes),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    phaseOrder: [...ACCEPT_RUN_PHASES0],
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

export async function writeMaterializedGeneratedAcceptRunFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedGeneratedAcceptRunFiles0 requires a non-empty output directory');
  }

  const envelope = await makeMaterializedGeneratedAcceptRun0(options);
  const checked = await CheckMaterializedGeneratedAcceptRun0(envelope, options.checkConfig ?? {});
  const finalVerdict = await EmitFinalVerdict0(envelope.AcceptRun);

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedGeneratedAcceptRun0.json');
  const generatedPath = path.join(outDir, 'GeneratePCCPackOutput0.json');
  const acceptRunPath = path.join(outDir, 'AcceptRun0.json');
  const pccPackPath = path.join(outDir, 'PCCPack0.json');
  const finalVerdictPath = path.join(outDir, 'EmitFinalVerdict0.json');
  const checkPath = path.join(outDir, 'MaterializedGeneratedAcceptRun0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(generatedPath, envelope.GeneratedPackage);
  await writeJsonFile0(acceptRunPath, envelope.AcceptRun);
  await writeJsonFile0(pccPackPath, envelope.AcceptRun.Pgen);
  await writeJsonFile0(finalVerdictPath, finalVerdict);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    finalVerdict,
    files: {
      envelopePath,
      generatedPath,
      acceptRunPath,
      pccPackPath,
      finalVerdictPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'AcceptRun0') {
    return {
      kind: 'MaterializedGeneratedAcceptRun0',
      version: CHECKER_VERSION,
      MaterializedPCCPack: {
        kind: 'MaterializedPCCPack0',
        version: CHECKER_VERSION,
        PCCPack: input.Pgen,
      },
      GeneratedPackage: makeGeneratePCCPackOutput0(input.Pgen),
      AcceptRun: input,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedGeneratedAcceptRunConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedGeneratedAcceptRunConfig0') {
    return validationReject0(['kind'], 'MaterializedGeneratedAcceptRunConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedGeneratedAcceptRunConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkMaterializedPCCPack',
    'checkAcceptRun',
    'checkReplay',
    'checkFinalVerdict',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedGeneratedAcceptRunConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.pccPackConfig)) {
    return validationReject0(['pccPackConfig'], 'pccPackConfig must be an object', {
      actual: typeof config.pccPackConfig,
    });
  }

  return validationAccept0({
    kind: 'MaterializedGeneratedAcceptRunConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedGeneratedAcceptRun0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedGeneratedAcceptRun0') {
    return validationReject0(['kind'], 'MaterializedGeneratedAcceptRun0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedGeneratedAcceptRun0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.MaterializedPCCPack)) {
    return validationReject0(['MaterializedPCCPack'], 'MaterializedGeneratedAcceptRun0 must include MaterializedPCCPack', {
      actual: typeof envelope.MaterializedPCCPack,
    });
  }

  if (!isPlainObject(envelope.GeneratedPackage)) {
    return validationReject0(['GeneratedPackage'], 'MaterializedGeneratedAcceptRun0 must include GeneratedPackage', {
      actual: typeof envelope.GeneratedPackage,
    });
  }

  if (!isPlainObject(envelope.AcceptRun)) {
    return validationReject0(['AcceptRun'], 'MaterializedGeneratedAcceptRun0 must include AcceptRun', {
      actual: typeof envelope.AcceptRun,
    });
  }

  if (envelope.AcceptRun.kind !== 'AcceptRun0') {
    return validationReject0(['AcceptRun', 'kind'], 'AcceptRun kind must be AcceptRun0', {
      actual: envelope.AcceptRun.kind,
    });
  }

  return validationAccept0({
    kind: 'MaterializedGeneratedAcceptRunShape0NF',
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['MaterializedGeneratedAcceptRun0'], 'MaterializedGeneratedAcceptRun0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['MaterializedGeneratedAcceptRun0'], 'MaterializedGeneratedAcceptRun0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedGeneratedAcceptRunJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'MaterializedGeneratedAcceptRunFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === MATERIALIZED_ACCEPT_RUN_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== MATERIALIZED_ACCEPT_RUN_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== MATERIALIZED_ACCEPT_RUN_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'materialized generated accept-run contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'MaterializedGeneratedAcceptRunNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  const pccPack = resolvePCCPack0(envelope.MaterializedPCCPack);

  if (!isPlainObject(pccPack)) {
    return validationReject0(['MaterializedPCCPack', 'PCCPack'], 'MaterializedPCCPack must expose a PCCPack object', {
      actual: typeof pccPack,
    });
  }

  const expectedCoreBytes = stableStringify0(pccPack.Core);
  const expectedPackBytes = stableStringify0(pccPack);

  if (envelope.GeneratedPackage.outputCoreBytes !== expectedCoreBytes) {
    return validationReject0(['GeneratedPackage', 'outputCoreBytes'], 'GeneratedPackage core bytes must match PCCPack.Core canonical bytes', {
      expectedDigest: digestCanonical0(expectedCoreBytes),
      actualDigest: digestCanonical0(envelope.GeneratedPackage.outputCoreBytes),
    });
  }

  if (envelope.GeneratedPackage.outputPackBytes !== expectedPackBytes) {
    return validationReject0(['GeneratedPackage', 'outputPackBytes'], 'GeneratedPackage pack bytes must match PCCPack canonical bytes', {
      expectedDigest: digestCanonical0(expectedPackBytes),
      actualDigest: digestCanonical0(envelope.GeneratedPackage.outputPackBytes),
    });
  }

  if (envelope.AcceptRun.GenCall.outputCoreBytes !== expectedCoreBytes) {
    return validationReject0(['AcceptRun', 'GenCall', 'outputCoreBytes'], 'AcceptRun GenCall core bytes must match PCCPack.Core canonical bytes', {
      expectedDigest: digestCanonical0(expectedCoreBytes),
      actualDigest: digestCanonical0(envelope.AcceptRun.GenCall.outputCoreBytes),
    });
  }

  if (envelope.AcceptRun.GenCall.outputPackBytes !== expectedPackBytes) {
    return validationReject0(['AcceptRun', 'GenCall', 'outputPackBytes'], 'AcceptRun GenCall pack bytes must match PCCPack canonical bytes', {
      expectedDigest: digestCanonical0(expectedPackBytes),
      actualDigest: digestCanonical0(envelope.AcceptRun.GenCall.outputPackBytes),
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.AcceptRun.Pgen), digestCanonical0(pccPack))) {
    return validationReject0(['AcceptRun', 'Pgen'], 'AcceptRun Pgen must match materialized PCCPack', {
      expected: digestCanonical0(pccPack),
      actual: digestCanonical0(envelope.AcceptRun.Pgen),
    });
  }

  const expected = {
    materializedPCCPackDigest: digestCanonical0(envelope.MaterializedPCCPack),
    pccPackDigest: digestCanonical0(pccPack),
    generatedPackageDigest: digestCanonical0(envelope.GeneratedPackage),
    acceptRunDigest: digestCanonical0(envelope.AcceptRun),
    outputCoreDigest: digestCanonical0(envelope.GeneratedPackage.outputCoreBytes),
    outputPackDigest: digestCanonical0(envelope.GeneratedPackage.outputPackBytes),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedGeneratedAcceptRunLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedGeneratedAcceptRun0 Linkage must be an object when present', {
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

  for (let index = 0; index < ACCEPT_RUN_PHASES0.length; index += 1) {
    if (envelope.Linkage.phaseOrder[index] !== ACCEPT_RUN_PHASES0[index]) {
      return validationReject0(['Linkage', 'phaseOrder', index], 'Linkage phaseOrder mismatch', {
        expected: ACCEPT_RUN_PHASES0[index],
        actual: envelope.Linkage.phaseOrder[index],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedGeneratedAcceptRunLinkage0NF',
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
      MATERIALIZED_ACCEPT_RUN_SYNTHETIC_MARKER0,
      ...MATERIALIZED_ACCEPT_RUN_FORBIDDEN_MARKERS0,
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

function resolvePCCPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'PCCPack0'
    ? value
    : value.PCCPack ?? value.pccPack ?? value.Pgen ?? null;
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
