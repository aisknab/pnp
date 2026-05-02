import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from './pcc-release-audit0.mjs';

import {
  CheckFinalCertificatePublicStatus0,
  makeFinalCertificatePublicStatus0,
} from './pcc-final-certificate-public-status0.mjs';

const CHECKER_VERSION = 0;

export const RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_PHASES0 = Object.freeze([
  'CheckReleaseAuditFinalCertificateGateInput0',
  'CheckReleaseAuditRecord0',
  'CheckFinalCertificatePublicStatus0',
  'CheckReleaseAuditFinalCertificatePublicConclusion0',
  'CheckReleaseAuditFinalCertificateGateLinkage0',
  'EmitReleaseAuditFinalCertificateGate0',
]);

const RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_SYNTHETIC_MARKER0 = 'synthetic';

export function makeReleaseAuditFinalCertificateGateConfig0(overrides = {}) {
  return {
    kind: 'ReleaseAuditFinalCertificateGateConfig0',
    version: CHECKER_VERSION,
    checkReleaseAuditRecord: true,
    checkFinalCertificatePublicStatus: true,
    checkPublicConclusionAlignment: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    finalCertificatePublicStatusConfig: {
      checkReleaseAuditRecord: true,
    },
    ...overrides,
  };
}

export async function makeReleaseAuditFinalCertificateGate0({
  ReleaseAuditRecord = null,
  FinalCertificatePublicStatusEnvelope = null,
  FinalCertificateEnvelope = null,
  runReleaseAudit = ReleaseAuditRecord === null,
  releaseAuditConfig = {},
  releaseAuditRunner = null,
  overrides = {},
} = {}) {
  const effectiveReleaseAuditRecord = ReleaseAuditRecord ?? (
    runReleaseAudit === true
      ? await runReleaseAudit0(releaseAuditRunner, releaseAuditConfig)
      : null
  );

  const finalCertificatePublicStatusEnvelope = FinalCertificatePublicStatusEnvelope ?? await makeFinalCertificatePublicStatus0({
    FinalCertificateEnvelope,
    ReleaseAuditRecord: effectiveReleaseAuditRecord,
  });

  const linkage = {
    kind: 'ReleaseAuditFinalCertificateGateLinkage0',
    version: CHECKER_VERSION,
    releaseAuditAttached: isPlainObject(effectiveReleaseAuditRecord),
    releaseAuditDigest: isPlainObject(effectiveReleaseAuditRecord)
      ? effectiveReleaseAuditRecord.Digest ?? effectiveReleaseAuditRecord.digest ?? digestCanonical0(effectiveReleaseAuditRecord)
      : null,
    finalCertificatePublicStatusDigest: digestCanonical0(finalCertificatePublicStatusEnvelope),
    publicStatusDigest: digestCanonical0(finalCertificatePublicStatusEnvelope.PublicStatus),
    certificateDigest: digestCanonical0(finalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(finalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      finalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      finalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.FinalVerdict.digest ??
      null,
    acceptRunDigest: digestCanonical0(finalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun),
    pccPackDigest: digestCanonical0(finalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen),
  };

  return {
    kind: 'ReleaseAuditFinalCertificateGate0',
    version: CHECKER_VERSION,
    ReleaseAuditRecord: effectiveReleaseAuditRecord,
    FinalCertificatePublicStatusEnvelope: finalCertificatePublicStatusEnvelope,
    Linkage: linkage,
    PiReleaseAuditFinalCertificateGate: {
      kind: 'PiReleaseAuditFinalCertificateGate0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ReleaseAuditRecord',
          digest: linkage.releaseAuditDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalCertificatePublicStatus',
          digest: linkage.finalCertificatePublicStatusDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckReleaseAuditFinalCertificateGate0(
  input,
  config = makeReleaseAuditFinalCertificateGateConfig0(),
) {
  const checker = 'CheckReleaseAuditFinalCertificateGate0';
  const ledger = [];
  const cfg = makeReleaseAuditFinalCertificateGateConfig0(config);
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
    phase: 'CheckReleaseAuditFinalCertificateGateInput0',
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

  if (cfg.checkReleaseAuditRecord === true) {
    const releaseAudit = validateReleaseAuditRecord0(envelope.ReleaseAuditRecord);

    ledger.push({
      phase: 'CheckReleaseAuditRecord0',
      status: releaseAudit.ok ? 'pass' : 'fail',
      digest: digestCanonical0(releaseAudit.nf ?? releaseAudit.witness ?? null),
    });

    if (!releaseAudit.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ReleaseAuditRecord`,
        path: releaseAudit.path,
        witness: releaseAudit.witness,
        ledger,
      });
    }
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
  }

  if (cfg.checkPublicConclusionAlignment === true) {
    const alignment = validatePublicConclusionAlignment0(envelope);

    ledger.push({
      phase: 'CheckReleaseAuditFinalCertificatePublicConclusion0',
      status: alignment.ok ? 'pass' : 'fail',
      digest: digestCanonical0(alignment.nf ?? alignment.witness ?? null),
    });

    if (!alignment.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.PublicConclusion`,
        path: alignment.path,
        witness: alignment.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['ReleaseAuditFinalCertificateGate0']);

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
      phase: 'CheckReleaseAuditFinalCertificateGateLinkage0',
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

  const releaseAuditNF = envelope.ReleaseAuditRecord.NF ?? envelope.ReleaseAuditRecord.nf ?? {};
  const publicStatus = envelope.FinalCertificatePublicStatusEnvelope.PublicStatus;
  const certificate = envelope.FinalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.Certificate;

  const nf = {
    kind: 'ReleaseAuditFinalCertificateGate0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,
    releaseAuditAttached: true,
    releaseAuditDigest: envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest,
    releaseAuditChecker: envelope.ReleaseAuditRecord.checker,
    releaseAuditMaterializedPublicStatusGateDigest: releaseAuditNF.materializedPublicStatusGateDigest ?? null,
    releaseAuditPublicSurfaceFreezeDigest: releaseAuditNF.publicSurfaceFreezeDigest ?? null,

    status: publicStatus.status,
    verdict: publicStatus.verdict,
    publicConclusionEmitted: publicStatus.publicConclusionEmitted,
    publicConclusion: publicStatus.publicConclusion,
    claimBoundary: publicStatus.claimBoundary,

    certificateDigest: publicStatus.certificateDigest,
    finalVerdictDigest: publicStatus.finalVerdictDigest,
    acceptRunDigest: publicStatus.acceptRunDigest,
    pccPackDigest: publicStatus.pccPackDigest,
    canonicalByteRoots: publicStatus.canonicalByteRoots,
    acceptanceTranscript: publicStatus.acceptanceTranscript,

    finalCertificatePublicStatusDigest: digestCanonical0(envelope.FinalCertificatePublicStatusEnvelope),
    publicStatusDigest: digestCanonical0(publicStatus),
    finalCertificateDigest: digestCanonical0(certificate),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
  };

  ledger.push({
    phase: 'EmitReleaseAuditFinalCertificateGate0',
    status: 'pass',
    digest: digestCanonical0(nf),
  });

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeReleaseAuditFinalCertificateGateFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeReleaseAuditFinalCertificateGateFiles0 requires a non-empty output directory');
  }

  const envelope = await makeReleaseAuditFinalCertificateGate0(options);
  const checked = await CheckReleaseAuditFinalCertificateGate0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ReleaseAuditFinalCertificateGate0.json');
  const releaseAuditPath = path.join(outDir, 'ReleaseAudit0.json');
  const finalCertificatePublicStatusPath = path.join(outDir, 'FinalCertificatePublicStatus0.json');
  const publicStatusPath = path.join(outDir, 'FinalCertificatePublicStatusEmission0.json');
  const certificatePath = path.join(outDir, 'FinalCertificate0.json');
  const checkPath = path.join(outDir, 'ReleaseAuditFinalCertificateGate0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(releaseAuditPath, envelope.ReleaseAuditRecord);
  await writeJsonFile0(finalCertificatePublicStatusPath, envelope.FinalCertificatePublicStatusEnvelope);
  await writeJsonFile0(publicStatusPath, envelope.FinalCertificatePublicStatusEnvelope.PublicStatus);
  await writeJsonFile0(certificatePath, envelope.FinalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.Certificate);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      releaseAuditPath,
      finalCertificatePublicStatusPath,
      publicStatusPath,
      certificatePath,
      checkPath,
    },
  };
}

async function runReleaseAudit0(releaseAuditRunner, releaseAuditConfig) {
  const runner = typeof releaseAuditRunner === 'function'
    ? releaseAuditRunner
    : CheckReleaseAudit0;

  return runner(makeReleaseAuditConfig0(releaseAuditConfig ?? {}));
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ReleaseAuditFinalCertificateGateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ReleaseAuditFinalCertificateGateConfig0') {
    return validationReject0(['kind'], 'ReleaseAuditFinalCertificateGateConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ReleaseAuditFinalCertificateGateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkReleaseAuditRecord',
    'checkFinalCertificatePublicStatus',
    'checkPublicConclusionAlignment',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ReleaseAuditFinalCertificateGateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.finalCertificatePublicStatusConfig)) {
    return validationReject0(['finalCertificatePublicStatusConfig'], 'finalCertificatePublicStatusConfig must be an object', {
      actual: typeof config.finalCertificatePublicStatusConfig,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditFinalCertificateGateConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ReleaseAuditFinalCertificateGate0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ReleaseAuditFinalCertificateGate0') {
    return validationReject0(['kind'], 'ReleaseAuditFinalCertificateGate0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ReleaseAuditFinalCertificateGate0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ReleaseAuditRecord)) {
    return validationReject0(['ReleaseAuditRecord'], 'ReleaseAuditFinalCertificateGate0 must include an accepted ReleaseAuditRecord', {
      actual: typeof envelope.ReleaseAuditRecord,
    });
  }

  if (!isPlainObject(envelope.FinalCertificatePublicStatusEnvelope)) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope'], 'ReleaseAuditFinalCertificateGate0 must include FinalCertificatePublicStatusEnvelope', {
      actual: typeof envelope.FinalCertificatePublicStatusEnvelope,
    });
  }

  if (!isPlainObject(envelope.FinalCertificatePublicStatusEnvelope.PublicStatus)) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope', 'PublicStatus'], 'FinalCertificatePublicStatusEnvelope must expose PublicStatus', {
      actual: typeof envelope.FinalCertificatePublicStatusEnvelope.PublicStatus,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditFinalCertificateGateShape0NF',
  });
}

function validateReleaseAuditRecord0(record) {
  if (!isPlainObject(record)) {
    return validationReject0(['ReleaseAuditRecord'], 'ReleaseAuditRecord must be an object', {
      actual: typeof record,
    });
  }

  if (record.tag !== 'accept') {
    return validationReject0(['ReleaseAuditRecord', 'tag'], 'ReleaseAuditRecord must be accepted', {
      actual: record.tag,
    });
  }

  if (record.checker !== 'CheckReleaseAudit0') {
    return validationReject0(['ReleaseAuditRecord', 'checker'], 'ReleaseAuditRecord checker mismatch', {
      actual: record.checker,
    });
  }

  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['ReleaseAuditRecord', 'NF'], 'ReleaseAuditRecord must expose NF', {
      actual: typeof nf,
    });
  }

  if (nf.kind !== 'ReleaseAudit0NF') {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'kind'], 'ReleaseAuditRecord NF kind mismatch', {
      actual: nf.kind,
    });
  }

  const expectedDigest = digestCanonical0(nf);

  if (!sameDigestHex0(record.Digest ?? record.digest, expectedDigest)) {
    return validationReject0(['ReleaseAuditRecord', 'Digest'], 'ReleaseAuditRecord Digest must match its NF', {
      expected: expectedDigest,
      actual: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditRecord0NF',
    releaseAuditDigest: record.Digest ?? record.digest,
  });
}

function validatePublicConclusionAlignment0(envelope) {
  const releaseAuditNF = envelope.ReleaseAuditRecord.NF ?? envelope.ReleaseAuditRecord.nf ?? {};
  const publicStatus = envelope.FinalCertificatePublicStatusEnvelope.PublicStatus;

  if (publicStatus.status !== 'accepted') {
    return validationReject0(['FinalCertificatePublicStatusEnvelope', 'PublicStatus', 'status'], 'final certificate public status must be accepted', {
      actual: publicStatus.status,
    });
  }

  if (publicStatus.publicConclusionEmitted !== true) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope', 'PublicStatus', 'publicConclusionEmitted'], 'accepted final certificate public status must emit public conclusion', {
      actual: publicStatus.publicConclusionEmitted,
    });
  }

  if (!samePublicConclusion0(publicStatus.publicConclusion, {
    antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    consequent: 'P = NP',
    conditional: true,
  })) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope', 'PublicStatus', 'publicConclusion'], 'final certificate public conclusion mismatch', {
      actual: publicStatus.publicConclusion,
    });
  }

  if (isPlainObject(releaseAuditNF.publicConclusion) && !samePublicConclusion0(publicStatus.publicConclusion, releaseAuditNF.publicConclusion)) {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'publicConclusion'], 'release audit public conclusion must match final certificate public conclusion', {
      expected: publicStatus.publicConclusion,
      actual: releaseAuditNF.publicConclusion,
    });
  }

  if (
    releaseAuditNF.materializedPublicStatusGateAcceptedPublicConclusionOnly !== undefined &&
    releaseAuditNF.materializedPublicStatusGateAcceptedPublicConclusionOnly !== true
  ) {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'materializedPublicStatusGateAcceptedPublicConclusionOnly'], 'release audit must certify accepted-public-conclusion-only gate discipline when present', {
      actual: releaseAuditNF.materializedPublicStatusGateAcceptedPublicConclusionOnly,
    });
  }

  if (publicStatus.releaseAuditAttached !== true) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope', 'PublicStatus', 'releaseAuditAttached'], 'final certificate public status must attach release audit', {
      actual: publicStatus.releaseAuditAttached,
    });
  }

  if (!sameDigestHex0(publicStatus.releaseAuditDigest, envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest)) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope', 'PublicStatus', 'releaseAuditDigest'], 'final certificate public status release audit digest mismatch', {
      expected: envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest,
      actual: publicStatus.releaseAuditDigest,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditFinalCertificatePublicConclusion0NF',
    publicConclusion: publicStatus.publicConclusion,
    releaseAuditDigest: envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ReleaseAuditFinalCertificateGate0'], 'ReleaseAuditFinalCertificateGate0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ReleaseAuditFinalCertificateGate0'], 'ReleaseAuditFinalCertificateGate0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditFinalCertificateGateJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ReleaseAuditFinalCertificateGateFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'release-audit final-certificate gate contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditFinalCertificateGateNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  const statusEnvelope = envelope.FinalCertificatePublicStatusEnvelope;
  const expected = {
    releaseAuditDigest: envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest,
    finalCertificatePublicStatusDigest: digestCanonical0(statusEnvelope),
    publicStatusDigest: digestCanonical0(statusEnvelope.PublicStatus),
    certificateDigest: digestCanonical0(statusEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(statusEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      statusEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      statusEnvelope.FinalCertificateEnvelope.FinalVerdict.digest,
    acceptRunDigest: digestCanonical0(statusEnvelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun),
    pccPackDigest: digestCanonical0(statusEnvelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ReleaseAuditFinalCertificateGateLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ReleaseAuditFinalCertificateGate0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  if (envelope.Linkage.releaseAuditAttached !== true) {
    return validationReject0(['Linkage', 'releaseAuditAttached'], 'Linkage must record releaseAuditAttached=true', {
      actual: envelope.Linkage.releaseAuditAttached,
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
    kind: 'ReleaseAuditFinalCertificateGateLinkage0NF',
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
      RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_SYNTHETIC_MARKER0,
      ...RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_FORBIDDEN_MARKERS0,
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

function samePublicConclusion0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.antecedent === b.antecedent &&
    a.consequent === b.consequent &&
    a.conditional === b.conditional
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
