import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  EmitFinalVerdict0,
} from './pcc-accept-run0.mjs';

import {
  CheckMaterializedGeneratedAcceptRun0,
  makeMaterializedGeneratedAcceptRun0,
} from './pcc-accept-run-materialized0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_CERT_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const MATERIALIZED_CERT_SYNTHETIC_MARKER0 = 'synthetic';

export function makeMaterializedFinalCertificateConfig0(overrides = {}) {
  return {
    kind: 'MaterializedFinalCertificateConfig0',
    version: CHECKER_VERSION,
    checkGeneratedAcceptRun: true,
    checkFinalVerdict: true,
    checkCertificate: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    generatedAcceptRunConfig: {},
    ...overrides,
  };
}

export async function makeMaterializedFinalCertificate0({
  GeneratedAcceptRunEnvelope = null,
  FinalVerdict = null,
  Certificate = null,
  overrides = {},
} = {}) {
  const generatedAcceptRunEnvelope = GeneratedAcceptRunEnvelope ?? await makeMaterializedGeneratedAcceptRun0();
  const finalVerdict = FinalVerdict ?? await EmitFinalVerdict0(generatedAcceptRunEnvelope.AcceptRun);
  const certificate = Certificate ?? makeFinalCertificateRecord0(generatedAcceptRunEnvelope, finalVerdict);

  const pccPack = resolvePCCPack0(generatedAcceptRunEnvelope.MaterializedPCCPack);

  const linkage = {
    kind: 'MaterializedFinalCertificateLinkage0',
    version: CHECKER_VERSION,
    generatedAcceptRunEnvelopeDigest: digestCanonical0(generatedAcceptRunEnvelope),
    materializedPCCPackDigest: digestCanonical0(generatedAcceptRunEnvelope.MaterializedPCCPack),
    pccPackDigest: digestCanonical0(pccPack),
    generatedPackageDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage),
    acceptRunDigest: digestCanonical0(generatedAcceptRunEnvelope.AcceptRun),
    finalVerdictDigest: digestCanonical0(finalVerdict),
    finalVerdictRecordDigest: finalVerdict.Digest ?? finalVerdict.digest ?? null,
    certificateDigest: digestCanonical0(certificate),
    outputCoreDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage.outputCoreBytes),
    outputPackDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage.outputPackBytes),
  };

  return {
    kind: 'MaterializedFinalCertificate0',
    version: CHECKER_VERSION,
    GeneratedAcceptRunEnvelope: generatedAcceptRunEnvelope,
    FinalVerdict: finalVerdict,
    Certificate: certificate,
    Linkage: linkage,
    PiMaterializedFinalCertificate: {
      kind: 'PiMaterializedFinalCertificate0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'GeneratedAcceptRunEnvelope',
          digest: linkage.generatedAcceptRunEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalVerdict',
          digest: linkage.finalVerdictDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalCertificate',
          digest: linkage.certificateDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeFinalCertificateRecord0(generatedAcceptRunEnvelope, finalVerdict) {
  const pccPack = resolvePCCPack0(generatedAcceptRunEnvelope.MaterializedPCCPack);
  const acceptRun = generatedAcceptRunEnvelope.AcceptRun;
  const finalNF = finalVerdict.NF ?? finalVerdict.nf ?? {};
  const publicConclusion = finalNF.publicConclusion ?? null;

  return {
    kind: 'FinalCertificate0',
    version: CHECKER_VERSION,

    status: 'accepted',
    claimBoundary: 'conditional-on-accepted-replay',
    noClaimBeforeAccept: true,

    checker: 'CheckPCCPackexp',
    generator: 'GeneratePCCPack',
    runId: acceptRun.RunID,
    verdict: finalNF.verdict ?? acceptRun.Verdict.verdict,
    replayAccepted: true,
    publicConclusionEmitted: finalNF.publicConclusionEmitted === true,

    publicTheorem: publicConclusion,

    canonicalByteRoots: {
      kind: 'FinalCertificateCanonicalByteRoots0',
      coreBytesDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage.outputCoreBytes),
      packBytesDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage.outputPackBytes),
      coreObjectDigest: digestCanonical0(pccPack.Core),
      pccPackObjectDigest: digestCanonical0(pccPack),
    },

    artefactDigests: {
      kind: 'FinalCertificateArtefactDigests0',
      materializedPCCPackDigest: digestCanonical0(generatedAcceptRunEnvelope.MaterializedPCCPack),
      pccPackDigest: digestCanonical0(pccPack),
      generatedPackageDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage),
      acceptRunDigest: digestCanonical0(acceptRun),
      finalVerdictObjectDigest: digestCanonical0(finalVerdict),
      finalVerdictRecordDigest: finalVerdict.Digest ?? finalVerdict.digest ?? null,
    },

    acceptanceTranscript: {
      kind: 'FinalCertificateAcceptanceTranscript0',
      phaseOrder: acceptRun.PhaseOrder,
      transcriptDigest: digestCanonical0(acceptRun.Transcript),
      auditLogDigest: digestCanonical0(acceptRun.AuditLogs),
      rejectLogCount: acceptRun.RejectLog.length,
    },

    releaseAuditDigest: null,
    releaseAuditStatus: 'not-attached-to-this-materialized-certificate-yet',
  };
}

export async function CheckMaterializedFinalCertificate0(
  input,
  config = makeMaterializedFinalCertificateConfig0(),
) {
  const checker = 'CheckMaterializedFinalCertificate0';
  const ledger = [];
  const cfg = makeMaterializedFinalCertificateConfig0(config);
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

  if (cfg.checkGeneratedAcceptRun === true) {
    const generatedRunRecord = await CheckMaterializedGeneratedAcceptRun0(
      envelope.GeneratedAcceptRunEnvelope,
      cfg.generatedAcceptRunConfig ?? {},
    );
    const generatedRun = recordToValidation0(generatedRunRecord, ['GeneratedAcceptRunEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedGeneratedAcceptRun0',
      status: generatedRun.ok ? 'pass' : 'fail',
      digest: generatedRunRecord.Digest ?? generatedRunRecord.digest ?? digestCanonical0(generatedRunRecord),
    });

    if (!generatedRun.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GeneratedAcceptRun`,
        path: generatedRun.path,
        witness: generatedRun.witness,
        ledger,
      });
    }
  }

  let emittedFinalVerdict = null;

  if (cfg.checkFinalVerdict === true) {
    emittedFinalVerdict = await EmitFinalVerdict0(envelope.GeneratedAcceptRunEnvelope.AcceptRun);
    const finalVerdictResult = recordToValidation0(emittedFinalVerdict, ['GeneratedAcceptRunEnvelope', 'AcceptRun']);

    ledger.push({
      phase: 'EmitFinalVerdict0',
      status: finalVerdictResult.ok ? 'pass' : 'fail',
      digest: emittedFinalVerdict.Digest ?? emittedFinalVerdict.digest ?? digestCanonical0(emittedFinalVerdict),
    });

    if (!finalVerdictResult.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.EmitFinalVerdict0`,
        path: finalVerdictResult.path,
        witness: finalVerdictResult.witness,
        ledger,
      });
    }

    const finalVerdictRecord = validateFinalVerdictRecord0(envelope.FinalVerdict, emittedFinalVerdict);

    ledger.push({
      phase: 'finalVerdictRecord',
      status: finalVerdictRecord.ok ? 'pass' : 'fail',
      digest: digestCanonical0(finalVerdictRecord.nf ?? finalVerdictRecord.witness ?? null),
    });

    if (!finalVerdictRecord.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalVerdict`,
        path: finalVerdictRecord.path,
        witness: finalVerdictRecord.witness,
        ledger,
      });
    }
  } else {
    emittedFinalVerdict = envelope.FinalVerdict;
  }

  if (cfg.checkCertificate === true) {
    const certificate = validateCertificateRecord0(
      envelope.Certificate,
      envelope.GeneratedAcceptRunEnvelope,
      envelope.FinalVerdict,
      emittedFinalVerdict,
    );

    ledger.push({
      phase: 'certificate',
      status: certificate.ok ? 'pass' : 'fail',
      digest: digestCanonical0(certificate.nf ?? certificate.witness ?? null),
    });

    if (!certificate.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.Certificate`,
        path: certificate.path,
        witness: certificate.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['MaterializedFinalCertificate0']);

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

  const finalVerdict = envelope.FinalVerdict.NF ?? envelope.FinalVerdict.nf ?? {};
  const certificate = envelope.Certificate;

  const nf = {
    kind: 'MaterializedFinalCertificate0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    status: certificate.status,
    claimBoundary: certificate.claimBoundary,
    checkerTarget: certificate.checker,
    generator: certificate.generator,
    runId: certificate.runId,
    verdict: certificate.verdict,
    publicConclusionEmitted: finalVerdict.publicConclusionEmitted === true,
    publicTheorem: certificate.publicTheorem,
    canonicalByteRoots: certificate.canonicalByteRoots,
    artefactDigests: certificate.artefactDigests,
    acceptanceTranscript: certificate.acceptanceTranscript,
    releaseAuditDigest: certificate.releaseAuditDigest,
    releaseAuditStatus: certificate.releaseAuditStatus,
    certificateDigest: digestCanonical0(certificate),
    finalVerdictDigest: envelope.FinalVerdict.Digest ?? envelope.FinalVerdict.digest,
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

export async function writeMaterializedFinalCertificateFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedFinalCertificateFiles0 requires a non-empty output directory');
  }

  const envelope = await makeMaterializedFinalCertificate0(options);
  const checked = await CheckMaterializedFinalCertificate0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedFinalCertificate0.json');
  const certificatePath = path.join(outDir, 'FinalCertificate0.json');
  const finalVerdictPath = path.join(outDir, 'EmitFinalVerdict0.json');
  const generatedAcceptRunPath = path.join(outDir, 'MaterializedGeneratedAcceptRun0.json');
  const acceptRunPath = path.join(outDir, 'AcceptRun0.json');
  const pccPackPath = path.join(outDir, 'PCCPack0.json');
  const checkPath = path.join(outDir, 'MaterializedFinalCertificate0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(certificatePath, envelope.Certificate);
  await writeJsonFile0(finalVerdictPath, envelope.FinalVerdict);
  await writeJsonFile0(generatedAcceptRunPath, envelope.GeneratedAcceptRunEnvelope);
  await writeJsonFile0(acceptRunPath, envelope.GeneratedAcceptRunEnvelope.AcceptRun);
  await writeJsonFile0(pccPackPath, envelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      certificatePath,
      finalVerdictPath,
      generatedAcceptRunPath,
      acceptRunPath,
      pccPackPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedFinalCertificateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedFinalCertificateConfig0') {
    return validationReject0(['kind'], 'MaterializedFinalCertificateConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalCertificateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkGeneratedAcceptRun',
    'checkFinalVerdict',
    'checkCertificate',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedFinalCertificateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.generatedAcceptRunConfig)) {
    return validationReject0(['generatedAcceptRunConfig'], 'generatedAcceptRunConfig must be an object', {
      actual: typeof config.generatedAcceptRunConfig,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalCertificateConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedFinalCertificate0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedFinalCertificate0') {
    return validationReject0(['kind'], 'MaterializedFinalCertificate0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalCertificate0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.GeneratedAcceptRunEnvelope)) {
    return validationReject0(['GeneratedAcceptRunEnvelope'], 'MaterializedFinalCertificate0 must include GeneratedAcceptRunEnvelope', {
      actual: typeof envelope.GeneratedAcceptRunEnvelope,
    });
  }

  if (!isPlainObject(envelope.FinalVerdict)) {
    return validationReject0(['FinalVerdict'], 'MaterializedFinalCertificate0 must include FinalVerdict', {
      actual: typeof envelope.FinalVerdict,
    });
  }

  if (!isPlainObject(envelope.Certificate)) {
    return validationReject0(['Certificate'], 'MaterializedFinalCertificate0 must include Certificate', {
      actual: typeof envelope.Certificate,
    });
  }

  if (envelope.Certificate.kind !== 'FinalCertificate0') {
    return validationReject0(['Certificate', 'kind'], 'Certificate kind must be FinalCertificate0', {
      actual: envelope.Certificate.kind,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalCertificateShape0NF',
  });
}

function validateFinalVerdictRecord0(finalVerdict, emittedFinalVerdict) {
  if (!isPlainObject(finalVerdict)) {
    return validationReject0(['FinalVerdict'], 'FinalVerdict must be an object', {
      actual: typeof finalVerdict,
    });
  }

  if (finalVerdict.tag !== 'accept') {
    return validationReject0(['FinalVerdict', 'tag'], 'FinalVerdict record must be accepted', {
      actual: finalVerdict.tag,
    });
  }

  const nf = finalVerdict.NF ?? finalVerdict.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['FinalVerdict', 'NF'], 'FinalVerdict must expose an NF object', {
      actual: typeof nf,
    });
  }

  const expectedSelfDigest = digestCanonical0(nf);

  if (!sameDigestHex0(finalVerdict.Digest ?? finalVerdict.digest, expectedSelfDigest)) {
    return validationReject0(['FinalVerdict', 'Digest'], 'FinalVerdict Digest must match its NF', {
      expected: expectedSelfDigest,
      actual: finalVerdict.Digest ?? finalVerdict.digest,
    });
  }

  const emittedDigest = emittedFinalVerdict.Digest ?? emittedFinalVerdict.digest;

  if (!sameDigestHex0(expectedSelfDigest, emittedDigest)) {
    return validationReject0(['FinalVerdict', 'Digest'], 'FinalVerdict must match freshly emitted final verdict', {
      expected: emittedDigest,
      actual: expectedSelfDigest,
    });
  }

  if (nf.verdict !== 'accept') {
    return validationReject0(['FinalVerdict', 'NF', 'verdict'], 'FinalVerdict certificate requires accepted verdict', {
      actual: nf.verdict,
    });
  }

  if (nf.publicConclusionEmitted !== true) {
    return validationReject0(['FinalVerdict', 'NF', 'publicConclusionEmitted'], 'FinalVerdict certificate requires public conclusion emission', {
      actual: nf.publicConclusionEmitted,
    });
  }

  if (!isPublicTheorem0(nf.publicConclusion)) {
    return validationReject0(['FinalVerdict', 'NF', 'publicConclusion'], 'FinalVerdict public conclusion mismatch', {
      actual: nf.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'FinalVerdictRecord0NF',
    finalVerdictDigest: expectedSelfDigest,
  });
}

function validateCertificateRecord0(certificate, generatedAcceptRunEnvelope, finalVerdict, emittedFinalVerdict) {
  const pccPack = resolvePCCPack0(generatedAcceptRunEnvelope.MaterializedPCCPack);
  const acceptRun = generatedAcceptRunEnvelope.AcceptRun;
  const finalNF = emittedFinalVerdict.NF ?? emittedFinalVerdict.nf ?? {};

  if (certificate.status !== 'accepted') {
    return validationReject0(['Certificate', 'status'], 'FinalCertificate status must be accepted', {
      actual: certificate.status,
    });
  }

  if (certificate.claimBoundary !== 'conditional-on-accepted-replay') {
    return validationReject0(['Certificate', 'claimBoundary'], 'FinalCertificate claim boundary mismatch', {
      actual: certificate.claimBoundary,
    });
  }

  if (certificate.noClaimBeforeAccept !== true) {
    return validationReject0(['Certificate', 'noClaimBeforeAccept'], 'FinalCertificate must certify no claim before accept', {
      actual: certificate.noClaimBeforeAccept,
    });
  }

  if (certificate.checker !== 'CheckPCCPackexp') {
    return validationReject0(['Certificate', 'checker'], 'FinalCertificate checker target mismatch', {
      actual: certificate.checker,
    });
  }

  if (certificate.generator !== 'GeneratePCCPack') {
    return validationReject0(['Certificate', 'generator'], 'FinalCertificate generator mismatch', {
      actual: certificate.generator,
    });
  }

  if (certificate.runId !== acceptRun.RunID) {
    return validationReject0(['Certificate', 'runId'], 'FinalCertificate runId must match AcceptRun RunID', {
      expected: acceptRun.RunID,
      actual: certificate.runId,
    });
  }

  if (certificate.verdict !== 'accept' || certificate.verdict !== finalNF.verdict) {
    return validationReject0(['Certificate', 'verdict'], 'FinalCertificate verdict must match accepted final verdict', {
      expected: finalNF.verdict,
      actual: certificate.verdict,
    });
  }

  if (certificate.publicConclusionEmitted !== true) {
    return validationReject0(['Certificate', 'publicConclusionEmitted'], 'FinalCertificate must record public conclusion emission', {
      actual: certificate.publicConclusionEmitted,
    });
  }

  if (!isPublicTheorem0(certificate.publicTheorem)) {
    return validationReject0(['Certificate', 'publicTheorem'], 'FinalCertificate public theorem mismatch', {
      actual: certificate.publicTheorem,
    });
  }

  if (stableStringify0(certificate.publicTheorem) !== stableStringify0(finalNF.publicConclusion)) {
    return validationReject0(['Certificate', 'publicTheorem'], 'FinalCertificate public theorem must match final verdict conclusion', {
      expected: finalNF.publicConclusion,
      actual: certificate.publicTheorem,
    });
  }

  const roots = certificate.canonicalByteRoots;

  if (!isPlainObject(roots)) {
    return validationReject0(['Certificate', 'canonicalByteRoots'], 'FinalCertificate must include canonical byte roots', {
      actual: typeof roots,
    });
  }

  const expectedCoreBytesDigest = digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage.outputCoreBytes);
  const expectedPackBytesDigest = digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage.outputPackBytes);
  const expectedCoreObjectDigest = digestCanonical0(pccPack.Core);
  const expectedPccPackObjectDigest = digestCanonical0(pccPack);

  const rootChecks = [
    ['coreBytesDigest', expectedCoreBytesDigest],
    ['packBytesDigest', expectedPackBytesDigest],
    ['coreObjectDigest', expectedCoreObjectDigest],
    ['pccPackObjectDigest', expectedPccPackObjectDigest],
  ];

  for (const [field, expected] of rootChecks) {
    if (!sameDigestHex0(roots[field], expected)) {
      return validationReject0(['Certificate', 'canonicalByteRoots', field], `FinalCertificate canonical byte root ${field} mismatch`, {
        expected,
        actual: roots[field],
      });
    }
  }

  const artefacts = certificate.artefactDigests;

  if (!isPlainObject(artefacts)) {
    return validationReject0(['Certificate', 'artefactDigests'], 'FinalCertificate must include artefact digests', {
      actual: typeof artefacts,
    });
  }

  const artefactChecks = [
    ['materializedPCCPackDigest', digestCanonical0(generatedAcceptRunEnvelope.MaterializedPCCPack)],
    ['pccPackDigest', digestCanonical0(pccPack)],
    ['generatedPackageDigest', digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage)],
    ['acceptRunDigest', digestCanonical0(acceptRun)],
    ['finalVerdictObjectDigest', digestCanonical0(finalVerdict)],
    ['finalVerdictRecordDigest', finalVerdict.Digest ?? finalVerdict.digest],
  ];

  for (const [field, expected] of artefactChecks) {
    if (!sameDigestHex0(artefacts[field], expected)) {
      return validationReject0(['Certificate', 'artefactDigests', field], `FinalCertificate artefact digest ${field} mismatch`, {
        expected,
        actual: artefacts[field],
      });
    }
  }

  if (!isPlainObject(certificate.acceptanceTranscript)) {
    return validationReject0(['Certificate', 'acceptanceTranscript'], 'FinalCertificate must include acceptance transcript digest block', {
      actual: typeof certificate.acceptanceTranscript,
    });
  }

  if (!sameDigestHex0(certificate.acceptanceTranscript.transcriptDigest, digestCanonical0(acceptRun.Transcript))) {
    return validationReject0(['Certificate', 'acceptanceTranscript', 'transcriptDigest'], 'FinalCertificate transcript digest mismatch', {
      expected: digestCanonical0(acceptRun.Transcript),
      actual: certificate.acceptanceTranscript.transcriptDigest,
    });
  }

  if (!sameDigestHex0(certificate.acceptanceTranscript.auditLogDigest, digestCanonical0(acceptRun.AuditLogs))) {
    return validationReject0(['Certificate', 'acceptanceTranscript', 'auditLogDigest'], 'FinalCertificate audit log digest mismatch', {
      expected: digestCanonical0(acceptRun.AuditLogs),
      actual: certificate.acceptanceTranscript.auditLogDigest,
    });
  }

  if (certificate.acceptanceTranscript.rejectLogCount !== 0) {
    return validationReject0(['Certificate', 'acceptanceTranscript', 'rejectLogCount'], 'Accepted FinalCertificate must have zero reject-log entries', {
      actual: certificate.acceptanceTranscript.rejectLogCount,
    });
  }

  return validationAccept0({
    kind: 'FinalCertificateRecord0NF',
    certificateDigest: digestCanonical0(certificate),
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['MaterializedFinalCertificate0'], 'MaterializedFinalCertificate0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['MaterializedFinalCertificate0'], 'MaterializedFinalCertificate0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalCertificateJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'MaterializedFinalCertificateFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === MATERIALIZED_CERT_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== MATERIALIZED_CERT_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== MATERIALIZED_CERT_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'materialized final certificate contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalCertificateNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  const pccPack = resolvePCCPack0(envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack);

  const expected = {
    generatedAcceptRunEnvelopeDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope),
    materializedPCCPackDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack),
    pccPackDigest: digestCanonical0(pccPack),
    generatedPackageDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope.GeneratedPackage),
    acceptRunDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope.AcceptRun),
    finalVerdictDigest: digestCanonical0(envelope.FinalVerdict),
    finalVerdictRecordDigest: envelope.FinalVerdict.Digest ?? envelope.FinalVerdict.digest,
    certificateDigest: digestCanonical0(envelope.Certificate),
    outputCoreDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope.GeneratedPackage.outputCoreBytes),
    outputPackDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope.GeneratedPackage.outputPackBytes),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'MaterializedFinalCertificateLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'MaterializedFinalCertificate0 Linkage must be an object when present', {
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
    kind: 'MaterializedFinalCertificateLinkage0NF',
    present: true,
    ...expected,
  });
}

function isPublicTheorem0(value) {
  return (
    isPlainObject(value) &&
    value.antecedent === 'CheckPCCPackexp(GeneratePCCPack())=accept' &&
    value.consequent === 'P = NP' &&
    value.conditional === true
  );
}

function scanFixtureMarkers0(value, path, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      MATERIALIZED_CERT_SYNTHETIC_MARKER0,
      ...MATERIALIZED_CERT_FORBIDDEN_MARKERS0,
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
