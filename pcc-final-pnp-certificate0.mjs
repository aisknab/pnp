import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckConcreteFinalAcceptanceReplay0,
  makeConcreteFinalAcceptanceReplay0,
} from './pcc-final-acceptance-replay0.mjs';

const CHECKER_VERSION = 0;

export const FINAL_PNP_CERTIFICATE_PHASES0 = Object.freeze([
  'CheckFinalPNPCertificateInput0',
  'CheckConcreteFinalAcceptanceReplay0',
  'CheckFinalPNPCertificateRecord0',
  'CheckFinalPNPCertificateContract0',
  'CheckFinalPNPCertificateJson0',
  'CheckFinalPNPCertificateLinkage0',
  'EmitFinalPNPCertificate0',
]);

export function makeFinalPNPCertificateConfig0(overrides = {}) {
  return {
    kind: 'FinalPNPCertificateConfig0',
    version: CHECKER_VERSION,
    checkConcreteFinalAcceptanceReplay: true,
    checkCertificate: true,
    checkContract: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    concreteFinalAcceptanceReplayConfig: {},
    ...overrides,
  };
}

export async function makeFinalPNPCertificate0({
  ConcreteFinalAcceptanceReplayEnvelope = null,
  Certificate = null,
  overrides = {},
} = {}) {
  const replayEnvelope =
    ConcreteFinalAcceptanceReplayEnvelope ?? await makeConcreteFinalAcceptanceReplay0();

  const replayRecord = await CheckConcreteFinalAcceptanceReplay0(replayEnvelope);

  const certificate = Certificate ?? makeFinalPNPCertificateRecord0({
    concreteFinalAcceptanceReplayEnvelope: replayEnvelope,
    concreteFinalAcceptanceReplayRecord: replayRecord,
  });

  const linkage = makeLinkage0({
    concreteFinalAcceptanceReplayEnvelope: replayEnvelope,
    concreteFinalAcceptanceReplayRecord: replayRecord,
    certificate,
  });

  return {
    kind: 'FinalPNPCertificate0',
    version: CHECKER_VERSION,
    ConcreteFinalAcceptanceReplayEnvelope: replayEnvelope,
    CheckConcreteFinalAcceptanceReplayRecord: replayRecord,
    Certificate: certificate,
    Linkage: linkage,
    PiFinalPNPCertificate: {
      kind: 'PiFinalPNPCertificate0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteFinalAcceptanceReplayEnvelope',
          digest: linkage.concreteFinalAcceptanceReplayEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckConcreteFinalAcceptanceReplayRecord',
          digest: linkage.concreteFinalAcceptanceReplayRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalPNPCertificateRecord',
          digest: linkage.certificateDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeFinalPNPCertificateRecord0({
  concreteFinalAcceptanceReplayEnvelope,
  concreteFinalAcceptanceReplayRecord,
}) {
  const resolved = resolveCertificateInputs0(concreteFinalAcceptanceReplayEnvelope);
  const replayNF = recordNF0(concreteFinalAcceptanceReplayRecord);
  const finalVerdictNF = recordNF0(concreteFinalAcceptanceReplayEnvelope?.FinalVerdictRecord);
  const checkPCCPackexpNF = recordNF0(concreteFinalAcceptanceReplayEnvelope?.CheckPCCPackexpRecord);
  const checkAcceptRunNF = recordNF0(concreteFinalAcceptanceReplayEnvelope?.CheckAcceptRunRecord);
  const replayRunNF = recordNF0(concreteFinalAcceptanceReplayEnvelope?.ReplayAcceptRunRecord);
  const acceptRun = resolved.acceptRun ?? {};

  return {
    kind: 'FinalPNPCertificateRecord0',
    version: CHECKER_VERSION,

    status: 'accepted',
    verdict: 'accept',
    theorem: {
      statement: 'P = NP',
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },
    claimBoundary: 'accepted-concrete-final-acceptance-replay',
    noClaimBeforeAccept: true,

    checker: 'CheckPCCPackexp0',
    generator: 'GeneratePCCPack',
    runId: replayNF.runId ?? acceptRun.RunID ?? null,

    finalAcceptanceReplayClosed: replayNF.finalAcceptanceReplayClosed === true,
    generatorIsGeneratePCCPack: replayNF.generatorIsGeneratePCCPack === true,
    checkAcceptRunAccepted: replayNF.checkAcceptRunAccepted === true,
    replayAccepted: replayNF.replayAccepted === true,
    finalVerdictAccepted: replayNF.finalVerdictAccepted === true,
    checkPCCPackexpAccepted: replayNF.checkPCCPackexpAccepted === true,

    publicConclusionEmitted: replayNF.publicConclusionEmitted === true,
    publicConclusionAntecedent: replayNF.publicConclusionAntecedent ?? null,
    publicConclusionConsequent: replayNF.publicConclusionConsequent ?? null,
    publicConclusionConditional: replayNF.publicConclusionConditional === true,

    generatedPackageCanonicalCoreBytesMatch:
      replayNF.generatedPackageCanonicalCoreBytesMatch === true,
    generatedPackageCanonicalPackBytesMatch:
      replayNF.generatedPackageCanonicalPackBytesMatch === true,
    acceptRunGenCallCoreBytesMatch:
      replayNF.acceptRunGenCallCoreBytesMatch === true,
    acceptRunGenCallPackBytesMatch:
      replayNF.acceptRunGenCallPackBytesMatch === true,

    checkPCCPackexpGeneratedPackageImplication:
      replayNF.checkPCCPackexpGeneratedPackageImplication === true,
    checkPCCPackexpConcreteCoverageComplete:
      replayNF.checkPCCPackexpConcreteCoverageComplete === true,
    checkPCCPackexpPCCPackLinkageComplete:
      replayNF.checkPCCPackexpPCCPackLinkageComplete === true,
    appendixCarriesCheckPCCPackexpContract:
      replayNF.appendixCarriesCheckPCCPackexpContract === true,

    releaseAuditDigest:
      resolved.releaseAuditRecord?.Digest ??
      resolved.releaseAuditRecord?.digest ??
      null,

    concreteFinalAcceptanceReplayEnvelopeDigest:
      digestCanonical0(concreteFinalAcceptanceReplayEnvelope),
    concreteFinalAcceptanceReplayRecordDigest:
      digestFromRecord0(concreteFinalAcceptanceReplayRecord),
    concreteReleaseAppendixEnvelopeDigest:
      replayNF.concreteReleaseAppendixEnvelopeDigest ?? digestCanonical0(resolved.appendixEnvelope),
    concreteReleaseAppendixDigest:
      replayNF.appendixDigest ?? digestCanonical0(resolved.appendix ?? null),

    acceptRunDigest:
      replayNF.acceptRunDigest ?? digestCanonical0(resolved.acceptRun ?? null),
    pccPackDigest:
      replayNF.pccPackDigest ?? digestCanonical0(resolved.acceptRun?.Pgen ?? null),
    generatedPackageDigest:
      replayNF.generatedPackageDigest ?? digestCanonical0(resolved.generatedPackage ?? null),
    materializedPCCPackDigest:
      replayNF.materializedPCCPackDigest ?? digestCanonical0(resolved.materializedPCCPack ?? null),

    checkAcceptRunRecordDigest:
      replayNF.checkAcceptRunRecordDigest ??
      digestFromRecord0(concreteFinalAcceptanceReplayEnvelope?.CheckAcceptRunRecord),
    replayRecordDigest:
      replayNF.replayRecordDigest ??
      digestFromRecord0(concreteFinalAcceptanceReplayEnvelope?.ReplayAcceptRunRecord),
    finalVerdictRecordDigest:
      replayNF.finalVerdictRecordDigest ??
      digestFromRecord0(concreteFinalAcceptanceReplayEnvelope?.FinalVerdictRecord),
    checkPCCPackexpRecordDigest:
      replayNF.checkPCCPackexpRecordDigest ??
      digestFromRecord0(concreteFinalAcceptanceReplayEnvelope?.CheckPCCPackexpRecord),

    acceptanceTranscriptDigest:
      digestCanonical0(acceptRun.Transcript ?? null),
    acceptRunAuditLogsDigest:
      digestCanonical0(acceptRun.AuditLogs ?? null),
    finalVerdictObjectDigest:
      digestCanonical0(acceptRun.Verdict ?? null),

    canonicalByteRoots: {
      outputCoreDigest: acceptRun.GenCall?.outputCoreDigest ?? null,
      outputPackDigest: acceptRun.GenCall?.outputPackDigest ?? null,
      outputCoreBytesDigest: digestCanonical0(acceptRun.GenCall?.outputCoreBytes ?? null),
      outputPackBytesDigest: digestCanonical0(acceptRun.GenCall?.outputPackBytes ?? null),
    },

    checkAcceptRunNFKind: checkAcceptRunNF.kind ?? null,
    replayNFKind: replayRunNF.kind ?? null,
    finalVerdictNFKind: finalVerdictNF.kind ?? null,
    checkPCCPackexpNFKind: checkPCCPackexpNF.kind ?? null,

    finalVerdictPublicConclusion:
      finalVerdictNF.publicConclusion ?? null,
  };
}

export async function CheckFinalPNPCertificate0(
  input,
  config = makeFinalPNPCertificateConfig0(),
) {
  const checker = 'CheckFinalPNPCertificate0';
  const ledger = [];
  const cfg = makeFinalPNPCertificateConfig0(config);
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
    phase: 'CheckFinalPNPCertificateInput0',
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

  let replayRecord = envelope.CheckConcreteFinalAcceptanceReplayRecord;

  if (cfg.checkConcreteFinalAcceptanceReplay === true) {
    const fresh = await CheckConcreteFinalAcceptanceReplay0(
      envelope.ConcreteFinalAcceptanceReplayEnvelope,
      cfg.concreteFinalAcceptanceReplayConfig ?? {},
    );

    const result = recordToValidation0(fresh, ['ConcreteFinalAcceptanceReplayEnvelope']);

    ledger.push({
      phase: 'CheckConcreteFinalAcceptanceReplay0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteFinalAcceptanceReplay`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.CheckConcreteFinalAcceptanceReplayRecord,
      fresh,
      ['CheckConcreteFinalAcceptanceReplayRecord'],
      'CheckConcreteFinalAcceptanceReplayRecord',
    );

    ledger.push({
      phase: 'CheckConcreteFinalAcceptanceReplayRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckConcreteFinalAcceptanceReplayRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    replayRecord = envelope.CheckConcreteFinalAcceptanceReplayRecord;
  }

  if (cfg.checkCertificate === true) {
    const expected = makeFinalPNPCertificateRecord0({
      concreteFinalAcceptanceReplayEnvelope: envelope.ConcreteFinalAcceptanceReplayEnvelope,
      concreteFinalAcceptanceReplayRecord: replayRecord,
    });

    const certificate = validateCertificateRecord0(envelope.Certificate, expected);

    ledger.push({
      phase: 'CheckFinalPNPCertificateRecord0',
      status: certificate.ok ? 'pass' : 'fail',
      digest: digestCanonical0(certificate.nf ?? certificate.witness ?? null),
    });

    if (!certificate.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.certificate`,
        path: certificate.path,
        witness: certificate.witness,
        ledger,
      });
    }
  }

  const contract = validateFinalPNPCertificateContract0(envelope.Certificate, replayRecord);

  if (cfg.checkContract === true) {
    ledger.push({
      phase: 'CheckFinalPNPCertificateContract0',
      status: contract.ok ? 'pass' : 'fail',
      digest: digestCanonical0(contract.nf ?? contract.witness ?? null),
    });

    if (!contract.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.contract`,
        path: contract.path,
        witness: contract.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

    ledger.push({
      phase: 'CheckFinalPNPCertificateJson0',
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

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope, replayRecord);

    ledger.push({
      phase: 'CheckFinalPNPCertificateLinkage0',
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

  const cert = envelope.Certificate;

  const nf = {
    kind: 'FinalPNPCertificate0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: FINAL_PNP_CERTIFICATE_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,

    finalPNPCertificateAccepted: true,
    status: cert.status,
    verdict: cert.verdict,
    theorem: cert.theorem,
    claimBoundary: cert.claimBoundary,
    noClaimBeforeAccept: cert.noClaimBeforeAccept,

    finalAcceptanceReplayClosed: cert.finalAcceptanceReplayClosed,
    generatorIsGeneratePCCPack: cert.generatorIsGeneratePCCPack,
    checkAcceptRunAccepted: cert.checkAcceptRunAccepted,
    replayAccepted: cert.replayAccepted,
    finalVerdictAccepted: cert.finalVerdictAccepted,
    checkPCCPackexpAccepted: cert.checkPCCPackexpAccepted,

    publicConclusionEmitted: cert.publicConclusionEmitted,
    publicConclusionAntecedent: cert.publicConclusionAntecedent,
    publicConclusionConsequent: cert.publicConclusionConsequent,
    publicConclusionConditional: cert.publicConclusionConditional,

    checkPCCPackexpGeneratedPackageImplication:
      cert.checkPCCPackexpGeneratedPackageImplication,
    checkPCCPackexpConcreteCoverageComplete:
      cert.checkPCCPackexpConcreteCoverageComplete,
    checkPCCPackexpPCCPackLinkageComplete:
      cert.checkPCCPackexpPCCPackLinkageComplete,

    releaseAuditDigest: cert.releaseAuditDigest,
    concreteFinalAcceptanceReplayEnvelopeDigest:
      cert.concreteFinalAcceptanceReplayEnvelopeDigest,
    concreteFinalAcceptanceReplayRecordDigest:
      cert.concreteFinalAcceptanceReplayRecordDigest,
    concreteReleaseAppendixEnvelopeDigest:
      cert.concreteReleaseAppendixEnvelopeDigest,
    concreteReleaseAppendixDigest:
      cert.concreteReleaseAppendixDigest,
    acceptRunDigest: cert.acceptRunDigest,
    pccPackDigest: cert.pccPackDigest,
    generatedPackageDigest: cert.generatedPackageDigest,
    materializedPCCPackDigest: cert.materializedPCCPackDigest,
    checkAcceptRunRecordDigest: cert.checkAcceptRunRecordDigest,
    replayRecordDigest: cert.replayRecordDigest,
    finalVerdictRecordDigest: cert.finalVerdictRecordDigest,
    checkPCCPackexpRecordDigest: cert.checkPCCPackexpRecordDigest,
    acceptanceTranscriptDigest: cert.acceptanceTranscriptDigest,
    acceptRunAuditLogsDigest: cert.acceptRunAuditLogsDigest,
    finalVerdictObjectDigest: cert.finalVerdictObjectDigest,
    canonicalByteRoots: cert.canonicalByteRoots,

    certificateDigest: digestCanonical0(cert),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeFinalPNPCertificateFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeFinalPNPCertificateFiles0 requires a non-empty output directory');
  }

  const envelope = await makeFinalPNPCertificate0(options);
  const checked = await CheckFinalPNPCertificate0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'FinalPNPCertificate0.json');
  const certificatePath = path.join(outDir, 'FinalPNPCertificateRecord0.json');
  const replayPath = path.join(outDir, 'ConcreteFinalAcceptanceReplay0.json');
  const replayCheckPath = path.join(outDir, 'ConcreteFinalAcceptanceReplay0.check.json');
  const appendixPath = path.join(outDir, 'ConcreteReleaseAppendix0.json');
  const finalVerdictPath = path.join(outDir, 'EmitFinalVerdict0.json');
  const checkPCCPackexpPath = path.join(outDir, 'CheckPCCPackexp0.json');
  const checkPath = path.join(outDir, 'FinalPNPCertificate0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(certificatePath, envelope.Certificate);
  await writeJsonFile0(replayPath, envelope.ConcreteFinalAcceptanceReplayEnvelope);
  await writeJsonFile0(replayCheckPath, envelope.CheckConcreteFinalAcceptanceReplayRecord);
  await writeJsonFile0(appendixPath, envelope.ConcreteFinalAcceptanceReplayEnvelope.ConcreteReleaseAppendixEnvelope);
  await writeJsonFile0(finalVerdictPath, envelope.ConcreteFinalAcceptanceReplayEnvelope.FinalVerdictRecord);
  await writeJsonFile0(checkPCCPackexpPath, envelope.ConcreteFinalAcceptanceReplayEnvelope.CheckPCCPackexpRecord);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      certificatePath,
      replayPath,
      replayCheckPath,
      appendixPath,
      finalVerdictPath,
      checkPCCPackexpPath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'FinalPNPCertificateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'FinalPNPCertificateConfig0') {
    return validationReject0(['kind'], 'FinalPNPCertificateConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalPNPCertificateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteFinalAcceptanceReplay',
    'checkCertificate',
    'checkContract',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `FinalPNPCertificateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concreteFinalAcceptanceReplayConfig)) {
    return validationReject0(['concreteFinalAcceptanceReplayConfig'], 'concreteFinalAcceptanceReplayConfig must be an object', {
      actual: typeof config.concreteFinalAcceptanceReplayConfig,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPCertificateConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'FinalPNPCertificate0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'FinalPNPCertificate0') {
    return validationReject0(['kind'], 'FinalPNPCertificate0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalPNPCertificate0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ConcreteFinalAcceptanceReplayEnvelope)) {
    return validationReject0(['ConcreteFinalAcceptanceReplayEnvelope'], 'FinalPNPCertificate0 must include ConcreteFinalAcceptanceReplayEnvelope', {
      actual: typeof envelope.ConcreteFinalAcceptanceReplayEnvelope,
    });
  }

  if (!isPlainObject(envelope.CheckConcreteFinalAcceptanceReplayRecord)) {
    return validationReject0(['CheckConcreteFinalAcceptanceReplayRecord'], 'FinalPNPCertificate0 must include CheckConcreteFinalAcceptanceReplayRecord', {
      actual: typeof envelope.CheckConcreteFinalAcceptanceReplayRecord,
    });
  }

  if (!isPlainObject(envelope.Certificate)) {
    return validationReject0(['Certificate'], 'FinalPNPCertificate0 must include Certificate', {
      actual: typeof envelope.Certificate,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPCertificateShape0NF',
  });
}

function validateMaterializedRecord0(actual, expected, path, label) {
  if (!isPlainObject(actual)) {
    return validationReject0(path, `${label} must be materialized`, {
      actual: typeof actual,
    });
  }

  if (!sameDigestHex0(digestFromRecord0(actual), digestFromRecord0(expected))) {
    return validationReject0(path, `${label} digest must match freshly recomputed record`, {
      expected: digestFromRecord0(expected),
      actual: digestFromRecord0(actual),
    });
  }

  return validationAccept0({
    kind: `${label}MaterializedRecord0NF`,
    digest: digestFromRecord0(actual),
  });
}

function validateCertificateRecord0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['Certificate'], 'FinalPNPCertificate record must match recomputed certificate summary', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  return validationAccept0({
    kind: 'FinalPNPCertificateRecord0NF',
    certificateDigest: digestCanonical0(actual),
  });
}

function validateFinalPNPCertificateContract0(certificate, replayRecord) {
  if (!isPlainObject(certificate)) {
    return validationReject0(['Certificate'], 'FinalPNPCertificate record must be an object', {
      actual: typeof certificate,
    });
  }

  const requiredTrue = [
    'noClaimBeforeAccept',
    'finalAcceptanceReplayClosed',
    'generatorIsGeneratePCCPack',
    'checkAcceptRunAccepted',
    'replayAccepted',
    'finalVerdictAccepted',
    'checkPCCPackexpAccepted',
    'publicConclusionEmitted',
    'publicConclusionConditional',
    'generatedPackageCanonicalCoreBytesMatch',
    'generatedPackageCanonicalPackBytesMatch',
    'acceptRunGenCallCoreBytesMatch',
    'acceptRunGenCallPackBytesMatch',
    'checkPCCPackexpGeneratedPackageImplication',
    'checkPCCPackexpConcreteCoverageComplete',
    'checkPCCPackexpPCCPackLinkageComplete',
    'appendixCarriesCheckPCCPackexpContract',
  ];

  for (const field of requiredTrue) {
    if (certificate[field] !== true) {
      return validationReject0(['Certificate', field], `FinalPNPCertificate must certify ${field}`, {
        actual: certificate[field],
      });
    }
  }

  if (certificate.status !== 'accepted' || certificate.verdict !== 'accept') {
    return validationReject0(['Certificate', 'status'], 'FinalPNPCertificate must record accepted verdict', {
      status: certificate.status,
      verdict: certificate.verdict,
    });
  }

  if (certificate.checker !== 'CheckPCCPackexp0') {
    return validationReject0(['Certificate', 'checker'], 'FinalPNPCertificate must name CheckPCCPackexp0', {
      actual: certificate.checker,
    });
  }

  if (certificate.generator !== 'GeneratePCCPack') {
    return validationReject0(['Certificate', 'generator'], 'FinalPNPCertificate must name GeneratePCCPack', {
      actual: certificate.generator,
    });
  }

  if (!samePublicTheorem0(certificate.theorem)) {
    return validationReject0(['Certificate', 'theorem'], 'FinalPNPCertificate theorem statement mismatch', {
      actual: certificate.theorem,
    });
  }

  if (
    certificate.publicConclusionAntecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept' ||
    certificate.publicConclusionConsequent !== 'P = NP'
  ) {
    return validationReject0(['Certificate', 'publicConclusion'], 'FinalPNPCertificate public conclusion mismatch', {
      antecedent: certificate.publicConclusionAntecedent,
      consequent: certificate.publicConclusionConsequent,
    });
  }

  if (!sameDigestHex0(certificate.concreteFinalAcceptanceReplayRecordDigest, digestFromRecord0(replayRecord))) {
    return validationReject0(['Certificate', 'concreteFinalAcceptanceReplayRecordDigest'], 'FinalPNPCertificate replay-check digest mismatch', {
      expected: digestFromRecord0(replayRecord),
      actual: certificate.concreteFinalAcceptanceReplayRecordDigest,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPCertificateContract0NF',
    finalPNPCertificateAccepted: true,
    certificateDigest: digestCanonical0(certificate),
  });
}

function resolveCertificateInputs0(concreteFinalAcceptanceReplayEnvelope) {
  const appendixEnvelope =
    concreteFinalAcceptanceReplayEnvelope?.ConcreteReleaseAppendixEnvelope ?? null;

  const gateEnvelope =
    appendixEnvelope?.ReleaseAuditConcreteFinalCertificateGateEnvelope ?? null;

  const concretePublicStatusEnvelope =
    gateEnvelope?.ConcreteFinalCertificatePublicStatusEnvelope ?? null;

  const concreteFinalCertificateEnvelope =
    concretePublicStatusEnvelope?.ConcreteFinalCertificateEnvelope ?? null;

  const concreteGeneratedAcceptRunEnvelope =
    concreteFinalCertificateEnvelope?.ConcreteGeneratedAcceptRunEnvelope ?? null;

  const generatedAcceptRunEnvelope =
    concreteGeneratedAcceptRunEnvelope?.GeneratedAcceptRunEnvelope ?? null;

  return {
    appendixEnvelope,
    appendix: appendixEnvelope?.Appendix ?? null,
    gateEnvelope,
    releaseAuditRecord: gateEnvelope?.ReleaseAuditRecord ?? null,
    concretePublicStatusEnvelope,
    concreteFinalCertificateEnvelope,
    concreteGeneratedAcceptRunEnvelope,
    generatedAcceptRunEnvelope,
    materializedPCCPack: generatedAcceptRunEnvelope?.MaterializedPCCPack ?? null,
    generatedPackage: generatedAcceptRunEnvelope?.GeneratedPackage ?? null,
    acceptRun: generatedAcceptRunEnvelope?.AcceptRun ?? null,
  };
}

function makeLinkage0({
  concreteFinalAcceptanceReplayEnvelope,
  concreteFinalAcceptanceReplayRecord,
  certificate,
}) {
  const resolved = resolveCertificateInputs0(concreteFinalAcceptanceReplayEnvelope);

  return {
    kind: 'FinalPNPCertificateLinkage0',
    version: CHECKER_VERSION,
    concreteFinalAcceptanceReplayEnvelopeDigest:
      digestCanonical0(concreteFinalAcceptanceReplayEnvelope),
    concreteFinalAcceptanceReplayRecordDigest:
      digestFromRecord0(concreteFinalAcceptanceReplayRecord),
    concreteReleaseAppendixEnvelopeDigest:
      digestCanonical0(resolved.appendixEnvelope),
    releaseAuditDigest:
      resolved.releaseAuditRecord?.Digest ??
      resolved.releaseAuditRecord?.digest ??
      null,
    acceptRunDigest:
      digestCanonical0(resolved.acceptRun ?? null),
    pccPackDigest:
      digestCanonical0(resolved.acceptRun?.Pgen ?? null),
    finalVerdictRecordDigest:
      digestFromRecord0(concreteFinalAcceptanceReplayEnvelope?.FinalVerdictRecord),
    checkPCCPackexpRecordDigest:
      digestFromRecord0(concreteFinalAcceptanceReplayEnvelope?.CheckPCCPackexpRecord),
    certificateDigest:
      digestCanonical0(certificate),
  };
}

function validateLinkage0(envelope, replayRecord) {
  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'FinalPNPCertificate0 Linkage must be an object', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = makeLinkage0({
    concreteFinalAcceptanceReplayEnvelope: envelope.ConcreteFinalAcceptanceReplayEnvelope,
    concreteFinalAcceptanceReplayRecord: replayRecord,
    certificate: envelope.Certificate,
  });

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (field === 'kind' || field === 'version') {
      continue;
    }

    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `FinalPNPCertificate0 linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'FinalPNPCertificateLinkage0NF',
    ...expected,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['FinalPNPCertificate0'], 'FinalPNPCertificate0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['FinalPNPCertificate0'], 'FinalPNPCertificate0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'FinalPNPCertificateJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function samePublicTheorem0(value) {
  return (
    isPlainObject(value) &&
    value.statement === 'P = NP' &&
    value.antecedent === 'CheckPCCPackexp(GeneratePCCPack())=accept' &&
    value.consequent === 'P = NP' &&
    value.conditional === true
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

function recordNF0(record) {
  return isPlainObject(record)
    ? record.NF ?? record.nf ?? {}
    : {};
}

function digestFromRecord0(record) {
  if (!isPlainObject(record)) {
    return null;
  }

  return record.Digest ?? record.digest ?? (
    isPlainObject(record.NF ?? record.nf)
      ? digestCanonical0(record.NF ?? record.nf)
      : digestCanonical0(record)
  );
}

function compactReject0(record) {
  if (!isRejectRecord0(record)) {
    return null;
  }

  return {
    checker: record.checker,
    coord: record.Coord ?? record.coord,
    path: record.Path ?? record.path,
    witness: record.Witness ?? record.witness,
    digest: record.Digest ?? record.digest,
  };
}

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  if (value.tag === 'reject' || value.kind === 'reject') {
    return 'reject';
  }

  if (value.tag === 'accept' || value.kind === 'accept') {
    return 'accept';
  }

  return 'unknown';
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

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}
