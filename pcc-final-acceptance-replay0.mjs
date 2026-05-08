import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckAcceptRun0,
  EmitFinalVerdict0,
  ReplayAcceptRun0,
} from './pcc-accept-run0.mjs';

import {
  CheckPCCPackexp0,
} from './pcc-check-pcc-pack-exp0.mjs';

import {
  CheckConcreteReleaseAppendix0,
  makeConcreteReleaseAppendix0,
} from './pcc-concrete-release-appendix0.mjs';

const CHECKER_VERSION = 0;

export const CONCRETE_FINAL_ACCEPTANCE_REPLAY_PHASES0 = Object.freeze([
  'CheckConcreteFinalAcceptanceReplayInput0',
  'CheckConcreteReleaseAppendix0',
  'CheckAcceptRun0',
  'ReplayAcceptRun0',
  'EmitFinalVerdict0',
  'CheckPCCPackexp0',
  'CheckFinalAcceptanceReplayContract0',
  'CheckFinalAcceptanceReplayJson0',
  'CheckFinalAcceptanceReplayLinkage0',
  'EmitConcreteFinalAcceptanceReplay0',
]);

export function makeConcreteFinalAcceptanceReplayConfig0(overrides = {}) {
  return {
    kind: 'ConcreteFinalAcceptanceReplayConfig0',
    version: CHECKER_VERSION,
    checkConcreteReleaseAppendix: true,
    checkAcceptRun: true,
    checkReplay: true,
    checkFinalVerdict: true,
    checkPCCPackexp: true,
    checkContract: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    concreteReleaseAppendixConfig: {},
    ...overrides,
  };
}

export async function makeConcreteFinalAcceptanceReplay0({
  ConcreteReleaseAppendixEnvelope = null,
  overrides = {},
} = {}) {
  const concreteReleaseAppendixEnvelope =
    ConcreteReleaseAppendixEnvelope ?? await makeConcreteReleaseAppendix0();

  const resolved = resolveFinalAcceptanceInputs0(concreteReleaseAppendixEnvelope);
  const checkAcceptRunRecord = await CheckAcceptRun0(resolved.acceptRun);
  const replayRecord = await ReplayAcceptRun0(resolved.acceptRun);
  const finalVerdictRecord = await EmitFinalVerdict0(resolved.acceptRun);
  const checkPCCPackexpRecord = await CheckPCCPackexp0(resolved.materializedPCCPack);

  const linkage = makeLinkage0({
    concreteReleaseAppendixEnvelope,
    checkAcceptRunRecord,
    replayRecord,
    finalVerdictRecord,
    checkPCCPackexpRecord,
  });

  return {
    kind: 'ConcreteFinalAcceptanceReplay0',
    version: CHECKER_VERSION,
    ConcreteReleaseAppendixEnvelope: concreteReleaseAppendixEnvelope,
    CheckAcceptRunRecord: checkAcceptRunRecord,
    ReplayAcceptRunRecord: replayRecord,
    FinalVerdictRecord: finalVerdictRecord,
    CheckPCCPackexpRecord: checkPCCPackexpRecord,
    Linkage: linkage,
    PiConcreteFinalAcceptanceReplay: {
      kind: 'PiConcreteFinalAcceptanceReplay0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteReleaseAppendixEnvelope',
          digest: linkage.concreteReleaseAppendixEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckAcceptRunRecord',
          digest: linkage.checkAcceptRunRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ReplayAcceptRunRecord',
          digest: linkage.replayRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalVerdictRecord',
          digest: linkage.finalVerdictRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckPCCPackexpRecord',
          digest: linkage.checkPCCPackexpRecordDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckConcreteFinalAcceptanceReplay0(
  input,
  config = makeConcreteFinalAcceptanceReplayConfig0(),
) {
  const checker = 'CheckConcreteFinalAcceptanceReplay0';
  const ledger = [];
  const cfg = makeConcreteFinalAcceptanceReplayConfig0(config);
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
    phase: 'CheckConcreteFinalAcceptanceReplayInput0',
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

  const resolved = resolveFinalAcceptanceInputs0(envelope.ConcreteReleaseAppendixEnvelope);

  if (cfg.checkConcreteReleaseAppendix === true) {
    const appendixRecord = await CheckConcreteReleaseAppendix0(
      envelope.ConcreteReleaseAppendixEnvelope,
      cfg.concreteReleaseAppendixConfig ?? {},
    );
    const appendix = recordToValidation0(appendixRecord, ['ConcreteReleaseAppendixEnvelope']);

    ledger.push({
      phase: 'CheckConcreteReleaseAppendix0',
      status: appendix.ok ? 'pass' : 'fail',
      digest: appendixRecord.Digest ?? appendixRecord.digest ?? digestCanonical0(appendixRecord),
    });

    if (!appendix.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteReleaseAppendix`,
        path: appendix.path,
        witness: appendix.witness,
        ledger,
      });
    }
  }

  let checkAcceptRunRecord = envelope.CheckAcceptRunRecord;
  let replayRecord = envelope.ReplayAcceptRunRecord;
  let finalVerdictRecord = envelope.FinalVerdictRecord;
  let checkPCCPackexpRecord = envelope.CheckPCCPackexpRecord;

  if (cfg.checkAcceptRun === true) {
    const fresh = await CheckAcceptRun0(resolved.acceptRun);
    const result = recordToValidation0(fresh, ['AcceptRun']);

    ledger.push({
      phase: 'CheckAcceptRun0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckAcceptRun0`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.CheckAcceptRunRecord,
      fresh,
      ['CheckAcceptRunRecord'],
      'CheckAcceptRunRecord',
    );

    ledger.push({
      phase: 'CheckAcceptRunRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckAcceptRunRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    checkAcceptRunRecord = envelope.CheckAcceptRunRecord;
  }

  if (cfg.checkReplay === true) {
    const fresh = await ReplayAcceptRun0(resolved.acceptRun);
    const result = recordToValidation0(fresh, ['AcceptRun']);

    ledger.push({
      phase: 'ReplayAcceptRun0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ReplayAcceptRun0`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.ReplayAcceptRunRecord,
      fresh,
      ['ReplayAcceptRunRecord'],
      'ReplayAcceptRunRecord',
    );

    ledger.push({
      phase: 'ReplayAcceptRunRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ReplayAcceptRunRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    replayRecord = envelope.ReplayAcceptRunRecord;
  }

  if (cfg.checkFinalVerdict === true) {
    const fresh = await EmitFinalVerdict0(resolved.acceptRun);
    const result = recordToValidation0(fresh, ['AcceptRun']);

    ledger.push({
      phase: 'EmitFinalVerdict0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.EmitFinalVerdict0`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.FinalVerdictRecord,
      fresh,
      ['FinalVerdictRecord'],
      'FinalVerdictRecord',
    );

    ledger.push({
      phase: 'FinalVerdictRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalVerdictRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    finalVerdictRecord = envelope.FinalVerdictRecord;
  }

  if (cfg.checkPCCPackexp === true) {
    const fresh = await CheckPCCPackexp0(resolved.materializedPCCPack);
    const result = recordToValidation0(fresh, ['MaterializedPCCPack']);

    ledger.push({
      phase: 'CheckPCCPackexp0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexp0`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.CheckPCCPackexpRecord,
      fresh,
      ['CheckPCCPackexpRecord'],
      'CheckPCCPackexpRecord',
    );

    ledger.push({
      phase: 'CheckPCCPackexpRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexpRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    checkPCCPackexpRecord = envelope.CheckPCCPackexpRecord;
  }

  const contract = validateFinalAcceptanceReplayContract0({
    envelope,
    resolved,
    checkAcceptRunRecord,
    replayRecord,
    finalVerdictRecord,
    checkPCCPackexpRecord,
  });

  if (cfg.checkContract === true) {
    ledger.push({
      phase: 'CheckFinalAcceptanceReplayContract0',
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
      phase: 'CheckFinalAcceptanceReplayJson0',
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
    const linkage = validateLinkage0(envelope, {
      concreteReleaseAppendixEnvelope: envelope.ConcreteReleaseAppendixEnvelope,
      checkAcceptRunRecord,
      replayRecord,
      finalVerdictRecord,
      checkPCCPackexpRecord,
    });

    ledger.push({
      phase: 'CheckFinalAcceptanceReplayLinkage0',
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

  const contractNF = contract.nf ?? {};
  const linkage = makeLinkage0({
    concreteReleaseAppendixEnvelope: envelope.ConcreteReleaseAppendixEnvelope,
    checkAcceptRunRecord,
    replayRecord,
    finalVerdictRecord,
    checkPCCPackexpRecord,
  });

  const nf = {
    kind: 'ConcreteFinalAcceptanceReplay0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: CONCRETE_FINAL_ACCEPTANCE_REPLAY_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,

    finalAcceptanceReplayClosed: true,
    runId: resolved.acceptRun?.RunID ?? null,
    generator: resolved.acceptRun?.GenCall?.generator ?? null,
    generatorIsGeneratePCCPack: contractNF.generatorIsGeneratePCCPack === true,

    checkAcceptRunAccepted: contractNF.checkAcceptRunAccepted === true,
    replayAccepted: contractNF.replayAccepted === true,
    finalVerdictAccepted: contractNF.finalVerdictAccepted === true,
    checkPCCPackexpAccepted: contractNF.checkPCCPackexpAccepted === true,

    verdict: contractNF.verdict ?? null,
    publicConclusionEmitted: contractNF.publicConclusionEmitted === true,
    publicConclusionAntecedent: contractNF.publicConclusionAntecedent ?? null,
    publicConclusionConsequent: contractNF.publicConclusionConsequent ?? null,
    publicConclusionConditional: contractNF.publicConclusionConditional === true,

    generatedPackageCanonicalCoreBytesMatch: contractNF.generatedPackageCanonicalCoreBytesMatch === true,
    generatedPackageCanonicalPackBytesMatch: contractNF.generatedPackageCanonicalPackBytesMatch === true,
    acceptRunGenCallCoreBytesMatch: contractNF.acceptRunGenCallCoreBytesMatch === true,
    acceptRunGenCallPackBytesMatch: contractNF.acceptRunGenCallPackBytesMatch === true,
    checkPCCPackexpGeneratedPackageImplication: contractNF.checkPCCPackexpGeneratedPackageImplication === true,
    checkPCCPackexpConcreteCoverageComplete: contractNF.checkPCCPackexpConcreteCoverageComplete === true,
    checkPCCPackexpPCCPackLinkageComplete: contractNF.checkPCCPackexpPCCPackLinkageComplete === true,
    appendixCarriesCheckPCCPackexpContract: contractNF.appendixCarriesCheckPCCPackexpContract === true,

    concreteReleaseAppendixEnvelopeDigest: linkage.concreteReleaseAppendixEnvelopeDigest,
    appendixDigest: linkage.appendixDigest,
    acceptRunDigest: linkage.acceptRunDigest,
    pccPackDigest: linkage.pccPackDigest,
    generatedPackageDigest: linkage.generatedPackageDigest,
    materializedPCCPackDigest: linkage.materializedPCCPackDigest,
    checkAcceptRunRecordDigest: linkage.checkAcceptRunRecordDigest,
    replayRecordDigest: linkage.replayRecordDigest,
    finalVerdictRecordDigest: linkage.finalVerdictRecordDigest,
    checkPCCPackexpRecordDigest: linkage.checkPCCPackexpRecordDigest,
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeConcreteFinalAcceptanceReplayFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteFinalAcceptanceReplayFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteFinalAcceptanceReplay0(options);
  const checked = await CheckConcreteFinalAcceptanceReplay0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteFinalAcceptanceReplay0.json');
  const appendixPath = path.join(outDir, 'ConcreteReleaseAppendix0.json');
  const acceptRunPath = path.join(outDir, 'AcceptRun0.json');
  const checkAcceptRunPath = path.join(outDir, 'CheckAcceptRun0.json');
  const replayPath = path.join(outDir, 'ReplayAcceptRun0.json');
  const finalVerdictPath = path.join(outDir, 'EmitFinalVerdict0.json');
  const checkPCCPackexpPath = path.join(outDir, 'CheckPCCPackexp0.json');
  const checkPath = path.join(outDir, 'ConcreteFinalAcceptanceReplay0.check.json');

  const resolved = resolveFinalAcceptanceInputs0(envelope.ConcreteReleaseAppendixEnvelope);

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(appendixPath, envelope.ConcreteReleaseAppendixEnvelope);
  await writeJsonFile0(acceptRunPath, resolved.acceptRun);
  await writeJsonFile0(checkAcceptRunPath, envelope.CheckAcceptRunRecord);
  await writeJsonFile0(replayPath, envelope.ReplayAcceptRunRecord);
  await writeJsonFile0(finalVerdictPath, envelope.FinalVerdictRecord);
  await writeJsonFile0(checkPCCPackexpPath, envelope.CheckPCCPackexpRecord);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      appendixPath,
      acceptRunPath,
      checkAcceptRunPath,
      replayPath,
      finalVerdictPath,
      checkPCCPackexpPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'ConcreteReleaseAppendix0') {
    return {
      kind: 'ConcreteFinalAcceptanceReplay0',
      version: CHECKER_VERSION,
      ConcreteReleaseAppendixEnvelope: input,
      CheckAcceptRunRecord: null,
      ReplayAcceptRunRecord: null,
      FinalVerdictRecord: null,
      CheckPCCPackexpRecord: null,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteFinalAcceptanceReplayConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteFinalAcceptanceReplayConfig0') {
    return validationReject0(['kind'], 'ConcreteFinalAcceptanceReplayConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteFinalAcceptanceReplayConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteReleaseAppendix',
    'checkAcceptRun',
    'checkReplay',
    'checkFinalVerdict',
    'checkPCCPackexp',
    'checkContract',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteFinalAcceptanceReplayConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concreteReleaseAppendixConfig)) {
    return validationReject0(['concreteReleaseAppendixConfig'], 'concreteReleaseAppendixConfig must be an object', {
      actual: typeof config.concreteReleaseAppendixConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalAcceptanceReplayConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteFinalAcceptanceReplay0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteFinalAcceptanceReplay0') {
    return validationReject0(['kind'], 'ConcreteFinalAcceptanceReplay0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteFinalAcceptanceReplay0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ConcreteReleaseAppendixEnvelope)) {
    return validationReject0(['ConcreteReleaseAppendixEnvelope'], 'ConcreteFinalAcceptanceReplay0 must include ConcreteReleaseAppendixEnvelope', {
      actual: typeof envelope.ConcreteReleaseAppendixEnvelope,
    });
  }

  const resolved = resolveFinalAcceptanceInputs0(envelope.ConcreteReleaseAppendixEnvelope);

  if (!isPlainObject(resolved.acceptRun)) {
    return validationReject0(['ConcreteReleaseAppendixEnvelope', 'AcceptRun'], 'ConcreteFinalAcceptanceReplay0 must resolve an AcceptRun0', {
      actual: typeof resolved.acceptRun,
    });
  }

  if (!isPlainObject(resolved.materializedPCCPack)) {
    return validationReject0(['ConcreteReleaseAppendixEnvelope', 'MaterializedPCCPack'], 'ConcreteFinalAcceptanceReplay0 must resolve a materialized PCCPack', {
      actual: typeof resolved.materializedPCCPack,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalAcceptanceReplayShape0NF',
  });
}

function resolveFinalAcceptanceInputs0(concreteReleaseAppendixEnvelope) {
  const gateEnvelope =
    concreteReleaseAppendixEnvelope?.ReleaseAuditConcreteFinalCertificateGateEnvelope ?? null;

  const concretePublicStatusEnvelope =
    gateEnvelope?.ConcreteFinalCertificatePublicStatusEnvelope ?? null;

  const concreteFinalCertificateEnvelope =
    concretePublicStatusEnvelope?.ConcreteFinalCertificateEnvelope ?? null;

  const concreteGeneratedAcceptRunEnvelope =
    concreteFinalCertificateEnvelope?.ConcreteGeneratedAcceptRunEnvelope ?? null;

  const generatedAcceptRunEnvelope =
    concreteGeneratedAcceptRunEnvelope?.GeneratedAcceptRunEnvelope ?? null;

  return {
    gateEnvelope,
    concretePublicStatusEnvelope,
    concreteFinalCertificateEnvelope,
    concreteGeneratedAcceptRunEnvelope,
    generatedAcceptRunEnvelope,
    materializedPCCPack: generatedAcceptRunEnvelope?.MaterializedPCCPack ?? null,
    generatedPackage: generatedAcceptRunEnvelope?.GeneratedPackage ?? null,
    acceptRun: generatedAcceptRunEnvelope?.AcceptRun ?? null,
    appendix: concreteReleaseAppendixEnvelope?.Appendix ?? null,
  };
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

function validateFinalAcceptanceReplayContract0({
  envelope,
  resolved,
  checkAcceptRunRecord,
  replayRecord,
  finalVerdictRecord,
  checkPCCPackexpRecord,
}) {
  const appendix = resolved.appendix ?? {};
  const acceptRun = resolved.acceptRun;
  const generatedPackage = resolved.generatedPackage;

  const acceptNF = recordNF0(checkAcceptRunRecord);
  const replayNF = recordNF0(replayRecord);
  const finalNF = recordNF0(finalVerdictRecord);
  const checkNF = recordNF0(checkPCCPackexpRecord);

  for (const [recordName, record] of [
    ['CheckAcceptRunRecord', checkAcceptRunRecord],
    ['ReplayAcceptRunRecord', replayRecord],
    ['FinalVerdictRecord', finalVerdictRecord],
    ['CheckPCCPackexpRecord', checkPCCPackexpRecord],
  ]) {
    if (!isPlainObject(record) || record.tag !== 'accept') {
      return validationReject0([recordName], `${recordName} must be an accept record`, {
        actual: record?.tag ?? typeof record,
      });
    }
  }

  const requiredAppendixFields = [
    'generatedPCCPackexpCheckPCCPackexp0',
    'generatedPCCPackexpCheckPCCPackexp0Accepted',
    'generatedPCCPackexpCheckPCCPackexp0MaterializedPath',
    'generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll',
    'generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun',
    'generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted',
    'generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion',
    'generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional',
    'generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete',
    'generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete',
    'generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted',
  ];

  for (const field of requiredAppendixFields) {
    if (appendix[field] !== true) {
      return validationReject0(['ConcreteReleaseAppendixEnvelope', 'Appendix', field], `Concrete final acceptance appendix must certify ${field}`, {
        actual: appendix[field],
      });
    }
  }

  if (appendix.generatedPCCPackexpCheckPCCPackexp0Checker !== 'CheckPCCPackexp0') {
    return validationReject0(['ConcreteReleaseAppendixEnvelope', 'Appendix', 'generatedPCCPackexpCheckPCCPackexp0Checker'], 'Concrete final acceptance appendix must certify CheckPCCPackexp0', {
      actual: appendix.generatedPCCPackexpCheckPCCPackexp0Checker,
    });
  }

  if (acceptNF.replayAccepted !== true) {
    return validationReject0(['CheckAcceptRunRecord', 'NF', 'replayAccepted'], 'CheckAcceptRun0 must certify accepted replay', {
      actual: acceptNF.replayAccepted,
    });
  }

  if (acceptNF.verdict !== 'accept') {
    return validationReject0(['CheckAcceptRunRecord', 'NF', 'verdict'], 'CheckAcceptRun0 verdict must be accept', {
      actual: acceptNF.verdict,
    });
  }

  if (finalNF.verdict !== 'accept' || finalNF.publicConclusionEmitted !== true) {
    return validationReject0(['FinalVerdictRecord', 'NF'], 'EmitFinalVerdict0 must emit accepted public conclusion', {
      verdict: finalNF.verdict,
      publicConclusionEmitted: finalNF.publicConclusionEmitted,
    });
  }

  if (!sameFinalPublicConclusion0(finalNF.publicConclusion)) {
    return validationReject0(['FinalVerdictRecord', 'NF', 'publicConclusion'], 'final public conclusion must be the generated package implication', {
      actual: finalNF.publicConclusion,
    });
  }

  if (checkNF.checkPCCPackexp !== true) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF', 'checkPCCPackexp'], 'CheckPCCPackexp0 NF must certify checkPCCPackexp', {
      actual: checkNF.checkPCCPackexp,
    });
  }

  if (checkNF.publicConclusionOnlyAfterAcceptRun !== true || checkNF.publicConclusionEmitted !== false) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF', 'publicConclusionOnlyAfterAcceptRun'], 'CheckPCCPackexp0 must not emit the final public conclusion before accept-run replay', {
      publicConclusionOnlyAfterAcceptRun: checkNF.publicConclusionOnlyAfterAcceptRun,
      publicConclusionEmitted: checkNF.publicConclusionEmitted,
    });
  }

  const canonicalCoreBytes = stableStringify0(acceptRun?.Pgen?.Core ?? null);
  const canonicalPackBytes = stableStringify0(acceptRun?.Pgen ?? null);

  const generatedPackageCanonicalCoreBytesMatch =
    generatedPackage?.outputCoreBytes === canonicalCoreBytes;

  const generatedPackageCanonicalPackBytesMatch =
    generatedPackage?.outputPackBytes === canonicalPackBytes;

  const acceptRunGenCallCoreBytesMatch =
    acceptRun?.GenCall?.outputCoreBytes === generatedPackage?.outputCoreBytes;

  const acceptRunGenCallPackBytesMatch =
    acceptRun?.GenCall?.outputPackBytes === generatedPackage?.outputPackBytes;

  for (const [field, value] of Object.entries({
    generatedPackageCanonicalCoreBytesMatch,
    generatedPackageCanonicalPackBytesMatch,
    acceptRunGenCallCoreBytesMatch,
    acceptRunGenCallPackBytesMatch,
  })) {
    if (value !== true) {
      return validationReject0(['AcceptRun', 'GenCall', field], 'final acceptance replay must compare canonical bytes, not digest-only equality', {
        field,
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteFinalAcceptanceReplayContract0NF',
    generatorIsGeneratePCCPack: acceptRun?.GenCall?.generator === 'GeneratePCCPack',
    checkAcceptRunAccepted: checkAcceptRunRecord.tag === 'accept',
    replayAccepted: replayRecord.tag === 'accept',
    finalVerdictAccepted: finalVerdictRecord.tag === 'accept',
    checkPCCPackexpAccepted: checkPCCPackexpRecord.tag === 'accept',
    verdict: finalNF.verdict,
    publicConclusionEmitted: finalNF.publicConclusionEmitted === true,
    publicConclusionAntecedent: finalNF.publicConclusion?.antecedent ?? null,
    publicConclusionConsequent: finalNF.publicConclusion?.consequent ?? null,
    publicConclusionConditional: finalNF.publicConclusion?.conditional === true,
    generatedPackageCanonicalCoreBytesMatch,
    generatedPackageCanonicalPackBytesMatch,
    acceptRunGenCallCoreBytesMatch,
    acceptRunGenCallPackBytesMatch,
    checkPCCPackexpGeneratedPackageImplication:
      appendix.generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication === true,
    checkPCCPackexpConcreteCoverageComplete:
      appendix.generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete === true,
    checkPCCPackexpPCCPackLinkageComplete:
      appendix.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete === true,
    appendixCarriesCheckPCCPackexpContract: true,
    replayRunId: replayNF.runId ?? acceptRun?.RunID ?? null,
  });
}

function makeLinkage0({
  concreteReleaseAppendixEnvelope,
  checkAcceptRunRecord,
  replayRecord,
  finalVerdictRecord,
  checkPCCPackexpRecord,
}) {
  const resolved = resolveFinalAcceptanceInputs0(concreteReleaseAppendixEnvelope);

  return {
    kind: 'ConcreteFinalAcceptanceReplayLinkage0',
    version: CHECKER_VERSION,
    concreteReleaseAppendixEnvelopeDigest: digestCanonical0(concreteReleaseAppendixEnvelope),
    appendixDigest: digestCanonical0(concreteReleaseAppendixEnvelope?.Appendix ?? null),
    acceptRunDigest: digestCanonical0(resolved.acceptRun ?? null),
    pccPackDigest: digestCanonical0(resolved.acceptRun?.Pgen ?? null),
    generatedPackageDigest: digestCanonical0(resolved.generatedPackage ?? null),
    materializedPCCPackDigest: digestCanonical0(resolved.materializedPCCPack ?? null),
    checkAcceptRunRecordDigest: digestFromRecord0(checkAcceptRunRecord),
    replayRecordDigest: digestFromRecord0(replayRecord),
    finalVerdictRecordDigest: digestFromRecord0(finalVerdictRecord),
    checkPCCPackexpRecordDigest: digestFromRecord0(checkPCCPackexpRecord),
  };
}

function validateLinkage0(envelope, parts) {
  const expected = makeLinkage0(parts);

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteFinalAcceptanceReplay0 Linkage must be an object', {
      actual: typeof envelope.Linkage,
    });
  }

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (field === 'kind' || field === 'version') {
      continue;
    }

    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `ConcreteFinalAcceptanceReplay0 linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteFinalAcceptanceReplayLinkage0NF',
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
    return validationReject0(['ConcreteFinalAcceptanceReplay0'], 'ConcreteFinalAcceptanceReplay0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteFinalAcceptanceReplay0'], 'ConcreteFinalAcceptanceReplay0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalAcceptanceReplayJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function sameFinalPublicConclusion0(value) {
  return (
    isPlainObject(value) &&
    value.antecedent === 'CheckPCCPackexp(GeneratePCCPack())=accept' &&
    value.consequent === 'P = NP' &&
    value.conditional === true
  );
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

function recordNF0(record) {
  return isPlainObject(record)
    ? record.NF ?? record.nf ?? {}
    : {};
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
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
