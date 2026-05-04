
import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  makeConcreteMaterializedPCCPack0,
} from './pcc-pack-concrete-materialized0.mjs';

import {
  CheckPCCPackexp0,
} from './pcc-check-pcc-pack-exp0.mjs';

import {
  CheckMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

const CHECKER_VERSION = 0;

const GENERATED_CORE_FORBIDDEN_KEYS0 = Object.freeze([
  'AcceptRun',
  'AcceptRunEnvelope',
  'MaterializedAcceptRun',
  'MaterializedAcceptRun0',
  'GeneratedAcceptRunEnvelope',
  'FinalCertificateEnvelope',
  'FinalCertificatePublicStatus',
  'FinalCertificatePublicStatusEnvelope',
  'PublicStatus',
  'ReleaseAuditRecord',
]);

export function makeGeneratePCCPackConfig0(overrides = {}) {
  return {
    kind: 'GeneratePCCPackConfig0',
    version: CHECKER_VERSION,
    checkDeterministicGenerator: true,
    checkGeneratedPackageCoreBoundary: true,
    checkMaterializedBoot0: true,
    checkCheckPCCPackexpRecord: true,
    checkPublicClaimBoundary: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    checkPCCPackexpConfig: {},
    ...overrides,
  };
}

export async function GeneratePCCPack0({
  packageOptions = {},
  overrides = {},
} = {}) {
  const generated = await makeConcreteMaterializedPCCPack0(packageOptions);

  if (isPlainObject(overrides) && Object.keys(overrides).length > 0) {
    return {
      ...generated,
      ...overrides,
    };
  }

  return generated;
}

export async function makeGeneratedPCCPackexp0({
  GeneratedPCCPack = null,
  CheckPCCPackexpRecord = null,
  checkPCCPackexpConfig = {},
  overrides = {},
} = {}) {
  const generatedPCCPack = GeneratedPCCPack ?? await GeneratePCCPack0();
  const checkPCCPackexpRecord = CheckPCCPackexpRecord ?? await CheckPCCPackexp0(
    generatedPCCPack,
    checkPCCPackexpConfig ?? {},
  );

  const claimBoundary = makeClaimBoundary0();

  const linkage = {
    kind: 'GeneratedPCCPackexpLinkage0',
    version: CHECKER_VERSION,
    generatedPackageDigest: digestCanonical0(generatedPCCPack),
    checkPCCPackexpRecordDigest: digestFromRecord0(checkPCCPackexpRecord),
    checkPCCPackexpPccPackDigest: checkPCCPackexpRecord?.NF?.pccPackDigest ?? checkPCCPackexpRecord?.nf?.pccPackDigest ?? null,
    checkPCCPackexpMaterializedPCCPackDigest:
      checkPCCPackexpRecord?.NF?.materializedPCCPackDigest ??
      checkPCCPackexpRecord?.nf?.materializedPCCPackDigest ??
      null,
    claimBoundaryDigest: digestCanonical0(claimBoundary),
  };

  return {
    kind: 'GeneratedPCCPackexp0',
    version: CHECKER_VERSION,
    GenCall: {
      kind: 'GeneratePCCPackCall0',
      version: CHECKER_VERSION,
      generator: 'GeneratePCCPack0',
      deterministic: true,
      materializedPath: true,
      syntheticRunAll: false,
      coreOnly: true,
      excludesAcceptRun: true,
    },
    GeneratedPCCPack: generatedPCCPack,
    CheckPCCPackexpRecord: checkPCCPackexpRecord,
    Linkage: linkage,
    PiGeneratedPCCPackexp: {
      kind: 'PiGeneratedPCCPackexp0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'GeneratedPCCPack',
          digest: linkage.generatedPackageDigest,
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

export async function CheckGeneratedPCCPackexp0(
  input,
  config = makeGeneratePCCPackConfig0(),
) {
  const checker = 'CheckGeneratedPCCPackexp0';
  const ledger = [];
  const cfg = makeGeneratePCCPackConfig0(config);
  const envelope = input;
  let deterministicNF = null;
  let coreBoundaryNF = null;
  let boot0NF = null;
  let freshCheckPCCPackexpRecord = null;
  let recordAlignmentNF = null;

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

  if (cfg.checkDeterministicGenerator === true) {
    const deterministic = await validateDeterministicGenerator0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'deterministicGenerator',
      status: deterministic.ok ? 'pass' : 'fail',
      digest: digestCanonical0(deterministic.nf ?? deterministic.witness ?? null),
    });

    if (!deterministic.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.deterministicGenerator`,
        path: deterministic.path,
        witness: deterministic.witness,
        ledger,
      });
    }

    deterministicNF = deterministic.nf;
  }

  if (cfg.checkGeneratedPackageCoreBoundary === true) {
    const coreBoundary = validateGeneratedPackageCoreBoundary0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'generatedPackageCoreBoundary',
      status: coreBoundary.ok ? 'pass' : 'fail',
      digest: digestCanonical0(coreBoundary.nf ?? coreBoundary.witness ?? null),
    });

    if (!coreBoundary.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.coreBoundary`,
        path: coreBoundary.path,
        witness: coreBoundary.witness,
        ledger,
      });
    }

    coreBoundaryNF = coreBoundary.nf;
  }

  if (cfg.checkMaterializedBoot0 === true) {
    const boot0 = await validateGeneratedBoot0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'CheckMaterializedBoot0',
      status: boot0.ok ? 'pass' : 'fail',
      digest: digestCanonical0(boot0.nf ?? boot0.witness ?? null),
    });

    if (!boot0.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.Boot0`,
        path: boot0.path,
        witness: boot0.witness,
        ledger,
      });
    }

    boot0NF = boot0.nf;
  }

  if (cfg.checkCheckPCCPackexpRecord === true) {
    freshCheckPCCPackexpRecord = await CheckPCCPackexp0(
      envelope.GeneratedPCCPack,
      cfg.checkPCCPackexpConfig ?? {},
    );

    const fresh = recordToValidation0(freshCheckPCCPackexpRecord, ['GeneratedPCCPack']);

    ledger.push({
      phase: 'CheckPCCPackexp0',
      status: fresh.ok ? 'pass' : 'fail',
      digest: digestFromRecord0(freshCheckPCCPackexpRecord) ?? digestCanonical0(freshCheckPCCPackexpRecord),
    });

    if (!fresh.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexp`,
        path: fresh.path,
        witness: fresh.witness,
        ledger,
      });
    }

    const alignment = validateMaterializedCheckPCCPackexpRecord0(
      envelope.CheckPCCPackexpRecord,
      freshCheckPCCPackexpRecord,
    );

    ledger.push({
      phase: 'CheckPCCPackexpRecord',
      status: alignment.ok ? 'pass' : 'fail',
      digest: digestCanonical0(alignment.nf ?? alignment.witness ?? null),
    });

    if (!alignment.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexpRecord`,
        path: alignment.path,
        witness: alignment.witness,
        ledger,
      });
    }

    recordAlignmentNF = alignment.nf;
  }

  if (cfg.checkPublicClaimBoundary === true) {
    const claim = validatePublicClaimBoundary0(envelope.CheckPCCPackexpRecord);

    ledger.push({
      phase: 'publicClaimBoundary',
      status: claim.ok ? 'pass' : 'fail',
      digest: digestCanonical0(claim.nf ?? claim.witness ?? null),
    });

    if (!claim.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.publicClaimBoundary`,
        path: claim.path,
        witness: claim.witness,
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

  const checkNF = envelope.CheckPCCPackexpRecord.NF ?? envelope.CheckPCCPackexpRecord.nf;
  const claimBoundary = makeClaimBoundary0();

  const nf = {
    kind: 'GeneratedPCCPackexp0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    generator: 'GeneratePCCPack0',
    genCallDigest: digestCanonical0(envelope.GenCall),
    deterministicGenerator: deterministicNF?.deterministic ?? null,
    generatedPackageMatchesGenerator: deterministicNF?.generatedPackageMatchesGenerator ?? null,
    generatedPackageCoreOnly: coreBoundaryNF?.coreOnly ?? null,
    generatorCoreExcludesAcceptRun: coreBoundaryNF?.excludesAcceptRun ?? null,

    generatedPackageBoot0: boot0NF?.boot0 ?? null,
    boot0Accepted: boot0NF?.boot0Accepted ?? null,
    boot0Kind: boot0NF?.boot0Kind ?? null,
    boot0Digest: boot0NF?.boot0Digest ?? null,
    boot0CheckDigest: boot0NF?.boot0CheckDigest ?? null,
    boot0CanonicalByteDigest: boot0NF?.boot0CanonicalByteDigest ?? null,
    boot0RowCount: boot0NF?.rowCount ?? null,
    boot0KernelRuleCount: boot0NF?.kernelRuleCount ?? null,
    boot0JsonMaterialized: boot0NF?.jsonMaterialized ?? null,
    boot0NoFixtureMarkers: boot0NF?.noFixtureMarkers ?? null,
    boot0BootBatchDigest: boot0NF?.bootBatchDigest ?? null,
    boot0BootAuditDigest: boot0NF?.bootAuditDigest ?? null,
    boot0LinkedToPCCPack: boot0NF?.boot0LinkedToPCCPack ?? null,
    boot0LinkedToCoreDigestMap: boot0NF?.boot0LinkedToCoreDigestMap ?? null,

    generatedPackageKind: envelope.GeneratedPCCPack.kind ?? null,
    generatedPackageDigest: digestCanonical0(envelope.GeneratedPCCPack),

    checkPCCPackexp: true,
    checkPCCPackexpRecordAccepted: envelope.CheckPCCPackexpRecord.tag === 'accept',
    checkPCCPackexpRecordChecker: envelope.CheckPCCPackexpRecord.checker,
    checkPCCPackexpRecordDigest: digestFromRecord0(envelope.CheckPCCPackexpRecord),
    checkPCCPackexpRecordDigestMatchesNF: recordAlignmentNF?.checkPCCPackexpRecordDigestMatchesNF ?? null,
    checkPCCPackexpRecordMatchesFresh: recordAlignmentNF?.checkPCCPackexpRecordMatchesFresh ?? null,

    pccPackDigest: checkNF.pccPackDigest,
    materializedPCCPackDigest: checkNF.materializedPCCPackDigest,
    concreteCoverageDigest: checkNF.concreteCoverageDigest,

    publicConclusionOnlyAfterAcceptRun: checkNF.publicConclusionOnlyAfterAcceptRun === true,
    publicConclusionEmitted: checkNF.publicConclusionEmitted === false ? false : checkNF.publicConclusionEmitted,
    claimBoundary,
    publicConclusion: claimBoundary,

    concretePCCPack: checkNF.concretePCCPack === true,
    concreteKBundle: checkNF.concreteKBundle === true,
    concreteHardCheck: checkNF.concreteHardCheck === true,
    concreteRows: checkNF.concreteRows === true,
    concreteLocalPackages: checkNF.concreteLocalPackages === true,
    concreteGlobalFirewalls: checkNF.concreteGlobalFirewalls === true,
    concreteGlobalProofDAG: checkNF.concreteGlobalProofDAG === true,
    concreteFinalIntegration: checkNF.concreteFinalIntegration === true,

    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeGeneratedPCCPackexpFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeGeneratedPCCPackexpFiles0 requires a non-empty output directory');
  }

  const envelope = await makeGeneratedPCCPackexp0(options);
  const checked = await CheckGeneratedPCCPackexp0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'GeneratedPCCPackexp0.json');
  const generatedPackagePath = path.join(outDir, 'GeneratedPCCPack0.json');
  const checkPCCPackexpRecordPath = path.join(outDir, 'CheckPCCPackexp0.json');
  const checkPath = path.join(outDir, 'GeneratedPCCPackexp0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(generatedPackagePath, envelope.GeneratedPCCPack);
  await writeJsonFile0(checkPCCPackexpRecordPath, envelope.CheckPCCPackexpRecord);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      generatedPackagePath,
      checkPCCPackexpRecordPath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'GeneratePCCPackConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'GeneratePCCPackConfig0') {
    return validationReject0(['kind'], 'GeneratePCCPackConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `GeneratePCCPackConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkDeterministicGenerator',
    'checkGeneratedPackageCoreBoundary',
    'checkMaterializedBoot0',
    'checkCheckPCCPackexpRecord',
    'checkPublicClaimBoundary',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `GeneratePCCPackConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.checkPCCPackexpConfig)) {
    return validationReject0(['checkPCCPackexpConfig'], 'checkPCCPackexpConfig must be an object', {
      actual: typeof config.checkPCCPackexpConfig,
    });
  }

  return validationAccept0({
    kind: 'GeneratePCCPackConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'GeneratedPCCPackexp0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'GeneratedPCCPackexp0') {
    return validationReject0(['kind'], 'GeneratedPCCPackexp0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `GeneratedPCCPackexp0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.GenCall)) {
    return validationReject0(['GenCall'], 'GeneratedPCCPackexp0 must include GenCall', {
      actual: typeof envelope.GenCall,
    });
  }

  if (!isPlainObject(envelope.GeneratedPCCPack)) {
    return validationReject0(['GeneratedPCCPack'], 'GeneratedPCCPackexp0 must include GeneratedPCCPack', {
      actual: typeof envelope.GeneratedPCCPack,
    });
  }

  if (!isPlainObject(envelope.CheckPCCPackexpRecord)) {
    return validationReject0(['CheckPCCPackexpRecord'], 'GeneratedPCCPackexp0 must include CheckPCCPackexpRecord', {
      actual: typeof envelope.CheckPCCPackexpRecord,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackexpShape0NF',
  });
}

async function validateDeterministicGenerator0(actualGeneratedPackage) {
  const generatedA = await GeneratePCCPack0();
  const generatedB = await GeneratePCCPack0();

  if (stableStringify0(generatedA) !== stableStringify0(generatedB)) {
    return validationReject0(['GeneratePCCPack0'], 'GeneratePCCPack0 must be deterministic across repeated generation', {
      firstDigest: digestCanonical0(generatedA),
      secondDigest: digestCanonical0(generatedB),
    });
  }

  if (stableStringify0(actualGeneratedPackage) !== stableStringify0(generatedA)) {
    return validationReject0(['GeneratedPCCPack'], 'GeneratedPCCPack must match GeneratePCCPack0 output by canonical bytes', {
      expectedDigest: digestCanonical0(generatedA),
      actualDigest: digestCanonical0(actualGeneratedPackage),
    });
  }

  return validationAccept0({
    kind: 'GeneratePCCPackDeterminism0NF',
    deterministic: true,
    generatedPackageMatchesGenerator: true,
    generatedPackageDigest: digestCanonical0(actualGeneratedPackage),
  });
}

function validateGeneratedPackageCoreBoundary0(value) {
  const hits = [];

  scanForbiddenCoreKeys0(value, ['GeneratedPCCPack'], hits);

  if (hits.length > 0) {
    return validationReject0(hits[0].path, 'GeneratedPCCPack core must not embed accept-run, public-status, release-audit, or final-certificate payloads', {
      hit: hits[0],
      hitCount: hits.length,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackCoreBoundary0NF',
    coreOnly: true,
    excludesAcceptRun: true,
    forbiddenKeyCount: 0,
  });
}

function scanForbiddenCoreKeys0(value, pathNow, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      scanForbiddenCoreKeys0(value[index], [...pathNow, index], hits);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const [key, child] of Object.entries(value)) {
    const childPath = [...pathNow, key];

    if (GENERATED_CORE_FORBIDDEN_KEYS0.includes(key)) {
      hits.push({
        path: childPath,
        key,
      });
    }

    scanForbiddenCoreKeys0(child, childPath, hits);
  }
}

async function validateGeneratedBoot0(generatedPackage) {
  const materializedPCCPack = generatedPackage?.MaterializedPCCPackEnvelope ?? generatedPackage?.MaterializedPCCPack ?? null;
  const pccPack = materializedPCCPack?.PCCPack ?? generatedPackage?.PCCPack ?? null;
  const boot0 = materializedPCCPack?.MaterializedBoot0 ?? pccPack?.Boot0 ?? null;

  if (!isPlainObject(boot0)) {
    return validationReject0(['GeneratedPCCPack', 'MaterializedPCCPackEnvelope', 'MaterializedBoot0'], 'GeneratedPCCPack must include materialized Boot0', {
      actual: typeof boot0,
    });
  }

  const bootRecord = await CheckMaterializedBoot0(boot0);
  const bootResult = recordToValidation0(bootRecord, ['GeneratedPCCPack', 'MaterializedPCCPackEnvelope', 'MaterializedBoot0']);

  if (!bootResult.ok) {
    return validationReject0(bootResult.path, 'CheckMaterializedBoot0 rejected generated package Boot0', {
      inner: bootResult.witness?.detail?.inner ?? bootResult.witness,
    });
  }

  const bootRecordNF = bootRecord.NF ?? bootRecord.nf;
  const bootObjectDigest = digestCanonical0(boot0);
  const pccPackBootDigest = digestCanonical0(pccPack?.Boot0 ?? null);
  const coreBootDigest = pccPack?.Core?.artefactDigests?.Boot0 ?? null;

  if (!sameDigestHex0(pccPackBootDigest, bootObjectDigest)) {
    return validationReject0(['GeneratedPCCPack', 'PCCPack', 'Boot0'], 'PCCPack Boot0 must match materialized Boot0', {
      expected: bootObjectDigest,
      actual: pccPackBootDigest,
    });
  }

  if (!sameDigestHex0(coreBootDigest, bootObjectDigest)) {
    return validationReject0(['GeneratedPCCPack', 'PCCPack', 'Core', 'artefactDigests', 'Boot0'], 'PCCPack Core artefactDigests.Boot0 must match materialized Boot0', {
      expected: bootObjectDigest,
      actual: coreBootDigest,
    });
  }

  if (bootRecordNF?.jsonMaterializable !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'jsonMaterializable'], 'materialized Boot0 must be JSON materializable', {
      actual: bootRecordNF?.jsonMaterializable ?? null,
    });
  }

  if (bootRecordNF?.noFixtureMarkers !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'noFixtureMarkers'], 'materialized Boot0 must contain no fixture markers', {
      actual: bootRecordNF?.noFixtureMarkers ?? null,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackBoot0Bridge0NF',
    boot0: true,
    boot0Accepted: true,
    boot0Kind: boot0.kind ?? null,
    boot0Digest: bootObjectDigest,
    boot0CheckDigest: bootRecord.Digest ?? bootRecord.digest,
    boot0CanonicalByteDigest: bootRecordNF.canonicalByteDigest ?? null,
    rowCount: bootRecordNF.rowCount ?? null,
    kernelRuleCount: bootRecordNF.kernelRuleCount ?? null,
    jsonMaterialized: bootRecordNF.jsonMaterializable === true,
    noFixtureMarkers: bootRecordNF.noFixtureMarkers === true,
    bootBatchDigest: bootRecordNF.bootBatchDigest ?? null,
    bootAuditDigest: bootRecordNF.bootAuditDigest ?? null,
    boot0LinkedToPCCPack: true,
    boot0LinkedToCoreDigestMap: true,
  });
}

function validateMaterializedCheckPCCPackexpRecord0(actual, expected) {
  if (!isPlainObject(actual)) {
    return validationReject0(['CheckPCCPackexpRecord'], 'CheckPCCPackexpRecord must be an object', {
      actual: typeof actual,
    });
  }

  if (actual.tag !== 'accept') {
    return validationReject0(['CheckPCCPackexpRecord', 'tag'], 'CheckPCCPackexpRecord must be accepted', {
      actual: actual.tag,
    });
  }

  if (actual.checker !== 'CheckPCCPackexp0') {
    return validationReject0(['CheckPCCPackexpRecord', 'checker'], 'CheckPCCPackexpRecord checker mismatch', {
      actual: actual.checker,
    });
  }

  const actualNF = actual.NF ?? actual.nf;
  const expectedNF = expected?.NF ?? expected?.nf;

  if (!isPlainObject(actualNF)) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF'], 'CheckPCCPackexpRecord must expose NF', {
      actual: typeof actualNF,
    });
  }

  if (!isPlainObject(expectedNF)) {
    return validationReject0(['CheckPCCPackexpRecord'], 'fresh CheckPCCPackexp0 record must expose NF', {
      actual: typeof expectedNF,
    });
  }

  const actualDigest = digestFromRecord0(actual);
  const actualNFDigest = digestCanonical0(actualNF);

  if (!sameDigestHex0(actualDigest, actualNFDigest)) {
    return validationReject0(['CheckPCCPackexpRecord', 'Digest'], 'CheckPCCPackexpRecord Digest must match its NF', {
      expected: actualNFDigest,
      actual: actualDigest,
    });
  }

  if (stableStringify0(actualNF) !== stableStringify0(expectedNF)) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF'], 'CheckPCCPackexpRecord must match fresh CheckPCCPackexp0 replay', {
      expectedDigest: digestCanonical0(expectedNF),
      actualDigest: digestCanonical0(actualNF),
    });
  }

  if (!sameDigestHex0(actualDigest, digestFromRecord0(expected))) {
    return validationReject0(['CheckPCCPackexpRecord', 'Digest'], 'CheckPCCPackexpRecord digest must match fresh CheckPCCPackexp0 replay digest', {
      expected: digestFromRecord0(expected),
      actual: actualDigest,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackCheckPCCPackexpRecord0NF',
    checkPCCPackexpRecordDigest: actualDigest,
    checkPCCPackexpRecordDigestMatchesNF: true,
    checkPCCPackexpRecordMatchesFresh: true,
  });
}

function validatePublicClaimBoundary0(record) {
  const nf = record?.NF ?? record?.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF'], 'CheckPCCPackexpRecord must expose NF for public claim boundary', {
      actual: typeof nf,
    });
  }

  if (nf.publicConclusionOnlyAfterAcceptRun !== true) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF', 'publicConclusionOnlyAfterAcceptRun'], 'CheckPCCPackexp must gate public conclusion by accepted replay', {
      actual: nf.publicConclusionOnlyAfterAcceptRun,
    });
  }

  if (nf.publicConclusionEmitted !== false) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF', 'publicConclusionEmitted'], 'CheckPCCPackexp package check must not emit public theorem conclusion', {
      actual: nf.publicConclusionEmitted,
    });
  }

  if (!samePublicConclusion0(nf.publicConclusion, makeClaimBoundary0())) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF', 'publicConclusion'], 'CheckPCCPackexp public claim boundary mismatch', {
      actual: nf.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackPublicClaimBoundary0NF',
    claimBoundary: makeClaimBoundary0(),
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['GeneratedPCCPackexp0'], 'GeneratedPCCPackexp0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['GeneratedPCCPackexp0'], 'GeneratedPCCPackexp0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackexpJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope) {
  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'GeneratedPCCPackexp0 must include Linkage', {
      actual: typeof envelope.Linkage,
    });
  }

  const checkNF = envelope.CheckPCCPackexpRecord.NF ?? envelope.CheckPCCPackexpRecord.nf;

  const expected = {
    generatedPackageDigest: digestCanonical0(envelope.GeneratedPCCPack),
    checkPCCPackexpRecordDigest: digestFromRecord0(envelope.CheckPCCPackexpRecord),
    checkPCCPackexpPccPackDigest: checkNF?.pccPackDigest ?? null,
    checkPCCPackexpMaterializedPCCPackDigest: checkNF?.materializedPCCPackDigest ?? null,
    claimBoundaryDigest: digestCanonical0(makeClaimBoundary0()),
  };

  for (const [field, digest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], digest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: digest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackexpLinkage0NF',
    present: true,
    ...expected,
  });
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function makeClaimBoundary0() {
  return {
    antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    consequent: 'P = NP',
    conditional: true,
  };
}

function digestFromRecord0(record) {
  if (!isPlainObject(record)) {
    return null;
  }

  return record.Digest ?? record.digest ?? null;
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

function samePublicConclusion0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.antecedent === b.antecedent &&
    a.consequent === b.consequent &&
    a.conditional === b.conditional
  );
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
