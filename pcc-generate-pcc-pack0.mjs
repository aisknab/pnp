
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

import {
  CheckBootBatch0,
} from './pcc-boot0.mjs';

const CHECKER_VERSION = 0;

const GENERATED_PCCPACK_BOOT_B0_REQUIRED_FAMILIES0 = Object.freeze([
  'BIface',
  'BSched',
  'BNF',
  'BTruthEval',
  'BRel',
  'BCharge',
  'BObl',
  'BArith',
  'BMode',
  'BRoute',
  'BHash',
  'BImport',
]);

const GENERATED_PCCPACK_KERNEL_SEED_REQUIRED_RULES0 = Object.freeze([
  'Eq',
  'Subst',
  'Record',
  'DAGInd',
  'LedgerInd',
  'OblTopoInd',
  'TraceInd',
  'FiniteExhaust',
  'DPInd',
  'Hall',
  'RankInd',
  'MinCounterexample',
  'IntArith',
  'Transport',
  'TruthVec',
  'FiniteRel',
]);

const GENERATED_PCCPACK_KERNEL_SEED_REQUIRED_PROOF_NODE_KINDS0 = Object.freeze([
  'PrimitiveRule',
  'SigmaInstance',
  'ReflectionInstance',
  'RowProof',
  'PackageTheorem',
]);

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
    checkKernelSeed0: true,
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
  let kernelSeedNF = null;
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

  if (cfg.checkKernelSeed0 === true) {
    const kernelSeed = validateGeneratedKernelSeed0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'KernelSeed0',
      status: kernelSeed.ok ? 'pass' : 'fail',
      digest: digestCanonical0(kernelSeed.nf ?? kernelSeed.witness ?? null),
    });

    if (!kernelSeed.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.KernelSeed0`,
        path: kernelSeed.path,
        witness: kernelSeed.witness,
        ledger,
      });
    }

    kernelSeedNF = kernelSeed.nf;
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
    boot0B0Accepted: boot0NF?.boot0B0Accepted ?? null,
    boot0B0Digest: boot0NF?.boot0B0Digest ?? null,
    boot0B0CoverageDigest: boot0NF?.boot0B0CoverageDigest ?? null,
    boot0B0FamilyCount: boot0NF?.boot0B0FamilyCount ?? null,
    boot0B0RequiredFamilyCount: boot0NF?.boot0B0RequiredFamilyCount ?? null,
    boot0B0Families: boot0NF?.boot0B0Families ?? null,
    boot0B0AllRequiredFamiliesPresent: boot0NF?.boot0B0AllRequiredFamiliesPresent ?? null,
    boot0B0CoversIface: boot0NF?.boot0B0CoversIface ?? null,
    boot0B0CoversSched: boot0NF?.boot0B0CoversSched ?? null,
    boot0B0CoversNF: boot0NF?.boot0B0CoversNF ?? null,
    boot0B0CoversTruthEval: boot0NF?.boot0B0CoversTruthEval ?? null,
    boot0B0CoversRel: boot0NF?.boot0B0CoversRel ?? null,
    boot0B0CoversCharge: boot0NF?.boot0B0CoversCharge ?? null,
    boot0B0CoversObl: boot0NF?.boot0B0CoversObl ?? null,
    boot0B0CoversArith: boot0NF?.boot0B0CoversArith ?? null,
    boot0B0CoversMode: boot0NF?.boot0B0CoversMode ?? null,
    boot0B0CoversRoute: boot0NF?.boot0B0CoversRoute ?? null,
    boot0B0CoversHash: boot0NF?.boot0B0CoversHash ?? null,
    boot0B0CoversImport: boot0NF?.boot0B0CoversImport ?? null,

    boot0LinkedToPCCPack: boot0NF?.boot0LinkedToPCCPack ?? null,
    boot0LinkedToCoreDigestMap: boot0NF?.boot0LinkedToCoreDigestMap ?? null,

    generatedPackageKernelSeed0: kernelSeedNF?.kernelSeed0 ?? null,
    kernelSeed0Accepted: kernelSeedNF?.kernelSeed0Accepted ?? null,
    kernelSeed0Kind: kernelSeedNF?.kernelSeed0Kind ?? null,
    kernelSeed0Digest: kernelSeedNF?.kernelSeed0Digest ?? null,
    kernelSeed0RuleCount: kernelSeedNF?.kernelSeed0RuleCount ?? null,
    kernelSeed0RequiredRuleCount: kernelSeedNF?.kernelSeed0RequiredRuleCount ?? null,
    kernelSeed0Rules: kernelSeedNF?.kernelSeed0Rules ?? null,
    kernelSeed0AllRequiredRulesPresent: kernelSeedNF?.kernelSeed0AllRequiredRulesPresent ?? null,
    kernelSeed0HasEq: kernelSeedNF?.kernelSeed0HasEq ?? null,
    kernelSeed0HasSubst: kernelSeedNF?.kernelSeed0HasSubst ?? null,
    kernelSeed0HasRecord: kernelSeedNF?.kernelSeed0HasRecord ?? null,
    kernelSeed0HasDAGInd: kernelSeedNF?.kernelSeed0HasDAGInd ?? null,
    kernelSeed0HasLedgerInd: kernelSeedNF?.kernelSeed0HasLedgerInd ?? null,
    kernelSeed0HasOblTopoInd: kernelSeedNF?.kernelSeed0HasOblTopoInd ?? null,
    kernelSeed0HasTraceInd: kernelSeedNF?.kernelSeed0HasTraceInd ?? null,
    kernelSeed0HasFiniteExhaust: kernelSeedNF?.kernelSeed0HasFiniteExhaust ?? null,
    kernelSeed0HasDPInd: kernelSeedNF?.kernelSeed0HasDPInd ?? null,
    kernelSeed0HasHall: kernelSeedNF?.kernelSeed0HasHall ?? null,
    kernelSeed0HasRankInd: kernelSeedNF?.kernelSeed0HasRankInd ?? null,
    kernelSeed0HasMinCounterexample: kernelSeedNF?.kernelSeed0HasMinCounterexample ?? null,
    kernelSeed0HasIntArith: kernelSeedNF?.kernelSeed0HasIntArith ?? null,
    kernelSeed0HasTransport: kernelSeedNF?.kernelSeed0HasTransport ?? null,
    kernelSeed0HasTruthVec: kernelSeedNF?.kernelSeed0HasTruthVec ?? null,
    kernelSeed0HasFiniteRel: kernelSeedNF?.kernelSeed0HasFiniteRel ?? null,
    kernelSeed0ProofNodeKindCount: kernelSeedNF?.kernelSeed0ProofNodeKindCount ?? null,
    kernelSeed0ProofNodeKinds: kernelSeedNF?.kernelSeed0ProofNodeKinds ?? null,
    kernelSeed0AllRequiredProofNodeKindsPresent:
      kernelSeedNF?.kernelSeed0AllRequiredProofNodeKindsPresent ?? null,
    kernelSeed0ProofRefsRejectOpaque: kernelSeedNF?.kernelSeed0ProofRefsRejectOpaque ?? null,
    kernelSeed0ProofRefsTypedAcyclic: kernelSeedNF?.kernelSeed0ProofRefsTypedAcyclic ?? null,
    kernelSeed0ProofRefsHashIndependent: kernelSeedNF?.kernelSeed0ProofRefsHashIndependent ?? null,
    kernelSeed0PiBootDigestMatches: kernelSeedNF?.kernelSeed0PiBootDigestMatches ?? null,

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
    'checkKernelSeed0',
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

function validateGeneratedKernelSeed0(generatedPackage) {
  const materializedPCCPack = generatedPackage?.MaterializedPCCPackEnvelope ?? generatedPackage?.MaterializedPCCPack ?? null;
  const boot0 = materializedPCCPack?.MaterializedBoot0 ?? materializedPCCPack?.PCCPack?.Boot0 ?? null;
  const kernelSeed0 = boot0?.KernelSeed0 ?? null;

  if (!isPlainObject(kernelSeed0)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0'], 'GeneratedPCCPack must include concrete KernelSeed0', {
      actual: typeof kernelSeed0,
    });
  }

  if (kernelSeed0.kind !== undefined && kernelSeed0.kind !== 'KernelSeed0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'kind'], 'KernelSeed0 kind mismatch', {
      actual: kernelSeed0.kind,
    });
  }

  if (!Array.isArray(kernelSeed0.rules)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'rules'], 'KernelSeed0 rules must be an array', {
      actual: typeof kernelSeed0.rules,
    });
  }

  const duplicateRule = firstDuplicate0(kernelSeed0.rules);

  if (duplicateRule !== null) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'rules'], 'KernelSeed0 rules must be unique', {
      duplicateRule,
    });
  }

  const missingRules = GENERATED_PCCPACK_KERNEL_SEED_REQUIRED_RULES0.filter((rule) => !kernelSeed0.rules.includes(rule));

  if (missingRules.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'rules'], 'KernelSeed0 is missing required primitive rules', {
      missingRules,
      actual: kernelSeed0.rules,
    });
  }

  if (!Array.isArray(kernelSeed0.proofNodeKinds)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'proofNodeKinds'], 'KernelSeed0 proofNodeKinds must be an array', {
      actual: typeof kernelSeed0.proofNodeKinds,
    });
  }

  const missingProofNodeKinds = GENERATED_PCCPACK_KERNEL_SEED_REQUIRED_PROOF_NODE_KINDS0.filter((kind) => (
    !kernelSeed0.proofNodeKinds.includes(kind)
  ));

  if (missingProofNodeKinds.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'proofNodeKinds'], 'KernelSeed0 is missing required proof node kinds', {
      missingProofNodeKinds,
      actual: kernelSeed0.proofNodeKinds,
    });
  }

  const proofReferencePolicy = kernelSeed0.proofReferencePolicy ?? {};

  if (proofReferencePolicy.rejectsOpaqueProofBlobs !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'proofReferencePolicy', 'rejectsOpaqueProofBlobs'], 'KernelSeed0 must reject opaque proof blobs', {
      actual: proofReferencePolicy.rejectsOpaqueProofBlobs,
    });
  }

  if (proofReferencePolicy.requiresTypedAcyclicRefs !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'proofReferencePolicy', 'requiresTypedAcyclicRefs'], 'KernelSeed0 must require typed acyclic proof refs', {
      actual: proofReferencePolicy.requiresTypedAcyclicRefs,
    });
  }

  if (proofReferencePolicy.hashIndependent !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'proofReferencePolicy', 'hashIndependent'], 'KernelSeed0 proof references must be hash independent', {
      actual: proofReferencePolicy.hashIndependent,
    });
  }

  const kernelSeedDigest = digestCanonical0(kernelSeed0);
  const piBootRefs = Array.isArray(boot0?.PiBoot?.refs) ? boot0.PiBoot.refs : [];
  const piBootKernelSeedRef = piBootRefs.find((ref) => (
    ref?.label === 'KernelSeed0' ||
    ref?.target === 'KernelSeed0'
  ));

  if (!isPlainObject(piBootKernelSeedRef)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs'], 'PiBoot must reference KernelSeed0', {
      refs: piBootRefs,
    });
  }

  if (!sameDigestHex0(piBootKernelSeedRef.digest, kernelSeedDigest)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs', 'KernelSeed0'], 'PiBoot KernelSeed0 digest must match concrete KernelSeed0', {
      expected: kernelSeedDigest,
      actual: piBootKernelSeedRef.digest,
    });
  }

  const ruleFlags = Object.fromEntries(
    GENERATED_PCCPACK_KERNEL_SEED_REQUIRED_RULES0.map((rule) => [
      kernelSeedRuleFlagName0(rule),
      kernelSeed0.rules.includes(rule),
    ]),
  );

  return validationAccept0({
    kind: 'GeneratedPCCPackKernelSeed0NF',
    kernelSeed0: true,
    kernelSeed0Accepted: true,
    kernelSeed0Kind: kernelSeed0.kind ?? 'KernelSeed0',
    kernelSeed0Digest: kernelSeedDigest,
    kernelSeed0RuleCount: kernelSeed0.rules.length,
    kernelSeed0RequiredRuleCount: GENERATED_PCCPACK_KERNEL_SEED_REQUIRED_RULES0.length,
    kernelSeed0Rules: kernelSeed0.rules,
    kernelSeed0AllRequiredRulesPresent: missingRules.length === 0,
    ...ruleFlags,
    kernelSeed0ProofNodeKindCount: kernelSeed0.proofNodeKinds.length,
    kernelSeed0ProofNodeKinds: kernelSeed0.proofNodeKinds,
    kernelSeed0AllRequiredProofNodeKindsPresent: missingProofNodeKinds.length === 0,
    kernelSeed0ProofRefsRejectOpaque: proofReferencePolicy.rejectsOpaqueProofBlobs === true,
    kernelSeed0ProofRefsTypedAcyclic: proofReferencePolicy.requiresTypedAcyclicRefs === true,
    kernelSeed0ProofRefsHashIndependent: proofReferencePolicy.hashIndependent === true,
    kernelSeed0PiBootDigestMatches: true,
  });
}

function kernelSeedRuleFlagName0(rule) {
  const map = {
    Eq: 'kernelSeed0HasEq',
    Subst: 'kernelSeed0HasSubst',
    Record: 'kernelSeed0HasRecord',
    DAGInd: 'kernelSeed0HasDAGInd',
    LedgerInd: 'kernelSeed0HasLedgerInd',
    OblTopoInd: 'kernelSeed0HasOblTopoInd',
    TraceInd: 'kernelSeed0HasTraceInd',
    FiniteExhaust: 'kernelSeed0HasFiniteExhaust',
    DPInd: 'kernelSeed0HasDPInd',
    Hall: 'kernelSeed0HasHall',
    RankInd: 'kernelSeed0HasRankInd',
    MinCounterexample: 'kernelSeed0HasMinCounterexample',
    IntArith: 'kernelSeed0HasIntArith',
    Transport: 'kernelSeed0HasTransport',
    TruthVec: 'kernelSeed0HasTruthVec',
    FiniteRel: 'kernelSeed0HasFiniteRel',
  };

  return map[rule] ?? `kernelSeed0Has${rule}`;
}

function firstDuplicate0(values) {
  const seen = new Set();

  for (const value of values) {
    if (seen.has(value)) {
      return value;
    }

    seen.add(value);
  }

  return null;
}

async function validateGeneratedBootBatch0(batch) {
  const record = await CheckBootBatch0(batch);
  const result = recordToValidation0(record, ['GeneratedPCCPack', 'Boot0', 'B0']);

  if (!result.ok) {
    return validationReject0(result.path, 'CheckBootBatch0 rejected generated package B0', {
      inner: result.witness?.detail?.inner ?? result.witness,
    });
  }

  const nf = record.NF ?? record.nf;
  const coverage = nf?.coverage ?? null;
  const families = Array.isArray(coverage?.families)
    ? coverage.families.map((entry) => entry.family)
    : [];

  const missing = GENERATED_PCCPACK_BOOT_B0_REQUIRED_FAMILIES0.filter((family) => !families.includes(family));

  if (missing.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'B0', 'coverage'], 'Generated package B0 is missing required bootstrap row families', {
      missing,
      families,
    });
  }

  const flags = Object.fromEntries(
    GENERATED_PCCPACK_BOOT_B0_REQUIRED_FAMILIES0.map((family) => [
      boot0FamilyFlagName0(family),
      families.includes(family),
    ]),
  );

  return validationAccept0({
    kind: 'GeneratedPCCPackB0Coverage0NF',
    boot0B0Accepted: true,
    boot0B0Digest: record.Digest ?? record.digest,
    boot0B0CoverageDigest: digestCanonical0(coverage),
    boot0B0FamilyCount: families.length,
    boot0B0RequiredFamilyCount: GENERATED_PCCPACK_BOOT_B0_REQUIRED_FAMILIES0.length,
    boot0B0Families: families,
    boot0B0AllRequiredFamiliesPresent: missing.length === 0,
    ...flags,
  });
}

function boot0FamilyFlagName0(family) {
  const map = {
    BIface: 'boot0B0CoversIface',
    BSched: 'boot0B0CoversSched',
    BNF: 'boot0B0CoversNF',
    BTruthEval: 'boot0B0CoversTruthEval',
    BRel: 'boot0B0CoversRel',
    BCharge: 'boot0B0CoversCharge',
    BObl: 'boot0B0CoversObl',
    BArith: 'boot0B0CoversArith',
    BMode: 'boot0B0CoversMode',
    BRoute: 'boot0B0CoversRoute',
    BHash: 'boot0B0CoversHash',
    BImport: 'boot0B0CoversImport',
  };

  return map[family] ?? `boot0B0Covers${family}`;
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

  const bootBatch = await validateGeneratedBootBatch0(boot0.B0);

  if (!bootBatch.ok) {
    return bootBatch;
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
    ...bootBatch.nf,
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
