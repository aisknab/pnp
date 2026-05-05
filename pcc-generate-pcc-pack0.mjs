
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

const GENERATED_PCCPACK_IFACE_REQUIRED_FORBIDDEN_SYMBOLS0 = Object.freeze([
  'µ',
  'µ*',
  'µ#',
  'Can',
  'argmin',
  'maxG',
  'minimumEquivalent',
  'optimalCircuit',
  'exactMinSearch',
  'canonicalMinimizer',
  'maximizeGain',
]);

const GENERATED_PCCPACK_IFACE_PUBLIC_CONSTRUCTORS0 = Object.freeze([
  'Gain',
  'Minimum',
  'ZeroSlack',
  'NoBudget',
  'NoHereditary',
  'SelectorSilent',
  'Faithful',
  'Token',
]);

const GENERATED_PCCPACK_IFACE_CRITICAL_KINDS0 = Object.freeze([
  'CritC',
  'Q',
  'E',
  'L',
  'X1',
  'X2',
  'X3',
  'X4',
]);

const GENERATED_PCCPACK_IFACE_ROUTE_TOKENS0 = Object.freeze([
  'UnaryWindow',
  'BCLeak',
  'HNShape',
  'BudgetShape',
  'SelectorSeed',
  'ExactRoute',
  'StrictDescent',
]);

const GENERATED_PCCPACK_SCHED_REQUIRED_CORE0 = Object.freeze({
  B0: 64,
  K0: 512,
  R0: 64,
  H0: 128,
  O0: 64,
  Rel0: 16,
});

const GENERATED_PCCPACK_SCHED_REQUIRED_SCALE_FACTORS0 = Object.freeze({
  FT: 1,
  X: 2,
  Splice: 2,
  BC: 4,
  UN: 4,
  HN: 8,
  BUD: 8,
  RW: 8,
  BN: 8,
  PkgC: 16,
  Packet: 16,
  R: 16,
});

const GENERATED_PCCPACK_BYTELANG_REQUIRED_TAGS0 = Object.freeze({
  Boot0: 0x0001,
  BootBatch0: 0x0002,
  Row0: 0x0003,
  Digest0: 0x0004,
  IfaceDict0: 0x0005,
  Sched0: 0x0006,
  KernelSeed0: 0x0007,
  BootAudit0: 0x0008,
  PiBoot0: 0x0009,
  ProofRef0: 0x000a,
  BoundsRef0: 0x000b,
  TransportProof0: 0x000c,
});

const GENERATED_PCCPACK_BYTELANG_REQUIRED_SORTS0 = Object.freeze([
  'Unit',
  'Name',
  'Record',
  'Row',
  'Digest',
  'Route',
  'ProofRef',
  'BoundsRef',
]);

const GENERATED_PCCPACK_BYTELANG_REQUIRED_CONSTRUCTORS0 = Object.freeze([
  'accept',
  'reject',
  'row',
  'digest',
  'proofRef',
  'boundsRef',
  'transport',
]);

const GENERATED_PCCPACK_BYTELANG_REQUIRED_RECORD_ARITIES0 = Object.freeze({
  Boot0: 9,
  BootBatch0: 3,
  Row0: 12,
  Digest0: 4,
  IfaceDict0: 4,
  Sched0: 3,
  KernelSeed0: 3,
  BootAudit0: 3,
  PiBoot0: 4,
});

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
    checkCodecDigest0: true,
    checkIfaceSched0: true,
    checkByteLang0: true,
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
  let codecDigestNF = null;
  let ifaceSchedNF = null;
  let byteLangNF = null;
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

  if (cfg.checkCodecDigest0 === true) {
    const codecDigest = validateGeneratedCodecDigest0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'CodecDigest0',
      status: codecDigest.ok ? 'pass' : 'fail',
      digest: digestCanonical0(codecDigest.nf ?? codecDigest.witness ?? null),
    });

    if (!codecDigest.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CodecDigest0`,
        path: codecDigest.path,
        witness: codecDigest.witness,
        ledger,
      });
    }

    codecDigestNF = codecDigest.nf;
  }

  if (cfg.checkIfaceSched0 === true) {
    const ifaceSched = validateGeneratedIfaceSched0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'IfaceSched0',
      status: ifaceSched.ok ? 'pass' : 'fail',
      digest: digestCanonical0(ifaceSched.nf ?? ifaceSched.witness ?? null),
    });

    if (!ifaceSched.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.IfaceSched0`,
        path: ifaceSched.path,
        witness: ifaceSched.witness,
        ledger,
      });
    }

    ifaceSchedNF = ifaceSched.nf;
  }

  if (cfg.checkByteLang0 === true) {
    const byteLang = validateGeneratedByteLang0(envelope.GeneratedPCCPack);

    ledger.push({
      phase: 'ByteLang0',
      status: byteLang.ok ? 'pass' : 'fail',
      digest: digestCanonical0(byteLang.nf ?? byteLang.witness ?? null),
    });

    if (!byteLang.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ByteLang0`,
        path: byteLang.path,
        witness: byteLang.witness,
        ledger,
      });
    }

    byteLangNF = byteLang.nf;
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

    generatedPackageCodec0: codecDigestNF?.codec0 ?? null,
    codec0Accepted: codecDigestNF?.codec0Accepted ?? null,
    codec0Kind: codecDigestNF?.codec0Kind ?? null,
    codec0Digest: codecDigestNF?.codec0Digest ?? null,
    codec0Canonical: codecDigestNF?.codec0Canonical ?? null,
    codec0NaturalEncoding: codecDigestNF?.codec0NaturalEncoding ?? null,
    codec0IntegerEncoding: codecDigestNF?.codec0IntegerEncoding ?? null,
    codec0StringEncoding: codecDigestNF?.codec0StringEncoding ?? null,
    codec0TopLevelConsumesAllBytes: codecDigestNF?.codec0TopLevelConsumesAllBytes ?? null,
    codec0NormalFormSerialization: codecDigestNF?.codec0NormalFormSerialization ?? null,
    codec0PiBootDigestMatches: codecDigestNF?.codec0PiBootDigestMatches ?? null,

    generatedPackageDigest0: codecDigestNF?.digest0 ?? null,
    digest0Accepted: codecDigestNF?.digest0Accepted ?? null,
    digest0Kind: codecDigestNF?.digest0Kind ?? null,
    digest0Digest: codecDigestNF?.digest0Digest ?? null,
    digest0Alg: codecDigestNF?.digest0Alg ?? null,
    digest0Bytes: codecDigestNF?.digest0Bytes ?? null,
    digest0EqualityNotObjectEquality: codecDigestNF?.digest0EqualityNotObjectEquality ?? null,
    digest0FullKeyComparisonAfterHashLookup:
      codecDigestNF?.digest0FullKeyComparisonAfterHashLookup ?? null,
    digest0PiBootDigestMatches: codecDigestNF?.digest0PiBootDigestMatches ?? null,

    generatedPackageIfaceDict0: ifaceSchedNF?.ifaceDict0 ?? null,
    ifaceDict0Accepted: ifaceSchedNF?.ifaceDict0Accepted ?? null,
    ifaceDict0Kind: ifaceSchedNF?.ifaceDict0Kind ?? null,
    ifaceDict0Digest: ifaceSchedNF?.ifaceDict0Digest ?? null,
    ifaceDict0ForbiddenSymbolCount: ifaceSchedNF?.ifaceDict0ForbiddenSymbolCount ?? null,
    ifaceDict0RequiredForbiddenSymbolsPresent:
      ifaceSchedNF?.ifaceDict0RequiredForbiddenSymbolsPresent ?? null,
    ifaceDict0NoExecutableMinSymbols: ifaceSchedNF?.ifaceDict0NoExecutableMinSymbols ?? null,
    ifaceDict0PublicConstructorsPresent: ifaceSchedNF?.ifaceDict0PublicConstructorsPresent ?? null,
    ifaceDict0CriticalKindsPresent: ifaceSchedNF?.ifaceDict0CriticalKindsPresent ?? null,
    ifaceDict0RouteTokensPresent: ifaceSchedNF?.ifaceDict0RouteTokensPresent ?? null,
    ifaceDict0PiBootDigestMatches: ifaceSchedNF?.ifaceDict0PiBootDigestMatches ?? null,

    generatedPackageSched0: ifaceSchedNF?.sched0 ?? null,
    sched0Accepted: ifaceSchedNF?.sched0Accepted ?? null,
    sched0Kind: ifaceSchedNF?.sched0Kind ?? null,
    sched0Digest: ifaceSchedNF?.sched0Digest ?? null,
    sched0CoreMatchesExpected: ifaceSchedNF?.sched0CoreMatchesExpected ?? null,
    sched0CoreB0: ifaceSchedNF?.sched0CoreB0 ?? null,
    sched0CoreK0: ifaceSchedNF?.sched0CoreK0 ?? null,
    sched0CoreR0: ifaceSchedNF?.sched0CoreR0 ?? null,
    sched0CoreH0: ifaceSchedNF?.sched0CoreH0 ?? null,
    sched0CoreO0: ifaceSchedNF?.sched0CoreO0 ?? null,
    sched0CoreRel0: ifaceSchedNF?.sched0CoreRel0 ?? null,
    sched0ScaleFactorsPresent: ifaceSchedNF?.sched0ScaleFactorsPresent ?? null,
    sched0SelectorBoundsPresent: ifaceSchedNF?.sched0SelectorBoundsPresent ?? null,
    sched0SelectorBoundBH: ifaceSchedNF?.sched0SelectorBoundBH ?? null,
    sched0SelectorBoundBTheta: ifaceSchedNF?.sched0SelectorBoundBTheta ?? null,
    sched0PolynomialExponent: ifaceSchedNF?.sched0PolynomialExponent ?? null,
    sched0PiBootDigestMatches: ifaceSchedNF?.sched0PiBootDigestMatches ?? null,

    generatedPackageByteLang0: byteLangNF?.byteLang0 ?? null,
    byteLang0Accepted: byteLangNF?.byteLang0Accepted ?? null,
    byteLang0Kind: byteLangNF?.byteLang0Kind ?? null,
    byteLang0Digest: byteLangNF?.byteLang0Digest ?? null,
    byteLang0TagCount: byteLangNF?.byteLang0TagCount ?? null,
    byteLang0TagsUnique: byteLangNF?.byteLang0TagsUnique ?? null,
    byteLang0RequiredTagsPresent: byteLangNF?.byteLang0RequiredTagsPresent ?? null,
    byteLang0SortCount: byteLangNF?.byteLang0SortCount ?? null,
    byteLang0RequiredSortsPresent: byteLangNF?.byteLang0RequiredSortsPresent ?? null,
    byteLang0ConstructorCount: byteLangNF?.byteLang0ConstructorCount ?? null,
    byteLang0RequiredConstructorsPresent: byteLangNF?.byteLang0RequiredConstructorsPresent ?? null,
    byteLang0RecordCount: byteLangNF?.byteLang0RecordCount ?? null,
    byteLang0RequiredRecordAritiesPresent: byteLangNF?.byteLang0RequiredRecordAritiesPresent ?? null,
    byteLang0PiBootDigestMatches: byteLangNF?.byteLang0PiBootDigestMatches ?? null,

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
    'checkCodecDigest0',
    'checkIfaceSched0',
    'checkByteLang0',
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

function validateGeneratedByteLang0(generatedPackage) {
  const materializedPCCPack = generatedPackage?.MaterializedPCCPackEnvelope ?? generatedPackage?.MaterializedPCCPack ?? null;
  const boot0 = materializedPCCPack?.MaterializedBoot0 ?? materializedPCCPack?.PCCPack?.Boot0 ?? null;
  const byteLang0 = boot0?.ByteLang0 ?? null;

  if (!isPlainObject(byteLang0)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0'], 'GeneratedPCCPack must include concrete ByteLang0', {
      actual: typeof byteLang0,
    });
  }

  if (byteLang0.kind !== undefined && byteLang0.kind !== 'ByteLang0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'kind'], 'ByteLang0 kind mismatch', {
      actual: byteLang0.kind,
    });
  }

  if (!isPlainObject(byteLang0.tags)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'tags'], 'ByteLang0 tags must be an object', {
      actual: typeof byteLang0.tags,
    });
  }

  const duplicateTagValue = firstDuplicateObjectValue0(byteLang0.tags);

  if (duplicateTagValue !== null) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'tags'], 'ByteLang0 tag values must be unique', {
      duplicateTagValue,
      tags: byteLang0.tags,
    });
  }

  for (const [tagName, expected] of Object.entries(GENERATED_PCCPACK_BYTELANG_REQUIRED_TAGS0)) {
    if (byteLang0.tags[tagName] !== expected) {
      return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'tags', tagName], 'ByteLang0 required tag mismatch', {
        expected,
        actual: byteLang0.tags[tagName],
      });
    }
  }

  if (!isPlainObject(byteLang0.sorts)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'sorts'], 'ByteLang0 sorts must be an object', {
      actual: typeof byteLang0.sorts,
    });
  }

  for (const sortName of GENERATED_PCCPACK_BYTELANG_REQUIRED_SORTS0) {
    if (byteLang0.sorts[sortName] !== sortName) {
      return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'sorts', sortName], 'ByteLang0 required sort mismatch', {
        expected: sortName,
        actual: byteLang0.sorts[sortName],
      });
    }
  }

  if (!isPlainObject(byteLang0.constructors)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'constructors'], 'ByteLang0 constructors must be an object', {
      actual: typeof byteLang0.constructors,
    });
  }

  for (const constructorName of GENERATED_PCCPACK_BYTELANG_REQUIRED_CONSTRUCTORS0) {
    if (byteLang0.constructors[constructorName] !== constructorName) {
      return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'constructors', constructorName], 'ByteLang0 required constructor mismatch', {
        expected: constructorName,
        actual: byteLang0.constructors[constructorName],
      });
    }
  }

  if (!isPlainObject(byteLang0.records)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'records'], 'ByteLang0 records must be an object', {
      actual: typeof byteLang0.records,
    });
  }

  for (const [recordName, expected] of Object.entries(GENERATED_PCCPACK_BYTELANG_REQUIRED_RECORD_ARITIES0)) {
    if (byteLang0.records[recordName] !== expected) {
      return validationReject0(['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'records', recordName], 'ByteLang0 required record arity mismatch', {
        expected,
        actual: byteLang0.records[recordName],
      });
    }
  }

  const byteLangDigest = digestCanonical0(byteLang0);
  const piBootRefs = Array.isArray(boot0?.PiBoot?.refs) ? boot0.PiBoot.refs : [];

  const byteLangRef = piBootRefs.find((ref) => (
    ref?.label === 'ByteLang0' ||
    ref?.target === 'ByteLang0'
  ));

  if (!isPlainObject(byteLangRef)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs'], 'PiBoot must reference ByteLang0', {
      refs: piBootRefs,
    });
  }

  if (!sameDigestHex0(byteLangRef.digest, byteLangDigest)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs', 'ByteLang0'], 'PiBoot ByteLang0 digest must match concrete ByteLang0', {
      expected: byteLangDigest,
      actual: byteLangRef.digest,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackByteLang0NF',
    byteLang0: true,
    byteLang0Accepted: true,
    byteLang0Kind: byteLang0.kind ?? 'ByteLang0',
    byteLang0Digest: byteLangDigest,
    byteLang0TagCount: Object.keys(byteLang0.tags).length,
    byteLang0TagsUnique: duplicateTagValue === null,
    byteLang0RequiredTagsPresent: true,
    byteLang0SortCount: Object.keys(byteLang0.sorts).length,
    byteLang0RequiredSortsPresent: true,
    byteLang0ConstructorCount: Object.keys(byteLang0.constructors).length,
    byteLang0RequiredConstructorsPresent: true,
    byteLang0RecordCount: Object.keys(byteLang0.records).length,
    byteLang0RequiredRecordAritiesPresent: true,
    byteLang0PiBootDigestMatches: true,
  });
}

function firstDuplicateObjectValue0(value) {
  const seen = new Set();

  for (const item of Object.values(value)) {
    const key = JSON.stringify(item);

    if (seen.has(key)) {
      return item;
    }

    seen.add(key);
  }

  return null;
}

function validateGeneratedIfaceSched0(generatedPackage) {
  const materializedPCCPack = generatedPackage?.MaterializedPCCPackEnvelope ?? generatedPackage?.MaterializedPCCPack ?? null;
  const boot0 = materializedPCCPack?.MaterializedBoot0 ?? materializedPCCPack?.PCCPack?.Boot0 ?? null;
  const ifaceDict0 = boot0?.IfaceDict0 ?? null;
  const sched0 = boot0?.Sched0 ?? null;

  if (!isPlainObject(ifaceDict0)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0'], 'GeneratedPCCPack must include concrete IfaceDict0', {
      actual: typeof ifaceDict0,
    });
  }

  if (ifaceDict0.kind !== undefined && ifaceDict0.kind !== 'IfaceDict0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'kind'], 'IfaceDict0 kind mismatch', {
      actual: ifaceDict0.kind,
    });
  }

  if (!Array.isArray(ifaceDict0.forbiddenSymbols)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'forbiddenSymbols'], 'IfaceDict0 forbiddenSymbols must be an array', {
      actual: typeof ifaceDict0.forbiddenSymbols,
    });
  }

  const missingForbiddenSymbols = GENERATED_PCCPACK_IFACE_REQUIRED_FORBIDDEN_SYMBOLS0.filter((symbol) => (
    !ifaceDict0.forbiddenSymbols.includes(symbol)
  ));

  if (missingForbiddenSymbols.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'forbiddenSymbols'], 'IfaceDict0 is missing required forbidden executable symbols', {
      missingForbiddenSymbols,
      actual: ifaceDict0.forbiddenSymbols,
    });
  }

  if (!Array.isArray(ifaceDict0.publicConstructors)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'publicConstructors'], 'IfaceDict0 publicConstructors must be an array', {
      actual: typeof ifaceDict0.publicConstructors,
    });
  }

  const missingPublicConstructors = GENERATED_PCCPACK_IFACE_PUBLIC_CONSTRUCTORS0.filter((constructorName) => (
    !ifaceDict0.publicConstructors.includes(constructorName)
  ));

  if (missingPublicConstructors.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'publicConstructors'], 'IfaceDict0 is missing required public constructors', {
      missingPublicConstructors,
      actual: ifaceDict0.publicConstructors,
    });
  }

  if (!Array.isArray(ifaceDict0.criticalKinds)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'criticalKinds'], 'IfaceDict0 criticalKinds must be an array', {
      actual: typeof ifaceDict0.criticalKinds,
    });
  }

  const missingCriticalKinds = GENERATED_PCCPACK_IFACE_CRITICAL_KINDS0.filter((kind) => (
    !ifaceDict0.criticalKinds.includes(kind)
  ));

  if (missingCriticalKinds.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'criticalKinds'], 'IfaceDict0 is missing critical route kinds', {
      missingCriticalKinds,
      actual: ifaceDict0.criticalKinds,
    });
  }

  if (!Array.isArray(ifaceDict0.routeTokens)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'routeTokens'], 'IfaceDict0 routeTokens must be an array', {
      actual: typeof ifaceDict0.routeTokens,
    });
  }

  const missingRouteTokens = GENERATED_PCCPACK_IFACE_ROUTE_TOKENS0.filter((token) => (
    !ifaceDict0.routeTokens.includes(token)
  ));

  if (missingRouteTokens.length > 0) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'routeTokens'], 'IfaceDict0 is missing required route tokens', {
      missingRouteTokens,
      actual: ifaceDict0.routeTokens,
    });
  }

  if (!isPlainObject(sched0)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0'], 'GeneratedPCCPack must include concrete Sched0', {
      actual: typeof sched0,
    });
  }

  if (sched0.kind !== undefined && sched0.kind !== 'Sched0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'kind'], 'Sched0 kind mismatch', {
      actual: sched0.kind,
    });
  }

  if (!isPlainObject(sched0.core)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'core'], 'Sched0 core must be an object', {
      actual: typeof sched0.core,
    });
  }

  for (const [field, expected] of Object.entries(GENERATED_PCCPACK_SCHED_REQUIRED_CORE0)) {
    if (sched0.core[field] !== expected) {
      return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'core', field], 'Sched0 core constant mismatch', {
        expected,
        actual: sched0.core[field],
      });
    }
  }

  if (!isPlainObject(sched0.packageScaleFactors)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'packageScaleFactors'], 'Sched0 packageScaleFactors must be an object', {
      actual: typeof sched0.packageScaleFactors,
    });
  }

  for (const [field, expected] of Object.entries(GENERATED_PCCPACK_SCHED_REQUIRED_SCALE_FACTORS0)) {
    if (sched0.packageScaleFactors[field] !== expected) {
      return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'packageScaleFactors', field], 'Sched0 package scale factor mismatch', {
        expected,
        actual: sched0.packageScaleFactors[field],
      });
    }
  }

  if (!isPlainObject(sched0.selectorBounds)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'selectorBounds'], 'Sched0 selectorBounds must be an object', {
      actual: typeof sched0.selectorBounds,
    });
  }

  if (sched0.selectorBounds.bH !== 8) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'selectorBounds', 'bH'], 'Sched0 selector bound bH mismatch', {
      expected: 8,
      actual: sched0.selectorBounds.bH,
    });
  }

  if (sched0.selectorBounds.bTheta !== 12) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'selectorBounds', 'bTheta'], 'Sched0 selector bound bTheta mismatch', {
      expected: 12,
      actual: sched0.selectorBounds.bTheta,
    });
  }

  if (sched0.selectorBounds.polynomialExponent !== 36) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Sched0', 'selectorBounds', 'polynomialExponent'], 'Sched0 selector polynomial exponent mismatch', {
      expected: 36,
      actual: sched0.selectorBounds.polynomialExponent,
    });
  }

  const ifaceDigest = digestCanonical0(ifaceDict0);
  const schedDigest = digestCanonical0(sched0);
  const piBootRefs = Array.isArray(boot0?.PiBoot?.refs) ? boot0.PiBoot.refs : [];

  const ifaceRef = piBootRefs.find((ref) => (
    ref?.label === 'IfaceDict0' ||
    ref?.target === 'IfaceDict0'
  ));

  if (!isPlainObject(ifaceRef)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs'], 'PiBoot must reference IfaceDict0', {
      refs: piBootRefs,
    });
  }

  if (!sameDigestHex0(ifaceRef.digest, ifaceDigest)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs', 'IfaceDict0'], 'PiBoot IfaceDict0 digest must match concrete IfaceDict0', {
      expected: ifaceDigest,
      actual: ifaceRef.digest,
    });
  }

  const schedRef = piBootRefs.find((ref) => (
    ref?.label === 'Sched0' ||
    ref?.target === 'Sched0'
  ));

  if (!isPlainObject(schedRef)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs'], 'PiBoot must reference Sched0', {
      refs: piBootRefs,
    });
  }

  if (!sameDigestHex0(schedRef.digest, schedDigest)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs', 'Sched0'], 'PiBoot Sched0 digest must match concrete Sched0', {
      expected: schedDigest,
      actual: schedRef.digest,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackIfaceSched0NF',

    ifaceDict0: true,
    ifaceDict0Accepted: true,
    ifaceDict0Kind: ifaceDict0.kind ?? 'IfaceDict0',
    ifaceDict0Digest: ifaceDigest,
    ifaceDict0ForbiddenSymbolCount: ifaceDict0.forbiddenSymbols.length,
    ifaceDict0RequiredForbiddenSymbolsPresent: missingForbiddenSymbols.length === 0,
    ifaceDict0NoExecutableMinSymbols: true,
    ifaceDict0PublicConstructorsPresent: missingPublicConstructors.length === 0,
    ifaceDict0CriticalKindsPresent: missingCriticalKinds.length === 0,
    ifaceDict0RouteTokensPresent: missingRouteTokens.length === 0,
    ifaceDict0PiBootDigestMatches: true,

    sched0: true,
    sched0Accepted: true,
    sched0Kind: sched0.kind ?? 'Sched0',
    sched0Digest: schedDigest,
    sched0CoreMatchesExpected: true,
    sched0CoreB0: sched0.core.B0,
    sched0CoreK0: sched0.core.K0,
    sched0CoreR0: sched0.core.R0,
    sched0CoreH0: sched0.core.H0,
    sched0CoreO0: sched0.core.O0,
    sched0CoreRel0: sched0.core.Rel0,
    sched0ScaleFactorsPresent: true,
    sched0SelectorBoundsPresent: true,
    sched0SelectorBoundBH: sched0.selectorBounds.bH,
    sched0SelectorBoundBTheta: sched0.selectorBounds.bTheta,
    sched0PolynomialExponent: sched0.selectorBounds.polynomialExponent,
    sched0PiBootDigestMatches: true,
  });
}

function validateGeneratedCodecDigest0(generatedPackage) {
  const materializedPCCPack = generatedPackage?.MaterializedPCCPackEnvelope ?? generatedPackage?.MaterializedPCCPack ?? null;
  const boot0 = materializedPCCPack?.MaterializedBoot0 ?? materializedPCCPack?.PCCPack?.Boot0 ?? null;
  const codec0 = boot0?.Codec0 ?? null;
  const digest0 = boot0?.Digest0 ?? null;

  if (!isPlainObject(codec0)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0'], 'GeneratedPCCPack must include concrete Codec0', {
      actual: typeof codec0,
    });
  }

  if (codec0.kind !== undefined && codec0.kind !== 'Codec0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'kind'], 'Codec0 kind mismatch', {
      actual: codec0.kind,
    });
  }

  if (codec0.canonical !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'canonical'], 'Codec0 must require canonical encoding', {
      actual: codec0.canonical,
    });
  }

  if (codec0.naturalEncoding !== 'u32be-length-shortest-big-endian-magnitude') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'naturalEncoding'], 'Codec0 natural encoding must be shortest big-endian magnitude with u32be length', {
      actual: codec0.naturalEncoding,
    });
  }

  if (codec0.integerEncoding !== 'sign-byte-plus-canonical-natural-no-negative-zero') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'integerEncoding'], 'Codec0 integer encoding must reject negative zero', {
      actual: codec0.integerEncoding,
    });
  }

  if (codec0.stringEncoding !== 'utf8-nfc-length-prefixed') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'stringEncoding'], 'Codec0 string encoding must be UTF-8 NFC length-prefixed', {
      actual: codec0.stringEncoding,
    });
  }

  if (codec0.topLevelConsumesAllBytes !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'topLevelConsumesAllBytes'], 'Codec0 top-level parser must consume all bytes', {
      actual: codec0.topLevelConsumesAllBytes,
    });
  }

  if (codec0.normalFormSerialization !== 'canonical-json-v0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Codec0', 'normalFormSerialization'], 'Codec0 normal-form serialization must be canonical-json-v0', {
      actual: codec0.normalFormSerialization,
    });
  }

  if (!isPlainObject(digest0)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Digest0'], 'GeneratedPCCPack must include concrete Digest0', {
      actual: typeof digest0,
    });
  }

  if (digest0.kind !== undefined && digest0.kind !== 'Digest0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Digest0', 'kind'], 'Digest0 kind mismatch', {
      actual: digest0.kind,
    });
  }

  if (digest0.alg !== 'SHA256') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Digest0', 'alg'], 'Digest0 algorithm must be SHA256', {
      actual: digest0.alg,
    });
  }

  if (digest0.bytes !== 'canonical-json-v0') {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Digest0', 'bytes'], 'Digest0 byte discipline must be canonical-json-v0', {
      actual: digest0.bytes,
    });
  }

  if (digest0.digestEqualityIsNotObjectEquality !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Digest0', 'digestEqualityIsNotObjectEquality'], 'Digest0 must record that digest equality is not object equality', {
      actual: digest0.digestEqualityIsNotObjectEquality,
    });
  }

  if (digest0.fullKeyComparisonAfterHashLookup !== true) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'Digest0', 'fullKeyComparisonAfterHashLookup'], 'Digest0 hash lookups must be followed by full key comparison', {
      actual: digest0.fullKeyComparisonAfterHashLookup,
    });
  }

  const codecDigest = digestCanonical0(codec0);
  const digestDigest = digestCanonical0(digest0);
  const piBootRefs = Array.isArray(boot0?.PiBoot?.refs) ? boot0.PiBoot.refs : [];

  const codecRef = piBootRefs.find((ref) => (
    ref?.label === 'Codec0' ||
    ref?.target === 'Codec0'
  ));

  if (!isPlainObject(codecRef)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs'], 'PiBoot must reference Codec0', {
      refs: piBootRefs,
    });
  }

  if (!sameDigestHex0(codecRef.digest, codecDigest)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs', 'Codec0'], 'PiBoot Codec0 digest must match concrete Codec0', {
      expected: codecDigest,
      actual: codecRef.digest,
    });
  }

  const digestRef = piBootRefs.find((ref) => (
    ref?.label === 'Digest0' ||
    ref?.target === 'Digest0'
  ));

  if (!isPlainObject(digestRef)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs'], 'PiBoot must reference Digest0', {
      refs: piBootRefs,
    });
  }

  if (!sameDigestHex0(digestRef.digest, digestDigest)) {
    return validationReject0(['GeneratedPCCPack', 'Boot0', 'PiBoot', 'refs', 'Digest0'], 'PiBoot Digest0 digest must match concrete Digest0', {
      expected: digestDigest,
      actual: digestRef.digest,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPCCPackCodecDigest0NF',

    codec0: true,
    codec0Accepted: true,
    codec0Kind: codec0.kind ?? 'Codec0',
    codec0Digest: codecDigest,
    codec0Canonical: codec0.canonical === true,
    codec0NaturalEncoding: codec0.naturalEncoding,
    codec0IntegerEncoding: codec0.integerEncoding,
    codec0StringEncoding: codec0.stringEncoding,
    codec0TopLevelConsumesAllBytes: codec0.topLevelConsumesAllBytes === true,
    codec0NormalFormSerialization: codec0.normalFormSerialization,
    codec0PiBootDigestMatches: true,

    digest0: true,
    digest0Accepted: true,
    digest0Kind: digest0.kind ?? 'Digest0',
    digest0Digest: digestDigest,
    digest0Alg: digest0.alg,
    digest0Bytes: digest0.bytes,
    digest0EqualityNotObjectEquality: digest0.digestEqualityIsNotObjectEquality === true,
    digest0FullKeyComparisonAfterHashLookup: digest0.fullKeyComparisonAfterHashLookup === true,
    digest0PiBootDigestMatches: true,
  });
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
