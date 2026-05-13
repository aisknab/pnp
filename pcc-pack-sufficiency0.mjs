import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  makeAuditCase,
  makeRejectCase,
} from './pcc-verifier-frag0.mjs';

import {
  CheckBoot0,
  makeBootstrapB0Rows0,
} from './pcc-boot0.mjs';

import {
  CheckKBundle0,
  makeKernelConformanceSuite0,
  makeReflectionRegistry0,
  makeSigmaRegistry0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckHard0,
  makeSyntheticHardCheck0,
} from './pcc-hard0.mjs';

import {
  CheckRows0,
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

import {
  CheckGlobalProofDAG0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckLocalPackages0,
  makeSyntheticLocalPackages0,
} from './pcc-local-packages0.mjs';

import {
  CheckGlobalFirewalls0,
  makeSyntheticGlobalFirewalls0,
} from './pcc-global-firewalls0.mjs';

import {
  CheckGPack0,
  CheckRowFamG0,
  makeSyntheticGPack0,
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  CheckFinalIntegration0,
  makeSyntheticFinalIntegration0,
} from './pcc-final-framework0.mjs';

import {
  CheckFinal0,
  CheckRowFamFinal0,
  makeSyntheticFinalTheorem0,
  makeSyntheticRowFamFinal0,
} from './pcc-final0.mjs';

const CHECKER_VERSION = 0;

export const PACK_SUFFICIENCY_PHASES0 = Object.freeze([
  'Φ0.CheckBoot0',
  'Φ4.CheckKBundle0',
  'Φ5.CheckHard0',
  'Φ6.CheckRows0',
  'Φ7.CheckGlobalProofDAG0',
  'Φ8.CheckLocalPackages0',
  'Φ9.CheckGlobalFirewalls0',
  'Φ10.CheckGPack0',
  'Φ10.CheckRowFamG0',
  'Φ11.CheckFinalIntegration0',
  'Φ12.CheckFinal0',
  'Φ12.CheckRowFamFinal0',
  'Φ13.CheckPackSufficiency0',
]);

export const PCCPACK_REQUIRED_FIELDS0 = Object.freeze([
  'Core',
  'Manifest',
  'Boot0',
  'KBundle',
  'HardCheck',
  'RowPack',
  'GlobalProofDAG',
  'LocalPackages',
  'GlobalFirewalls',
  'GPack',
  'RowFamG',
  'FinalIntegration',
  'FinalTheorem',
  'RowFamFinal',
  'PackSufficiencyTheorem',
]);

export const PACK_SUFFICIENCY_THEOREM_IDS0 = Object.freeze([
  'PackageSufficiency',
  'ResidualBandExactMinimization',
  'GeneratedPackageSufficiency',
  'FinalAcceptanceImpliesCheckPCCPack',
  'CheckPCCPackAcceptImpliesPEqualsNP',
]);

export const PACK_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
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

export const PACK_EXPANSION_STAGES0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
]);

const EXECUTABLE_KEYS0 = new Set([
  'exec',
  'execs',
  'execCall',
  'execCalls',
  'call',
  'calls',
  'callee',
  'operator',
  'operation',
  'program',
  'body',
  'macroBody',
  'templateBody',
  'generatedBody',
]);

export function makeSyntheticBoot0(overrides = {}) {
  return {
    kind: 'Boot0',
    version: CHECKER_VERSION,

    ByteLang0: {
      kind: 'ByteLang0',
      version: CHECKER_VERSION,
      tags: {
        Boot0: 0x0001,
        BootBatch0: 0x0002,
        Row0: 0x0003,
        Digest0: 0x0004,
      },
      sorts: {
        Unit: 'Unit',
        Name: 'Name',
        Record: 'Record',
        Row: 'Row',
      },
      constructors: {
        accept: 'accept',
        reject: 'reject',
        row: 'row',
      },
      records: {
        Boot0: 9,
        BootBatch0: 3,
        Row0: 12,
      },
    },

    Codec0: {
      kind: 'Codec0',
      version: CHECKER_VERSION,
      canonical: true,
    },

    Digest0: {
      kind: 'Digest0',
      version: CHECKER_VERSION,
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
    },

    IfaceDict0: {
      kind: 'IfaceDict0',
      version: CHECKER_VERSION,
      forbiddenSymbols: [
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
      ],
      publicConstructors: [
        'Gain',
        'Minimum',
        'ZeroSlack',
        'NoBudget',
        'NoHereditary',
        'SelectorSilent',
        'Faithful',
        'Token',
      ],
    },

    Sched0: {
      kind: 'Sched0',
      version: CHECKER_VERSION,
      core: {
        B0: 64,
        K0: 512,
        R0: 64,
        H0: 128,
        O0: 64,
        Rel0: 16,
      },
    },

    KernelSeed0: {
      kind: 'KernelSeed0',
      version: CHECKER_VERSION,
      rules: [
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
      ],
    },

    B0: {
      kind: 'BootBatch0',
      version: CHECKER_VERSION,
      batchId: 'B0',
      rows: makeBootstrapB0Rows0(),
    },

    BootAudit0: {
      kind: 'VerifierFrag0',
      version: CHECKER_VERSION,
      suiteId: 'pack.synthetic.boot.audit',
      cases: [
        makeAuditCase({
          id: 'pack.boot.audit.positive',
          target: 'BootAudit0',
          run: () => undefined,
        }),
        makeRejectCase({
          id: 'pack.boot.audit.negative',
          target: 'BootAudit0',
          run: () => ({
            tag: 'reject',
            coord: 'synthetic.negative',
          }),
        }),
      ],
    },

    PiBoot: {
      kind: 'PiBoot0',
      version: CHECKER_VERSION,
      note: 'synthetic bootstrap proof marker for pack sufficiency',
    },

    ...overrides,
  };
}

export function makeSyntheticKBundle0(overrides = {}) {
  return {
    KImpl: makeSyntheticKImpl0(),
    K0: makeKernelConformanceSuite0(),
    PSigma: makeSigmaRegistry0(),
    ReflectionRegistry: makeReflectionRegistry0(),
    ...overrides,
  };
}

export function makeSyntheticPackSufficiencyTheorem0(overrides = {}) {
  return {
    kind: 'PackSufficiencyTheorem0',
    version: CHECKER_VERSION,
    theoremIds: PACK_SUFFICIENCY_THEOREM_IDS0,

    checker: 'CheckPCCPackexp',
    packageKind: 'PCCPack0',

    packageSufficiency: {
      id: 'PackageSufficiency',
      acceptedPackageValid: true,
      explicitFinite: true,
      polynomial: true,
      allLocalPackagesAccepted: true,
      allGlobalFirewallsAccepted: true,
      allFinalArtefactsAccepted: true,
    },

    residualBandMinimization: {
      id: 'ResidualBandExactMinimization',
      assumption: 'Lambda(C0)<=O(log|C0|)',
      conclusion: 'PCCMin_exp(C0) returns an exact minimum equivalent circuit in polynomial time',
      pccMinReturnsExactMinimum: true,
      residualSlackBounded: true,
      zeroSlackSound: true,
      terminalCarrierPreservesSemantics: true,
      terminalizationSizePreserving: true,
      closedFullWordRealizesCircuit: true,
      quotientEqualityNotConstructive: true,
      wholeSpanCheaperImpliesStrictDescent: true,
      transparentSaturationCostBalanced: true,
      interfaceExposureRoutesToE: true,
      originKernelObligationClosureRouted: true,
      projectionPositivityNotLostSilently: true,
      firstNontransparentStepRecorded: true,
      zeroSlackEarlierRoutesExcluded: true,
      positiveResidualWitnessYieldsBCELReady: true,
      positiveResidualWitnessExists: true,
      finiteAnchorSetExtracted: true,
      booleanAnchorAlgebraOrRoute: true,
      minimalPositiveNucleus: true,
      properCutConstantEquation: true,
      anchorSizeAtLeastTwo: true,
      bcelAnchorAlgebraBooleanOrRoutes: true,
      sideTightOnlyNoOverclaim: true,
      fourCornerOptimaCarrierCompatible: true,
      sideTightCompletionExists: true,
      tightBasisValueEqualsDelta: true,
      requestPredicatesStable: true,
      minimalConsumerAntichainsExact: true,
      jointSideTightRealizability: true,
      runtimeIntegersSeparatedFromFiniteState: true,
      incidenceAtomsAccountedExactlyOnce: true,
      activationByActiveAntichain: true,
      activationEqualityWithoutCutEnumeration: true,
      sameKeyCancellationExact: true,
      noOppositeSignSameKeyResidual: true,
      integerMassLedgerExact: true,
      negativeFullResidualLocalized: true,
      hallDeficitRoutesNamedOutcome: true,
      quotientToFullMatchingKeyPreserving: true,
      separatingConsumersSingletonized: true,
      unmatchedShadowNotSilent: true,
      constantCutHypergraphHypotheses: true,
      pairTriFullSpanExhaustive: true,
      mixedTripleCaseHandled: true,
      packetAtomsHaveSelectorPayloads: true,
      selectorUniverseCompleteAndPolynomial: true,
      selectorUniverseCompleteForPackets: true,
      realizerBotTyped: true,
      realizerBotOnlyHNBUDBlockedOrLowerRank: true,
      chargeSurplusInjectionStrict: true,
      blockerGraphAcyclicByRank: true,
      hbBlockerGraphAcyclic: true,
      selectorSilenceRankComplete: true,
      hbNoCircularNegativeClosure: true,
      zeroSlackContradictionFromPositiveSlack: true,
      zeroSlackCertificatePolynomialSize: true,
    },

    generatedPackageSufficiency: {
      id: 'GeneratedPackageSufficiency',
      generatorUntrusted: true,
      materializedOutputOnly: true,
      canonicalByteEquality: true,
      noDigestOnlyEquality: true,
      coreExcludesAcceptRun: true,
      assumption: 'CheckPCCPackexp(Core(GeneratePCCPack()))=accept',
      conclusion: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    },

    finalAcceptanceImplication: {
      id: 'FinalAcceptanceImpliesCheckPCCPack',
      antecedent: 'AcceptRun.Verdict=accept',
      replayed: true,
      canonicalBytesCompared: true,
      generatorOutputMatchedByBytes: true,
      conclusion: 'CheckPCCPackexp(Core(GeneratePCCPack()))=accept',
    },

    publicConclusion: {
      id: 'CheckPCCPackAcceptImpliesPEqualsNP',
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
      noClaimBeforeAccept: true,
      exported: true,
    },

    reflection: {
      exact: true,
      publicConclusion: true,
      replayable: true,
    },

    noHiddenMin: {
      expansionStages: PACK_EXPANSION_STAGES0,
      forbiddenSymbols: PACK_FORBIDDEN_EXEC_SYMBOLS0,
    },

    PiPackSufficiency: {
      kind: 'PiPackSufficiency0',
      version: CHECKER_VERSION,
      note: 'synthetic package sufficiency proof marker',
    },

    ...overrides,
  };
}

export function makeSyntheticPCCPack0(overrides = {}) {
  const gpack = makeSyntheticGPack0();
  const finalIntegration = makeSyntheticFinalIntegration0({
    gpack,
  });
  const finalTheorem = makeSyntheticFinalTheorem0({
    finalIntegration,
  });

  const pack = {
    kind: 'PCCPack0',
    version: CHECKER_VERSION,

    Core: {
      kind: 'PCCCorePackage0',
      version: CHECKER_VERSION,
      generatedBy: 'GeneratePCCPack',
      excludesAcceptRun: true,
      includesAcceptRun: false,
      generatorUntrusted: true,
      materializedOutputOnly: true,
      canonicalByteEquality: true,
      noDigestOnlyEquality: true,
      canonicalBytes: {
        alg: 'canonical-json-v0',
        digest: {
          alg: 'SHA256',
          hex: 'c27a582a059b496b7114f22aebff586a1f418358ac10350f83877e5db1eb1288',
        },
      },
    },

    Manifest: {
      kind: 'PCCPackManifest0',
      version: CHECKER_VERSION,
      phaseOrder: PACK_SUFFICIENCY_PHASES0,
      requiredArtefacts: PCCPACK_REQUIRED_FIELDS0,
      checker: 'CheckPCCPackexp',
      finalVerdictExcluded: true,
    },

    Boot0: makeSyntheticBoot0(),
    KBundle: makeSyntheticKBundle0(),
    HardCheck: makeSyntheticHardCheck0(),
    RowPack: makeSyntheticRowPack0(),
    GlobalProofDAG: makeSyntheticGlobalProofDAG0(),
    LocalPackages: makeSyntheticLocalPackages0(),
    GlobalFirewalls: makeSyntheticGlobalFirewalls0(),

    GPack: gpack,
    RowFamG: makeSyntheticRowFamG0(gpack),
    FinalIntegration: finalIntegration,
    FinalTheorem: finalTheorem,
    RowFamFinal: makeSyntheticRowFamFinal0(finalTheorem),

    PackSufficiencyTheorem: makeSyntheticPackSufficiencyTheorem0(),

    PiPackSufficiency: {
      kind: 'PiPackSufficiencyRun0',
      version: CHECKER_VERSION,
      note: 'synthetic top-level package sufficiency proof marker',
    },

    ...overrides,
  };

  return pack;
}

export async function CheckPackSufficiency0(pack) {
  const checker = 'CheckPackSufficiency0';
  const ledger = [];

  const initialPhases = [
    ['shape', `${checker}.input`, () => validatePackShape0(pack)],
    ['manifest', `${checker}.manifest`, () => validateManifest0(pack)],
    ['core', `${checker}.core`, () => validateCoreBoundary0(pack)],
  ];

  for (const [phase, coord, run] of initialPhases) {
    const result = run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const checkerPhases = [
    ['CheckBoot0', `${checker}.Boot0`, ['Boot0'], await CheckBoot0(pack.Boot0)],
    ['CheckKBundle0', `${checker}.KBundle`, ['KBundle'], await CheckKBundle0(pack.KBundle)],
    ['CheckHard0', `${checker}.HardCheck`, ['HardCheck'], await CheckHard0(pack.HardCheck)],
    ['CheckRows0', `${checker}.RowPack`, ['RowPack'], await CheckRows0(pack.RowPack)],
    ['CheckGlobalProofDAG0', `${checker}.GlobalProofDAG`, ['GlobalProofDAG'], await CheckGlobalProofDAG0(pack.GlobalProofDAG)],
    ['CheckLocalPackages0', `${checker}.LocalPackages`, ['LocalPackages'], await CheckLocalPackages0(pack.LocalPackages)],
    ['CheckGlobalFirewalls0', `${checker}.GlobalFirewalls`, ['GlobalFirewalls'], await CheckGlobalFirewalls0(pack.GlobalFirewalls)],
    ['CheckGPack0', `${checker}.GPack`, ['GPack'], await CheckGPack0(pack.GPack)],
    ['CheckRowFamG0', `${checker}.RowFamG`, ['RowFamG'], await CheckRowFamG0(pack.RowFamG)],
    ['CheckFinalIntegration0', `${checker}.FinalIntegration`, ['FinalIntegration'], await CheckFinalIntegration0(pack.FinalIntegration)],
    ['CheckFinal0', `${checker}.FinalTheorem`, ['FinalTheorem'], await CheckFinal0(pack.FinalTheorem)],
    ['CheckRowFamFinal0', `${checker}.RowFamFinal`, ['RowFamFinal'], await CheckRowFamFinal0(pack.RowFamFinal)],
  ];

  const phaseDigests = [];

  for (const [phase, coord, path, record] of checkerPhases) {
    const result = recordToValidation0(record, path);

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    phaseDigests.push({
      phase,
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });
  }

  const finalPhases = [
    ['crossArtefactConsistency', `${checker}.cross`, () => validateCrossArtefactConsistency0(pack)],
    ['packTheorem', `${checker}.PackSufficiencyTheorem`, () => validatePackSufficiencyTheorem0(pack.PackSufficiencyTheorem)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(pack, ['PCCPack0'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(pack, ['PCCPack0'])],
  ];

  for (const [phase, coord, run] of finalPhases) {
    const result = run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'PackSufficiency0NF',
    checker,
    version: CHECKER_VERSION,
    packageKind: pack.kind,
    phaseOrder: PACK_SUFFICIENCY_PHASES0,
    phaseDigests,
    theoremIds: PACK_SUFFICIENCY_THEOREM_IDS0,
    publicConclusion: pack.PackSufficiencyTheorem.publicConclusion,
    residualBandMinimizationDigest:
      digestCanonical0(pack.PackSufficiencyTheorem.residualBandMinimization),
    residualBandExactMinimization:
      pack.PackSufficiencyTheorem.residualBandMinimization?.pccMinReturnsExactMinimum === true,
    zeroSlackSound:
      pack.PackSufficiencyTheorem.residualBandMinimization?.zeroSlackSound === true,
    zeroSlackContradictionFromPositiveSlack:
      pack.PackSufficiencyTheorem.residualBandMinimization?.zeroSlackContradictionFromPositiveSlack === true,
    terminalMuBridgeComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.terminalCarrierPreservesSemantics === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.terminalizationSizePreserving === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.closedFullWordRealizesCircuit === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.quotientEqualityNotConstructive === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.wholeSpanCheaperImpliesStrictDescent === true,
    saturatePositiveComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.transparentSaturationCostBalanced === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.interfaceExposureRoutesToE === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.originKernelObligationClosureRouted === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.projectionPositivityNotLostSilently === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.firstNontransparentStepRecorded === true,
    bcelReadyPositiveNucleusComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.positiveResidualWitnessYieldsBCELReady === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.positiveResidualWitnessExists === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.finiteAnchorSetExtracted === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.booleanAnchorAlgebraOrRoute === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.minimalPositiveNucleus === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.properCutConstantEquation === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.anchorSizeAtLeastTwo === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.bcelAnchorAlgebraBooleanOrRoutes === true,
    bn2SideTightCoherentOptimaComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.sideTightOnlyNoOverclaim === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.fourCornerOptimaCarrierCompatible === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.sideTightCompletionExists === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.tightBasisValueEqualsDelta === true,
    bn3FiniteRequestEnvelopeComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.requestPredicatesStable === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.minimalConsumerAntichainsExact === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.jointSideTightRealizability === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.runtimeIntegersSeparatedFromFiniteState === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.incidenceAtomsAccountedExactlyOnce === true,
    bn4ActivationExactCancellationComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.activationByActiveAntichain === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.activationEqualityWithoutCutEnumeration === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.sameKeyCancellationExact === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.noOppositeSignSameKeyResidual === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.integerMassLedgerExact === true,
    bn5PkgCLocalizationComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.negativeFullResidualLocalized === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.hallDeficitRoutesNamedOutcome === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.quotientToFullMatchingKeyPreserving === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.separatingConsumersSingletonized === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.unmatchedShadowNotSilent === true,
    bn6PacketCollapseSelectorComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.constantCutHypergraphHypotheses === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.pairTriFullSpanExhaustive === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.mixedTripleCaseHandled === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.packetAtomsHaveSelectorPayloads === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.selectorUniverseCompleteAndPolynomial === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.selectorUniverseCompleteForPackets === true,
    realizerHBClosureComplete:
      pack.PackSufficiencyTheorem.residualBandMinimization?.realizerBotTyped === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.realizerBotOnlyHNBUDBlockedOrLowerRank === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.chargeSurplusInjectionStrict === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.blockerGraphAcyclicByRank === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.hbBlockerGraphAcyclic === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.selectorSilenceRankComplete === true &&
      pack.PackSufficiencyTheorem.residualBandMinimization?.hbNoCircularNegativeClosure === true,
    generatedPackageAssumption: pack.PackSufficiencyTheorem.generatedPackageSufficiency.assumption,
    coreDigest: digestCanonical0(pack.Core),
    manifestDigest: digestCanonical0(pack.Manifest),
    packTheoremDigest: digestCanonical0(pack.PackSufficiencyTheorem),
    piPackSufficiencyDigest: digestCanonical0(getPiPackSufficiency0(pack)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validatePackShape0(pack) {
  if (!isPlainObject(pack)) {
    return validationReject0([], 'PCCPack0 must be an object', {
      actual: typeof pack,
    });
  }

  if (pack.kind !== undefined && pack.kind !== 'PCCPack0') {
    return validationReject0(['kind'], 'PCCPack0 kind must be PCCPack0 when present', {
      actual: pack.kind,
    });
  }

  if (pack.version !== undefined && pack.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `PCCPack0 version must be ${CHECKER_VERSION} when present`, {
      actual: pack.version,
    });
  }

  for (const field of PCCPACK_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(pack, field)) {
      return validationReject0([field], 'PCCPack0 is missing a required artefact', {
        field,
      });
    }
  }

  if (getPiPackSufficiency0(pack) === undefined) {
    return validationReject0(['PiPackSufficiency'], 'PCCPack0 is missing PiPackSufficiency or Πpack', null);
  }

  return validationAccept0({
    kind: 'PCCPackShape0NF',
  });
}

function validateManifest0(pack) {
  const manifest = pack.Manifest;

  if (!isPlainObject(manifest)) {
    return validationReject0(['Manifest'], 'PCCPack Manifest must be an object', {
      actual: typeof manifest,
    });
  }

  if (manifest.kind !== undefined && manifest.kind !== 'PCCPackManifest0') {
    return validationReject0(['Manifest', 'kind'], 'PCCPack manifest kind must be PCCPackManifest0 when present', {
      actual: manifest.kind,
    });
  }

  if (!Array.isArray(manifest.phaseOrder)) {
    return validationReject0(['Manifest', 'phaseOrder'], 'PCCPack manifest phaseOrder must be an array', {
      actual: typeof manifest.phaseOrder,
    });
  }

  for (let index = 0; index < PACK_SUFFICIENCY_PHASES0.length; index += 1) {
    if (manifest.phaseOrder[index] !== PACK_SUFFICIENCY_PHASES0[index]) {
      return validationReject0(['Manifest', 'phaseOrder', index], 'PCCPack manifest phase order mismatch', {
        expected: PACK_SUFFICIENCY_PHASES0[index],
        actual: manifest.phaseOrder[index],
      });
    }
  }

  if (!arrayContainsAll0(manifest.requiredArtefacts, PCCPACK_REQUIRED_FIELDS0)) {
    return validationReject0(['Manifest', 'requiredArtefacts'], 'PCCPack manifest is missing required artefact names', {
      expected: PCCPACK_REQUIRED_FIELDS0,
      actual: manifest.requiredArtefacts,
    });
  }

  if (manifest.checker !== 'CheckPCCPackexp') {
    return validationReject0(['Manifest', 'checker'], 'PCCPack manifest checker must be CheckPCCPackexp', {
      actual: manifest.checker,
    });
  }

  if (manifest.finalVerdictExcluded !== true) {
    return validationReject0(['Manifest', 'finalVerdictExcluded'], 'PCCPack manifest must exclude final acceptance run verdict', {
      actual: manifest.finalVerdictExcluded,
    });
  }

  return validationAccept0({
    kind: 'PCCPackManifest0NF',
    phaseCount: PACK_SUFFICIENCY_PHASES0.length,
  });
}

function validateCoreBoundary0(pack) {
  if (Object.prototype.hasOwnProperty.call(pack, 'AcceptRun')) {
    return validationReject0(['AcceptRun'], 'PCCPack0 core package must not contain AcceptRun', null);
  }

  const core = pack.Core;

  if (!isPlainObject(core)) {
    return validationReject0(['Core'], 'PCCPack Core must be an object', {
      actual: typeof core,
    });
  }

  if (core.excludesAcceptRun !== true) {
    return validationReject0(['Core', 'excludesAcceptRun'], 'PCCPack Core must exclude AcceptRun', {
      actual: core.excludesAcceptRun,
    });
  }

  if (core.includesAcceptRun === true || Object.prototype.hasOwnProperty.call(core, 'AcceptRun')) {
    return validationReject0(['Core', 'AcceptRun'], 'PCCPack Core must not embed AcceptRun', null);
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
  ]) {
    if (core[field] !== true) {
      return validationReject0(['Core', field], `PCCPack Core must certify ${field}`, {
        actual: core[field],
      });
    }
  }

  return validationAccept0({
    kind: 'PCCPackCoreBoundary0NF',
  });
}

function validateCrossArtefactConsistency0(pack) {
  const checks = [
    {
      path: ['RowFamG', 'GPack'],
      reason: 'RowFamG GPack must match top-level GPack',
      left: pack.RowFamG.GPack,
      right: pack.GPack,
    },
    {
      path: ['FinalIntegration', 'GPack'],
      reason: 'FinalIntegration GPack must match top-level GPack',
      left: pack.FinalIntegration.GPack,
      right: pack.GPack,
    },
    {
      path: ['FinalTheorem', 'FinalIntegration'],
      reason: 'FinalTheorem FinalIntegration must match top-level FinalIntegration',
      left: pack.FinalTheorem.FinalIntegration,
      right: pack.FinalIntegration,
    },
    {
      path: ['RowFamFinal', 'FinalTheorem'],
      reason: 'RowFamFinal FinalTheorem must match top-level FinalTheorem',
      left: pack.RowFamFinal.FinalTheorem,
      right: pack.FinalTheorem,
    },
  ];

  for (const check of checks) {
    const leftDigest = digestCanonical0(check.left);
    const rightDigest = digestCanonical0(check.right);

    if (!sameDigest0(leftDigest, rightDigest)) {
      return validationReject0(check.path, check.reason, {
        expected: rightDigest,
        actual: leftDigest,
      });
    }
  }

  return validationAccept0({
    kind: 'PCCPackCrossArtefactConsistency0NF',
  });
}

function validatePackSufficiencyTheorem0(theorem) {
  if (!isPlainObject(theorem)) {
    return validationReject0(['PackSufficiencyTheorem'], 'PackSufficiencyTheorem must be an object', {
      actual: typeof theorem,
    });
  }

  if (theorem.kind !== undefined && theorem.kind !== 'PackSufficiencyTheorem0') {
    return validationReject0(['PackSufficiencyTheorem', 'kind'], 'PackSufficiencyTheorem kind mismatch', {
      actual: theorem.kind,
    });
  }

  if (!arrayContainsAll0(theorem.theoremIds, PACK_SUFFICIENCY_THEOREM_IDS0)) {
    return validationReject0(['PackSufficiencyTheorem', 'theoremIds'], 'PackSufficiencyTheorem is missing required theorem ids', {
      expected: PACK_SUFFICIENCY_THEOREM_IDS0,
      actual: theorem.theoremIds,
    });
  }

  if (theorem.checker !== 'CheckPCCPackexp') {
    return validationReject0(['PackSufficiencyTheorem', 'checker'], 'PackSufficiencyTheorem checker mismatch', {
      actual: theorem.checker,
    });
  }

  const packageSufficiency = theorem.packageSufficiency;

  if (!isPlainObject(packageSufficiency)) {
    return validationReject0(['PackSufficiencyTheorem', 'packageSufficiency'], 'packageSufficiency must be an object', null);
  }

  for (const field of [
    'acceptedPackageValid',
    'explicitFinite',
    'polynomial',
    'allLocalPackagesAccepted',
    'allGlobalFirewallsAccepted',
    'allFinalArtefactsAccepted',
  ]) {
    if (packageSufficiency[field] !== true) {
      return validationReject0(['PackSufficiencyTheorem', 'packageSufficiency', field], `packageSufficiency must certify ${field}`, {
        actual: packageSufficiency[field],
      });
    }
  }

  const residualBand = theorem.residualBandMinimization;

  if (!isPlainObject(residualBand)) {
    return validationReject0(['PackSufficiencyTheorem', 'residualBandMinimization'], 'residualBandMinimization must be an object', null);
  }

  if (residualBand.id !== 'ResidualBandExactMinimization') {
    return validationReject0(['PackSufficiencyTheorem', 'residualBandMinimization', 'id'], 'residualBandMinimization id mismatch', {
      actual: residualBand.id,
    });
  }

  if (residualBand.assumption !== 'Lambda(C0)<=O(log|C0|)') {
    return validationReject0(['PackSufficiencyTheorem', 'residualBandMinimization', 'assumption'], 'residualBandMinimization assumption mismatch', {
      actual: residualBand.assumption,
    });
  }

  if (residualBand.conclusion !== 'PCCMin_exp(C0) returns an exact minimum equivalent circuit in polynomial time') {
    return validationReject0(['PackSufficiencyTheorem', 'residualBandMinimization', 'conclusion'], 'residualBandMinimization conclusion mismatch', {
      actual: residualBand.conclusion,
    });
  }

  for (const field of [
    'pccMinReturnsExactMinimum',
    'residualSlackBounded',
    'zeroSlackSound',
    'terminalCarrierPreservesSemantics',
    'terminalizationSizePreserving',
    'closedFullWordRealizesCircuit',
    'quotientEqualityNotConstructive',
    'wholeSpanCheaperImpliesStrictDescent',
    'transparentSaturationCostBalanced',
    'interfaceExposureRoutesToE',
    'originKernelObligationClosureRouted',
    'projectionPositivityNotLostSilently',
    'firstNontransparentStepRecorded',
    'zeroSlackEarlierRoutesExcluded',
    'positiveResidualWitnessYieldsBCELReady',
    'positiveResidualWitnessExists',
    'finiteAnchorSetExtracted',
    'booleanAnchorAlgebraOrRoute',
    'minimalPositiveNucleus',
    'properCutConstantEquation',
    'anchorSizeAtLeastTwo',
    'bcelAnchorAlgebraBooleanOrRoutes',
    'sideTightOnlyNoOverclaim',
    'fourCornerOptimaCarrierCompatible',
    'sideTightCompletionExists',
    'tightBasisValueEqualsDelta',
    'requestPredicatesStable',
    'minimalConsumerAntichainsExact',
    'jointSideTightRealizability',
    'runtimeIntegersSeparatedFromFiniteState',
    'incidenceAtomsAccountedExactlyOnce',
    'activationByActiveAntichain',
    'activationEqualityWithoutCutEnumeration',
    'sameKeyCancellationExact',
    'noOppositeSignSameKeyResidual',
    'integerMassLedgerExact',
    'negativeFullResidualLocalized',
    'hallDeficitRoutesNamedOutcome',
    'quotientToFullMatchingKeyPreserving',
    'separatingConsumersSingletonized',
    'unmatchedShadowNotSilent',
    'constantCutHypergraphHypotheses',
    'pairTriFullSpanExhaustive',
    'mixedTripleCaseHandled',
    'packetAtomsHaveSelectorPayloads',
    'selectorUniverseCompleteAndPolynomial',
    'selectorUniverseCompleteForPackets',
    'realizerBotTyped',
    'realizerBotOnlyHNBUDBlockedOrLowerRank',
    'chargeSurplusInjectionStrict',
    'blockerGraphAcyclicByRank',
    'hbBlockerGraphAcyclic',
    'selectorSilenceRankComplete',
    'hbNoCircularNegativeClosure',
    'zeroSlackContradictionFromPositiveSlack',
    'zeroSlackCertificatePolynomialSize',
  ]) {
    if (residualBand[field] !== true) {
      return validationReject0(['PackSufficiencyTheorem', 'residualBandMinimization', field], `residualBandMinimization must certify ${field}`, {
        actual: residualBand[field],
      });
    }
  }

  const generated = theorem.generatedPackageSufficiency;

  if (!isPlainObject(generated)) {
    return validationReject0(['PackSufficiencyTheorem', 'generatedPackageSufficiency'], 'generatedPackageSufficiency must be an object', null);
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
    'coreExcludesAcceptRun',
  ]) {
    if (generated[field] !== true) {
      return validationReject0(['PackSufficiencyTheorem', 'generatedPackageSufficiency', field], `generatedPackageSufficiency must certify ${field}`, {
        actual: generated[field],
      });
    }
  }

  if (generated.assumption !== 'CheckPCCPackexp(Core(GeneratePCCPack()))=accept') {
    return validationReject0(['PackSufficiencyTheorem', 'generatedPackageSufficiency', 'assumption'], 'generated package sufficiency assumption mismatch', {
      actual: generated.assumption,
    });
  }

  if (generated.conclusion !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(['PackSufficiencyTheorem', 'generatedPackageSufficiency', 'conclusion'], 'generated package sufficiency conclusion mismatch', {
      actual: generated.conclusion,
    });
  }

  const finalAcceptance = theorem.finalAcceptanceImplication;

  if (!isPlainObject(finalAcceptance)) {
    return validationReject0(['PackSufficiencyTheorem', 'finalAcceptanceImplication'], 'finalAcceptanceImplication must be an object', null);
  }

  for (const field of [
    'replayed',
    'canonicalBytesCompared',
    'generatorOutputMatchedByBytes',
  ]) {
    if (finalAcceptance[field] !== true) {
      return validationReject0(['PackSufficiencyTheorem', 'finalAcceptanceImplication', field], `finalAcceptanceImplication must certify ${field}`, {
        actual: finalAcceptance[field],
      });
    }
  }

  const publicConclusion = theorem.publicConclusion;

  if (!isPlainObject(publicConclusion)) {
    return validationReject0(['PackSufficiencyTheorem', 'publicConclusion'], 'publicConclusion must be an object', null);
  }

  if (publicConclusion.antecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(['PackSufficiencyTheorem', 'publicConclusion', 'antecedent'], 'public conclusion antecedent mismatch', {
      actual: publicConclusion.antecedent,
    });
  }

  if (publicConclusion.consequent !== 'P = NP') {
    return validationReject0(['PackSufficiencyTheorem', 'publicConclusion', 'consequent'], 'public conclusion consequent mismatch', {
      actual: publicConclusion.consequent,
    });
  }

  for (const field of [
    'conditional',
    'noClaimBeforeAccept',
    'exported',
  ]) {
    if (publicConclusion[field] !== true) {
      return validationReject0(['PackSufficiencyTheorem', 'publicConclusion', field], `publicConclusion must certify ${field}`, {
        actual: publicConclusion[field],
      });
    }
  }

  if (!isPlainObject(theorem.reflection)) {
    return validationReject0(['PackSufficiencyTheorem', 'reflection'], 'reflection certificate must be an object', null);
  }

  for (const field of [
    'exact',
    'publicConclusion',
    'replayable',
  ]) {
    if (theorem.reflection[field] !== true) {
      return validationReject0(['PackSufficiencyTheorem', 'reflection', field], `reflection certificate must certify ${field}`, {
        actual: theorem.reflection[field],
      });
    }
  }

  if (!isPlainObject(theorem.noHiddenMin)) {
    return validationReject0(['PackSufficiencyTheorem', 'noHiddenMin'], 'noHiddenMin metadata must be an object', null);
  }

  if (!arrayContainsAll0(theorem.noHiddenMin.expansionStages, PACK_EXPANSION_STAGES0)) {
    return validationReject0(['PackSufficiencyTheorem', 'noHiddenMin', 'expansionStages'], 'noHiddenMin metadata is missing expansion stages', {
      expected: PACK_EXPANSION_STAGES0,
      actual: theorem.noHiddenMin.expansionStages,
    });
  }

  if (!arrayContainsAll0(theorem.noHiddenMin.forbiddenSymbols, PACK_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['PackSufficiencyTheorem', 'noHiddenMin', 'forbiddenSymbols'], 'noHiddenMin metadata is missing forbidden symbols', {
      expected: PACK_FORBIDDEN_EXEC_SYMBOLS0,
      actual: theorem.noHiddenMin.forbiddenSymbols,
    });
  }

  return validationAccept0({
    kind: 'PackSufficiencyTheorem0NF',
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'PackNoHiddenExecutableMin0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in PCCPack0', hit);
  }

  return validationAccept0({
    kind: 'PackNoOpaqueProof0NF',
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && PACK_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
      return {
        symbol: value,
        path,
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findForbiddenExecutableUse0(value[index], [...path, index], inExecutablePosition);

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
    const nextExecutablePosition =
      inExecutablePosition ||
      EXECUTABLE_KEYS0.has(key) ||
      /exec|call|program|body|operator|operation/i.test(key);

    const hit = findForbiddenExecutableUse0(value[key], [...path, key], nextExecutablePosition);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function findOpaqueProof0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findOpaqueProof0(value[index], [...path, index]);

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
    if (isOpaqueProofMaterialKey0(key)) {
      return {
        key,
        path: [...path, key],
        value: value[key],
      };
    }

    const hit = findOpaqueProof0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function isOpaqueProofMaterialKey0(key) {
  const normalized = String(key).replace(/[_\-\s]/g, '').toLowerCase();

  return (
    normalized === 'opaqueproof' ||
    normalized === 'opaqueproofblob' ||
    normalized === 'proofblob' ||
    normalized === 'trustedblob' ||
    normalized === 'trustedproofblob' ||
    normalized === 'assumeproof'
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

function sameDigest0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.alg === b.alg &&
    a.hex === b.hex
  );
}

function getPiPackSufficiency0(pack) {
  return pack.PiPackSufficiency ?? pack['Πpack'] ?? pack.piPackSufficiency;
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

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}