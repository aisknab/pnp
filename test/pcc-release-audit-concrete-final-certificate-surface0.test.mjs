import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
  summarizeReleaseAudit0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function digestOf0(hex) {
  return {
    alg: 'SHA256',
    bytes: 'canonical-json-v0',
    hex,
  };
}

function makeAcceptedConcreteFinalCertificatePublicStatusRecord0() {
  const nf = {
    kind: 'ConcreteFinalCertificatePublicStatus0NF',
    checker: 'CheckConcreteFinalCertificatePublicStatus0',
    version: 0,
    materializedPath: true,
    syntheticRunAll: false,

    concreteRows: true,
    concreteLocalPackages: true,
    concreteGlobalFirewalls: true,
    concreteGlobalProofDAG: true,

    concreteKBundle: true,
    kBundleKernelRuleCoverageComplete: true,
    kBundleSigmaProofRefsResolve: true,
    kBundleReflectionProofRefsResolve: true,

    concreteHardCheck: true,
    hardCheckerCoverageComplete: true,
    hardRowKeyCoverageComplete: true,
    hardRoutePriorityComplete: true,
    hardProofRefPolicyComplete: true,
    hardHashDisciplineComplete: true,
    hardNoMinCoverageComplete: true,
    hardImportPolicyComplete: true,
    hardReflectionPolicyComplete: true,
    hardBoundsPolicyComplete: true,
    hardDiagnosticsPolicyComplete: true,

    concreteFinalIntegration: true,
    finalIntegrationConcreteGlobalProofDAG: true,
    finalIntegrationGPackFieldCoverageComplete: true,
    finalIntegrationRowFamGCoverageComplete: true,
    finalIntegrationUsesGPack: true,
    rowFamGUsesGPack: true,
    finalTheoremUsesFinalIntegration: true,
    rowFamFinalUsesFinalTheorem: true,
    finalMatchUsesGPack: true,
    satDecisionUsesGPack: true,

    concretePCCPack: true,
    concretePCCPackCoverageDigest: digestOf0('cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc'),
    pccPackPublicConclusionOnlyAfterAcceptRun: true,
    pccPackLinkedToKBundle: true,
    pccPackLinkedToHardCheck: true,
    pccPackLinkedToRows: true,
    pccPackLinkedToLocalPackages: true,
    pccPackLinkedToGlobalFirewalls: true,
    pccPackLinkedToGlobalProofDAG: true,
    pccPackLinkedToGPack: true,
    pccPackLinkedToFinalIntegration: true,
    pccPackLinkedToFinalTheorem: true,
    checkPCCPackexpRecordPresent: true,
    checkPCCPackexpRecordAccepted: true,
    checkPCCPackexpRecordChecker: 'CheckPCCPackexp0',
    checkPCCPackexpRecordDigest: digestOf0('dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd'),
    checkPCCPackexpRecordDigestMatchesNF: true,
    checkPCCPackexpRecordConcretePCCPack: true,
    checkPCCPackexpRecordPccPackDigest: digestOf0('eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee'),
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: true,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: true,
    checkPCCPackexpRecordPublicConclusionNotEmitted: true,
    checkPCCPackexpRecordClaimBoundaryConditional: true,
    generatedPCCPackexpEnvelopePresent: true,
    generatedPCCPackexpEnvelopeDigest: digestOf0('ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'),
    generatedPCCPackexpGenCallGeneratePCCPack: true,
    generatedPCCPackexpCoreOnly: true,
    generatedPCCPackexpExcludesAcceptRun: true,
    generatedPCCPackexpPackageMatchesConcreteRun: true,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: true,
    generatedPCCPackexpCheckRecordAccepted: true,
    generatedPCCPackexpCheckRecordChecker: 'CheckPCCPackexp0',
    generatedPCCPackexpCheckRecordDigest: digestOf0('eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee'),
    generatedPCCPackexpCheckRecordDigestMatchesNF: true,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: true,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: true,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: true,
    checkGeneratedPCCPackexpRecordPresent: true,
    checkGeneratedPCCPackexpRecordAccepted: true,
    checkGeneratedPCCPackexpRecordChecker: 'CheckGeneratedPCCPackexp0',
    checkGeneratedPCCPackexpRecordDigest: digestOf0('1212121212121212121212121212121212121212121212121212121212121212'),
    checkGeneratedPCCPackexpRecordDigestMatchesNF: true,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: true,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: true,

    generatedPCCPackexpBoot0: true,
    generatedPCCPackexpBoot0Accepted: true,
    generatedPCCPackexpBoot0Kind: 'Boot0',
    generatedPCCPackexpBoot0Digest: digestOf0('1313131313131313131313131313131313131313131313131313131313131313'),
    generatedPCCPackexpBoot0CheckDigest: digestOf0('1414141414141414141414141414141414141414141414141414141414141414'),
    generatedPCCPackexpBoot0CanonicalByteDigest: digestOf0('1515151515151515151515151515151515151515151515151515151515151515'),
    generatedPCCPackexpBoot0RowCount: 11,
    generatedPCCPackexpBoot0KernelRuleCount: 16,
    generatedPCCPackexpBoot0JsonMaterialized: true,
    generatedPCCPackexpBoot0NoFixtureMarkers: true,
    generatedPCCPackexpBoot0BootBatchDigest: digestOf0('1616161616161616161616161616161616161616161616161616161616161616'),
    generatedPCCPackexpBoot0BootAuditDigest: digestOf0('1717171717171717171717171717171717171717171717171717171717171717'),
    generatedPCCPackexpBoot0LinkedToPCCPack: true,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap: true,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage: true,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap: true,
    generatedPCCPackexpBoot0B0Accepted: true,
    generatedPCCPackexpBoot0B0Digest: digestOf0('1818181818181818181818181818181818181818181818181818181818181818'),
    generatedPCCPackexpBoot0B0CoverageDigest: digestOf0('1919191919191919191919191919191919191919191919191919191919191919'),
    generatedPCCPackexpBoot0B0FamilyCount: 12,
    generatedPCCPackexpBoot0B0RequiredFamilyCount: 12,
    generatedPCCPackexpBoot0B0Families: [
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
    ],
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent: true,
    generatedPCCPackexpBoot0B0CoversIface: true,
    generatedPCCPackexpBoot0B0CoversSched: true,
    generatedPCCPackexpBoot0B0CoversNF: true,
    generatedPCCPackexpBoot0B0CoversTruthEval: true,
    generatedPCCPackexpBoot0B0CoversRel: true,
    generatedPCCPackexpBoot0B0CoversCharge: true,
    generatedPCCPackexpBoot0B0CoversObl: true,
    generatedPCCPackexpBoot0B0CoversArith: true,
    generatedPCCPackexpBoot0B0CoversMode: true,
    generatedPCCPackexpBoot0B0CoversRoute: true,
    generatedPCCPackexpBoot0B0CoversHash: true,
    generatedPCCPackexpBoot0B0CoversImport: true,
    generatedPCCPackexpKernelSeed0: true,
    generatedPCCPackexpKernelSeed0Accepted: true,
    generatedPCCPackexpKernelSeed0Kind: 'KernelSeed0',
    generatedPCCPackexpKernelSeed0Digest: digestOf0('2020202020202020202020202020202020202020202020202020202020202020'),
    generatedPCCPackexpKernelSeed0RuleCount: 16,
    generatedPCCPackexpKernelSeed0RequiredRuleCount: 16,
    generatedPCCPackexpKernelSeed0Rules: [
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
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent: true,
    generatedPCCPackexpKernelSeed0HasEq: true,
    generatedPCCPackexpKernelSeed0HasSubst: true,
    generatedPCCPackexpKernelSeed0HasRecord: true,
    generatedPCCPackexpKernelSeed0HasDAGInd: true,
    generatedPCCPackexpKernelSeed0HasLedgerInd: true,
    generatedPCCPackexpKernelSeed0HasOblTopoInd: true,
    generatedPCCPackexpKernelSeed0HasTraceInd: true,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust: true,
    generatedPCCPackexpKernelSeed0HasDPInd: true,
    generatedPCCPackexpKernelSeed0HasHall: true,
    generatedPCCPackexpKernelSeed0HasRankInd: true,
    generatedPCCPackexpKernelSeed0HasMinCounterexample: true,
    generatedPCCPackexpKernelSeed0HasIntArith: true,
    generatedPCCPackexpKernelSeed0HasTransport: true,
    generatedPCCPackexpKernelSeed0HasTruthVec: true,
    generatedPCCPackexpKernelSeed0HasFiniteRel: true,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount: 5,
    generatedPCCPackexpKernelSeed0ProofNodeKinds: [
      'PrimitiveRule',
      'SigmaInstance',
      'ReflectionInstance',
      'RowProof',
      'PackageTheorem',
    ],
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: true,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: true,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: true,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent: true,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches: true,
    generatedPCCPackexpCodec0: true,
    generatedPCCPackexpCodec0Accepted: true,
    generatedPCCPackexpCodec0Kind: 'Codec0',
    generatedPCCPackexpCodec0Digest: digestOf0('2323232323232323232323232323232323232323232323232323232323232323'),
    generatedPCCPackexpCodec0Canonical: true,
    generatedPCCPackexpCodec0NaturalEncoding: 'u32be-length-shortest-big-endian-magnitude',
    generatedPCCPackexpCodec0NaturalEncodingCanonical: true,
    generatedPCCPackexpCodec0IntegerEncoding: 'sign-byte-plus-canonical-natural-no-negative-zero',
    generatedPCCPackexpCodec0IntegerEncodingCanonical: true,
    generatedPCCPackexpCodec0StringEncoding: 'utf8-nfc-length-prefixed',
    generatedPCCPackexpCodec0StringEncodingCanonical: true,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes: true,
    generatedPCCPackexpCodec0NormalFormSerialization: 'canonical-json-v0',
    generatedPCCPackexpCodec0NormalFormSerializationCanonical: true,
    generatedPCCPackexpCodec0PiBootDigestMatches: true,

    generatedPCCPackexpDigest0: true,
    generatedPCCPackexpDigest0Accepted: true,
    generatedPCCPackexpDigest0Kind: 'Digest0',
    generatedPCCPackexpDigest0Digest: digestOf0('2424242424242424242424242424242424242424242424242424242424242424'),
    generatedPCCPackexpDigest0Alg: 'SHA256',
    generatedPCCPackexpDigest0AlgSHA256: true,
    generatedPCCPackexpDigest0Bytes: 'canonical-json-v0',
    generatedPCCPackexpDigest0BytesCanonicalJson: true,
    generatedPCCPackexpDigest0EqualityNotObjectEquality: true,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: true,
    generatedPCCPackexpDigest0PiBootDigestMatches: true,
    generatedPCCPackexpIfaceDict0: true,
    generatedPCCPackexpIfaceDict0Accepted: true,
    generatedPCCPackexpIfaceDict0Kind: 'IfaceDict0',
    generatedPCCPackexpIfaceDict0Digest: digestOf0('2525252525252525252525252525252525252525252525252525252525252525'),
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount: 11,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: true,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols: true,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent: true,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent: true,
    generatedPCCPackexpIfaceDict0RouteTokensPresent: true,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches: true,

    generatedPCCPackexpSched0: true,
    generatedPCCPackexpSched0Accepted: true,
    generatedPCCPackexpSched0Kind: 'Sched0',
    generatedPCCPackexpSched0Digest: digestOf0('2626262626262626262626262626262626262626262626262626262626262626'),
    generatedPCCPackexpSched0CoreMatchesExpected: true,
    generatedPCCPackexpSched0CoreB0: 64,
    generatedPCCPackexpSched0CoreK0: 512,
    generatedPCCPackexpSched0CoreR0: 64,
    generatedPCCPackexpSched0CoreH0: 128,
    generatedPCCPackexpSched0CoreO0: 64,
    generatedPCCPackexpSched0CoreRel0: 16,
    generatedPCCPackexpSched0ScaleFactorsPresent: true,
    generatedPCCPackexpSched0SelectorBoundsPresent: true,
    generatedPCCPackexpSched0SelectorBoundBH: 8,
    generatedPCCPackexpSched0SelectorBoundBTheta: 12,
    generatedPCCPackexpSched0PolynomialExponent: 36,
    generatedPCCPackexpSched0PiBootDigestMatches: true,
    generatedPCCPackexpByteLang0: true,
    generatedPCCPackexpByteLang0Accepted: true,
    generatedPCCPackexpByteLang0Kind: 'ByteLang0',
    generatedPCCPackexpByteLang0Digest: digestOf0('2727272727272727272727272727272727272727272727272727272727272727'),
    generatedPCCPackexpByteLang0TagCount: 12,
    generatedPCCPackexpByteLang0TagsUnique: true,
    generatedPCCPackexpByteLang0RequiredTagsPresent: true,
    generatedPCCPackexpByteLang0SortCount: 8,
    generatedPCCPackexpByteLang0RequiredSortsPresent: true,
    generatedPCCPackexpByteLang0ConstructorCount: 7,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent: true,
    generatedPCCPackexpByteLang0RecordCount: 9,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent: true,
    generatedPCCPackexpByteLang0PiBootDigestMatches: true,
    generatedPCCPackexpBootAudit0: true,
    generatedPCCPackexpBootAudit0Accepted: true,
    generatedPCCPackexpBootAudit0Checker: 'CheckVerifierFrag0',
    generatedPCCPackexpBootAudit0Digest: digestOf0('2828282828282828282828282828282828282828282828282828282828282828'),
    generatedPCCPackexpBootAudit0DigestMatchesNF: true,
    generatedPCCPackexpBootAudit0NFKind: 'VerifierFrag0AuditNF',
    generatedPCCPackexpBootAudit0SuiteId: 'boot0.materialized.audit',
    generatedPCCPackexpBootAudit0CaseCount: 3,
    generatedPCCPackexpBootAudit0PositiveCount: 1,
    generatedPCCPackexpBootAudit0NegativeCount: 2,
    generatedPCCPackexpBootAudit0CoversB0Accept: true,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject: true,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: true,

    generatedPCCPackexpPiBoot0: true,
    generatedPCCPackexpPiBoot0Accepted: true,
    generatedPCCPackexpPiBoot0Kind: 'PiBoot0',
    generatedPCCPackexpPiBoot0Digest: digestOf0('2929292929292929292929292929292929292929292929292929292929292929'),
    generatedPCCPackexpPiBoot0Materialized: true,
    generatedPCCPackexpPiBoot0ExternalJson: true,
    generatedPCCPackexpPiBoot0RefCount: 8,
    generatedPCCPackexpPiBoot0AllBootRefsPresent: true,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects: true,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0: true,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0: true,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0: true,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0: true,
    generatedPCCPackexpPiBoot0RefsIncludeSched0: true,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0: true,
    generatedPCCPackexpPiBoot0RefsIncludeB0: true,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0: true,

    finalCertificateUsesConcreteAcceptRun: true,
    statusUsesConcreteFinalCertificate: true,
    publicStatusCertificateDigestMatchesConcrete: true,
    publicStatusFinalVerdictDigestMatchesConcrete: true,
    publicStatusAcceptRunDigestMatchesConcrete: true,
    publicStatusPccPackDigestMatchesConcrete: true,

    status: 'accepted',
    verdict: 'accept',
    publicConclusionEmitted: true,
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },

    certificateDigest: digestOf0('1111111111111111111111111111111111111111111111111111111111111111'),
    finalVerdictDigest: digestOf0('2222222222222222222222222222222222222222222222222222222222222222'),
    acceptRunDigest: digestOf0('3333333333333333333333333333333333333333333333333333333333333333'),
    pccPackDigest: digestOf0('4444444444444444444444444444444444444444444444444444444444444444'),

    canonicalByteRoots: {
      coreBytesDigest: digestOf0('5555555555555555555555555555555555555555555555555555555555555555'),
      packBytesDigest: digestOf0('6666666666666666666666666666666666666666666666666666666666666666'),
    },

    acceptanceTranscript: {
      transcriptDigest: digestOf0('7777777777777777777777777777777777777777777777777777777777777777'),
      auditLogDigest: digestOf0('8888888888888888888888888888888888888888888888888888888888888888'),
      rejectLogCount: 0,
    },

    releaseAuditAttached: false,
    releaseAuditDigest: null,
    releaseAuditStatus: 'not-attached-to-this-materialized-certificate-yet',

    concreteFinalCertificateEnvelopeDigest: digestOf0('9999999999999999999999999999999999999999999999999999999999999999'),
    finalCertificatePublicStatusEnvelopeDigest: digestOf0('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'),
    concreteChainDigest: digestOf0('bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb'),
    linkageDigest: null,

    syntheticMarkerCount: 0,
    forbiddenMarkerCount: 0,
    allowSyntheticScaffoldMarker: true,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckConcreteFinalCertificatePublicStatus0',
    version: 0,
    NF: nf,
    Digest: digest,
    Ledger: [],
    nf,
    digest,
    ledger: [],
  };
}

test('CheckReleaseAudit0 reports the concrete final-certificate public-status gate summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => (
      makeAcceptedConcreteFinalCertificatePublicStatusRecord0()
    ),
  }));

  assert.equal(out.tag, 'accept', JSON.stringify({
    coord: out.Coord ?? out.coord ?? null,
    path: out.Path ?? out.path ?? null,
    witness: out.Witness ?? out.witness ?? null,
  }, null, 2));

  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGate, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateStatus, 'accepted');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateVerdict, 'accept');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePublicConclusionEmitted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteRows, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteLocalPackages, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteKBundle, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteHardCheck, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateHardImportPolicyComplete, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteFinalIntegration, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcretePCCPack, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToRows, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind, 'Boot0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount > 0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount > 0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount, 12);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount, 12);
  assert.deepEqual(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families, [
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
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind, 'KernelSeed0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount, 16);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount, 16);
  assert.deepEqual(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules, [
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
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount, 5);
  assert.deepEqual(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds, [
    'PrimitiveRule',
    'SigmaInstance',
    'ReflectionInstance',
    'RowProof',
    'PackageTheorem',
  ]);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind, 'Codec0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding, 'u32be-length-shortest-big-endian-magnitude');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding, 'sign-byte-plus-canonical-natural-no-negative-zero');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding, 'utf8-nfc-length-prefixed');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization, 'canonical-json-v0');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind, 'Digest0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg, 'SHA256');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes, 'canonical-json-v0');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind, 'IfaceDict0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount >= 11, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind, 'Sched0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0, 64);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0, 512);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0, 64);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0, 128);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0, 64);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0, 16);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH, 8);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta, 12);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent, 36);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind, 'ByteLang0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount >= 12, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount >= 8, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount >= 7, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount >= 9, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker, 'CheckVerifierFrag0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind, 'VerifierFrag0AuditNF');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId, 'boot0.materialized.audit');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount, 3);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount, 1);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount, 2);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind, 'PiBoot0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount, 8);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate, true);

  const summary = summarizeReleaseAudit0(out);

  assert.equal(summary.tag, 'accept');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateSummary.status, 'accepted');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteRows, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteKBundle, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteHardCheck, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteFinalIntegration, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcretePCCPack, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToRows, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker, 'CheckPCCPackexp0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind, 'Boot0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount > 0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount > 0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount, 12);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount, 12);
  assert.deepEqual(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families, [
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
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind, 'KernelSeed0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount, 16);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount, 16);
  assert.deepEqual(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules, [
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
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount, 5);
  assert.deepEqual(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds, [
    'PrimitiveRule',
    'SigmaInstance',
    'ReflectionInstance',
    'RowProof',
    'PackageTheorem',
  ]);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind, 'Codec0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding, 'u32be-length-shortest-big-endian-magnitude');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding, 'sign-byte-plus-canonical-natural-no-negative-zero');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding, 'utf8-nfc-length-prefixed');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization, 'canonical-json-v0');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind, 'Digest0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg, 'SHA256');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes, 'canonical-json-v0');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind, 'IfaceDict0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount >= 11, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind, 'Sched0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0, 64);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0, 512);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0, 64);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0, 128);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0, 64);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0, 16);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH, 8);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta, 12);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent, 36);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind, 'ByteLang0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount >= 12, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount >= 8, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount >= 7, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount >= 9, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker, 'CheckVerifierFrag0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind, 'VerifierFrag0AuditNF');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId, 'boot0.materialized.audit');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount, 3);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount, 1);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount, 2);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind, 'PiBoot0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount, 8);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateSummary.publicConclusion.consequent, 'P = NP');
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without concrete rows', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    concreteRows: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, ['concreteFinalCertificatePublicStatusGate', 'NF', 'concreteRows']);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without concrete PCCPack evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    concretePCCPack: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, ['concreteFinalCertificatePublicStatusGate', 'NF', 'concretePCCPack']);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without CheckPCCPackexp0 evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    checkPCCPackexpRecordPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'checkPCCPackexpRecordPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without GeneratedPCCPackexp0 evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpEnvelopePresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpEnvelopePresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without CheckGeneratedPCCPackexp0 record evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    checkGeneratedPCCPackexpRecordPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'checkGeneratedPCCPackexpRecordPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without Boot0 bridge evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpBoot0: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpBoot0',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without B0 row-family coverage', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpBoot0B0CoversTruthEval: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpBoot0B0CoversTruthEval',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without KernelSeed0 primitive rule evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpKernelSeed0HasHall: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpKernelSeed0HasHall',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate with unsafe KernelSeed0 proof refs', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without canonical Codec0 evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpCodec0NaturalEncodingCanonical: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpCodec0NaturalEncodingCanonical',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate with Digest0 object-equality misuse evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpDigest0EqualityNotObjectEquality: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpDigest0EqualityNotObjectEquality',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without IfaceDict0 route-token evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpIfaceDict0RouteTokensPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpIfaceDict0RouteTokensPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate with stale Sched0 evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpSched0SelectorBoundsPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpSched0SelectorBoundsPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without ByteLang0 tag uniqueness evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpByteLang0TagsUnique: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpByteLang0TagsUnique',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without ByteLang0 record-arity evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpByteLang0RequiredRecordAritiesPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without BootAudit0 audit evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without PiBoot reference evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpPiBoot0RefsMatchBootObjects',
  ]);
});
