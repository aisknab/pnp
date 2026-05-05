import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

import {
  CheckConcreteFinalCertificatePublicStatus0,
  makeConcreteFinalCertificatePublicStatus0,
  summarizeConcreteFinalCertificatePublicStatusChain0,
  writeConcreteFinalCertificatePublicStatusFiles0,
} from '../pcc-final-certificate-public-status-concrete0.mjs';

import {
  CheckFinalCertificatePublicStatus0,
} from '../pcc-final-certificate-public-status0.mjs';

test('CheckConcreteFinalCertificatePublicStatus0 accepts public status over concrete final certificate', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();
  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.NF.kind, 'ConcreteFinalCertificatePublicStatus0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);

  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.hardCheckerCoverageComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);

  assert.equal(out.NF.concreteFinalIntegration, true);
  assert.equal(out.NF.finalIntegrationConcreteGlobalProofDAG, true);
  assert.equal(out.NF.finalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationRowFamGCoverageComplete, true);

  assert.equal(out.NF.concretePCCPack, true);
  assert.match(out.NF.concretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.pccPackPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.pccPackLinkedToKBundle, true);
  assert.equal(out.NF.pccPackLinkedToHardCheck, true);
  assert.equal(out.NF.pccPackLinkedToRows, true);
  assert.equal(out.NF.pccPackLinkedToLocalPackages, true);
  assert.equal(out.NF.pccPackLinkedToGlobalFirewalls, true);
  assert.equal(out.NF.pccPackLinkedToGlobalProofDAG, true);
  assert.equal(out.NF.pccPackLinkedToGPack, true);
  assert.equal(out.NF.pccPackLinkedToFinalIntegration, true);
  assert.equal(out.NF.pccPackLinkedToFinalTheorem, true);

  assert.equal(out.NF.checkPCCPackexpRecordPresent, true);
  assert.equal(out.NF.checkPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.checkPCCPackexpRecordConcretePCCPack, true);
  assert.match(out.NF.checkPCCPackexpRecordPccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun, true);
  assert.equal(out.NF.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.checkPCCPackexpRecordPublicConclusionNotEmitted, true);
  assert.equal(out.NF.checkPCCPackexpRecordClaimBoundaryConditional, true);

  assert.equal(out.NF.generatedPCCPackexpEnvelopePresent, true);
  assert.match(out.NF.generatedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpGenCallGeneratePCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpCoreOnly, true);
  assert.equal(out.NF.generatedPCCPackexpExcludesAcceptRun, true);
  assert.equal(out.NF.generatedPCCPackexpPackageMatchesConcreteRun, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordMatchesConcreteRun, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordAccepted, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.generatedPCCPackexpCheckRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordDigestMatchesNF, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordClaimBoundaryConditional, true);
  assert.equal(out.NF.generatedPCCPackexpLinkageGeneratedPackageDigestMatches, true);
  assert.equal(out.NF.generatedPCCPackexpLinkageCheckRecordDigestMatches, true);

  assert.equal(out.NF.checkGeneratedPCCPackexpRecordPresent, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(out.NF.checkGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope, true);

  assert.equal(out.NF.generatedPCCPackexpBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0Kind, 'Boot0');
  assert.match(out.NF.generatedPCCPackexpBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBoot0RowCount > 0, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0KernelRuleCount > 0, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0JsonMaterialized, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0NoFixtureMarkers, true);
  assert.match(out.NF.generatedPCCPackexpBoot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBoot0LinkedToPCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0LinkedToCoreDigestMap, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap, true);

  assert.equal(out.NF.generatedPCCPackexpBoot0B0Accepted, true);
  assert.match(out.NF.generatedPCCPackexpBoot0B0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0B0CoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0FamilyCount, 12);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0RequiredFamilyCount, 12);
  assert.deepEqual(out.NF.generatedPCCPackexpBoot0B0Families, [
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
  assert.equal(out.NF.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversIface, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversSched, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversNF, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversTruthEval, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversRel, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversCharge, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversObl, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversArith, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversMode, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversRoute, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversHash, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversImport, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0Kind, 'KernelSeed0');
  assert.match(out.NF.generatedPCCPackexpKernelSeed0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0RuleCount, 16);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0RequiredRuleCount, 16);
  assert.deepEqual(out.NF.generatedPCCPackexpKernelSeed0Rules, [
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
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasEq, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasSubst, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasRecord, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasDAGInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasLedgerInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasOblTopoInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasTraceInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasFiniteExhaust, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasDPInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasHall, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasRankInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasMinCounterexample, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasIntArith, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasTransport, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasTruthVec, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasFiniteRel, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofNodeKindCount, 5);
  assert.deepEqual(out.NF.generatedPCCPackexpKernelSeed0ProofNodeKinds, [
    'PrimitiveRule',
    'SigmaInstance',
    'ReflectionInstance',
    'RowProof',
    'PackageTheorem',
  ]);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0Kind, 'Codec0');
  assert.match(out.NF.generatedPCCPackexpCodec0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpCodec0Canonical, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0NaturalEncoding, 'u32be-length-shortest-big-endian-magnitude');
  assert.equal(out.NF.generatedPCCPackexpCodec0NaturalEncodingCanonical, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0IntegerEncoding, 'sign-byte-plus-canonical-natural-no-negative-zero');
  assert.equal(out.NF.generatedPCCPackexpCodec0IntegerEncodingCanonical, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0StringEncoding, 'utf8-nfc-length-prefixed');
  assert.equal(out.NF.generatedPCCPackexpCodec0StringEncodingCanonical, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0TopLevelConsumesAllBytes, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0NormalFormSerialization, 'canonical-json-v0');
  assert.equal(out.NF.generatedPCCPackexpCodec0NormalFormSerializationCanonical, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0PiBootDigestMatches, true);

  assert.equal(out.NF.generatedPCCPackexpDigest0, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0Kind, 'Digest0');
  assert.match(out.NF.generatedPCCPackexpDigest0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpDigest0Alg, 'SHA256');
  assert.equal(out.NF.generatedPCCPackexpDigest0AlgSHA256, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0Bytes, 'canonical-json-v0');
  assert.equal(out.NF.generatedPCCPackexpDigest0BytesCanonicalJson, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0EqualityNotObjectEquality, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0Kind, 'IfaceDict0');
  assert.match(out.NF.generatedPCCPackexpIfaceDict0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount >= 11, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0PublicConstructorsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0CriticalKindsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0RouteTokensPresent, true);
  assert.equal(out.NF.generatedPCCPackexpIfaceDict0PiBootDigestMatches, true);

  assert.equal(out.NF.generatedPCCPackexpSched0, true);
  assert.equal(out.NF.generatedPCCPackexpSched0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpSched0Kind, 'Sched0');
  assert.match(out.NF.generatedPCCPackexpSched0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreMatchesExpected, true);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreB0, 64);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreK0, 512);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreR0, 64);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreH0, 128);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreO0, 64);
  assert.equal(out.NF.generatedPCCPackexpSched0CoreRel0, 16);
  assert.equal(out.NF.generatedPCCPackexpSched0ScaleFactorsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpSched0SelectorBoundsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpSched0SelectorBoundBH, 8);
  assert.equal(out.NF.generatedPCCPackexpSched0SelectorBoundBTheta, 12);
  assert.equal(out.NF.generatedPCCPackexpSched0PolynomialExponent, 36);
  assert.equal(out.NF.generatedPCCPackexpSched0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0Kind, 'ByteLang0');
  assert.match(out.NF.generatedPCCPackexpByteLang0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpByteLang0TagCount >= 12, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0TagsUnique, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0RequiredTagsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0SortCount >= 8, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0RequiredSortsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0ConstructorCount >= 7, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0RequiredConstructorsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0RecordCount >= 9, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent, true);
  assert.equal(out.NF.generatedPCCPackexpByteLang0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0, true);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0Checker, 'CheckVerifierFrag0');
  assert.match(out.NF.generatedPCCPackexpBootAudit0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0DigestMatchesNF, true);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0NFKind, 'VerifierFrag0AuditNF');
  assert.equal(out.NF.generatedPCCPackexpBootAudit0SuiteId, 'boot0.materialized.audit');
  assert.equal(out.NF.generatedPCCPackexpBootAudit0CaseCount, 3);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0PositiveCount, 1);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0NegativeCount, 2);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0CoversB0Accept, true);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject, true);
  assert.equal(out.NF.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject, true);

  assert.equal(out.NF.generatedPCCPackexpPiBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0Kind, 'PiBoot0');
  assert.match(out.NF.generatedPCCPackexpPiBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0Materialized, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0ExternalJson, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefCount, 8);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0AllBootRefsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsMatchBootObjects, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeByteLang0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeCodec0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeDigest0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeSched0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeB0, true);
  assert.equal(out.NF.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0Checker, 'CheckConcreteMaterializedKBundle0');
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0BootDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0KImplDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0K0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0SigmaDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0ReflectionDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteKBundle0ProofInventoryDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0KernelRuleCount, 16);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0ConformanceNodeCount, 16);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0SigmaTheoremCount, 2);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0ReflectionCount >= 5, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0Checker, 'CheckConcreteMaterializedHard0');
  assert.match(out.NF.generatedPCCPackexpConcreteHard0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteHard0MaterializedHardDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteHard0HardCheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteHard0CoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0CheckerCount, 13);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0CheckerCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0RowKeyFieldCount, 17);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0RowKeyCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0RoutePriorityComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0ProofRefPolicyComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0HashDisciplineComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0NoMinCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0ForbiddenSymbolCount, 11);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0ImportPolicyComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount, 6);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0ReflectionPolicyComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0BoundsPolicyComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteHard0LinkedToPCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0Checker, 'CheckConcreteMaterializedRows0');
  assert.match(out.NF.generatedPCCPackexpConcreteRows0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteRows0RowPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteRows0RowPackObjectDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteRows0BootDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteRows0IfaceHash.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteRows0SchedHash.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0RowCount, 39);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0RowCountComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0BatchCount, 13);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0BatchCountComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0FamilyCount, 39);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0FamilyCountComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0ConcreteIfaceHash, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount, 0);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0ScaffoldMarkerCount, 0);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0NoScaffoldMarkers, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0LinkedToPCCPack, true);

  assert.equal(out.NF.statusUsesConcreteFinalCertificate, true);
  assert.equal(out.NF.publicStatusCertificateDigestMatchesConcrete, true);
  assert.equal(out.NF.publicStatusFinalVerdictDigestMatchesConcrete, true);
  assert.equal(out.NF.publicStatusAcceptRunDigestMatchesConcrete, true);
  assert.equal(out.NF.publicStatusPccPackDigestMatchesConcrete, true);
  assert.equal(out.NF.publicConclusionMatchesCertificate, true);
  assert.equal(out.NF.publicConclusionMatchesFinalVerdict, true);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner final-certificate public-status checker accepts the concrete status envelope', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();
  const out = await CheckFinalCertificatePublicStatus0(envelope.FinalCertificatePublicStatusEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.NF.kind, 'FinalCertificatePublicStatus0NF');
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale concrete public-status chain summary', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteChain = {
    ...envelope.ConcreteChain,
    statusUsesConcreteFinalCertificate: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects status envelope not tied to concrete final certificate', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    FinalCertificateEnvelope: {
      ...envelope.FinalCertificatePublicStatusEnvelope.FinalCertificateEnvelope,
      Certificate: {
        ...envelope.FinalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.Certificate,
        status: 'drifted',
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificatePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'statusUsesConcreteFinalCertificate']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects concrete PCCPack component drift', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .PCCPack = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .PCCPack,
      HardCheck: {
        ...envelope.ConcreteFinalCertificateEnvelope
          .ConcreteGeneratedAcceptRunEnvelope
          .GeneratedAcceptRunEnvelope
          .MaterializedPCCPack
          .PCCPack
          .HardCheck,
        DriftWitness: 'changed-hard-check',
      },
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'concretePCCPack']);
});

test('CheckConcreteFinalCertificatePublicStatus0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    PublicStatus: {
      ...envelope.FinalCertificatePublicStatusEnvelope.PublicStatus,
      ScaffoldWitness: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificatePublicStatusEnvelopeDigest: undefined,
    publicStatusDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkFinalCertificatePublicStatus: false,
    checkConcreteChain: false,
    checkLinkage: false,
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteFinalCertificatePublicStatusFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-public-status-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteFinalCertificatePublicStatusFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.concreteFinalCertificatePath,
    result.files.finalCertificatePublicStatusPath,
    result.files.publicStatusPath,
    result.files.concreteChainPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects incomplete concrete HardCheck coverage', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .HardEnvelope
    .Coverage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .HardEnvelope
        .Coverage,
      noMinCoverageComplete: false,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects incomplete concrete final-integration coverage', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .FinalIntegrationEnvelope
    .ConcreteLinks = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .FinalIntegrationEnvelope
        .ConcreteLinks,
      rowFamGCoverageComplete: false,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalIntegrationRowFamGCoverageComplete']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects missing materialized CheckPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  delete envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckPCCPackexpRecord;

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .Linkage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .Linkage,
      checkPCCPackexpRecordDigest: undefined,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'checkPCCPackexpRecordPresent']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects missing GeneratedPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  delete envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedPCCPackexpEnvelope;

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .Linkage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .Linkage,
      generatedPCCPackexpEnvelopeDigest: undefined,
      generatedPCCPackDigest: undefined,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpEnvelopePresent']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects missing CheckGeneratedPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  delete envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .Linkage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .Linkage,
      checkGeneratedPCCPackexpRecordDigest: undefined,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'checkGeneratedPCCPackexpRecordPresent']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale B0 row-family evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    boot0B0CoversTruthEval: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpBoot0B0CoversTruthEval']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale KernelSeed0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    kernelSeed0HasHall: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpKernelSeed0HasHall']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale Codec0/Digest0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    digest0EqualityNotObjectEquality: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpDigest0EqualityNotObjectEquality']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale IfaceDict0/Sched0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    sched0CoreMatchesExpected: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpSched0CoreMatchesExpected']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale ByteLang0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    byteLang0TagsUnique: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpByteLang0TagsUnique']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale PiBoot evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    piBoot0RefsMatchBootObjects: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpPiBoot0RefsMatchBootObjects']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale concrete KBundle evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    concreteKBundle0NoOpaqueProofRefs: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale concrete HardCheck evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    concreteHard0ProofRefPolicyComplete: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpConcreteHard0ProofRefPolicyComplete']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale concrete RowPack evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  const record = envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  const nf = {
    ...record.NF,
    concreteRows0LinkedToPCCPack: false,
  };

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord = {
      ...record,
      NF: nf,
      nf,
      Digest: digestCanonical0(nf),
      digest: digestCanonical0(nf),
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpConcreteRows0LinkedToPCCPack']);
});
