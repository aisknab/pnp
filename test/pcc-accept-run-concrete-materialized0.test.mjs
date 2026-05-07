import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedGeneratedAcceptRun0,
  makeConcreteMaterializedGeneratedAcceptRun0,
  summarizeConcreteGeneratedAcceptRunChain0,
  writeConcreteMaterializedGeneratedAcceptRunFiles0,
} from '../pcc-accept-run-concrete-materialized0.mjs';

import {
  CheckMaterializedGeneratedAcceptRun0,
} from '../pcc-accept-run-materialized0.mjs';

test('CheckConcreteMaterializedGeneratedAcceptRun0 accepts an accept run over the concrete package chain', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();
  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedGeneratedAcceptRun0NF');
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
  assert.equal(out.NF.hardRowKeyCoverageComplete, true);
  assert.equal(out.NF.hardRoutePriorityComplete, true);
  assert.equal(out.NF.hardProofRefPolicyComplete, true);
  assert.equal(out.NF.hardHashDisciplineComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);
  assert.equal(out.NF.hardReflectionPolicyComplete, true);
  assert.equal(out.NF.hardBoundsPolicyComplete, true);
  assert.equal(out.NF.hardDiagnosticsPolicyComplete, true);

  assert.equal(out.NF.concreteFinalIntegration, true);
  assert.equal(out.NF.finalIntegrationConcreteGlobalProofDAG, true);
  assert.equal(out.NF.finalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationRowFamGCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationUsesGPack, true);
  assert.equal(out.NF.rowFamGUsesGPack, true);
  assert.equal(out.NF.finalTheoremUsesFinalIntegration, true);
  assert.equal(out.NF.rowFamFinalUsesFinalTheorem, true);
  assert.equal(out.NF.finalMatchUsesGPack, true);
  assert.equal(out.NF.satDecisionUsesGPack, true);

  assert.equal(out.NF.concretePCCPack, true);
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
  assert.match(out.NF.concretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);

  assert.equal(out.NF.checkPCCPackexp, true);
  assert.equal(out.NF.checkPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackexpMaterializedRecordPresent, true);
  assert.match(out.NF.checkPCCPackexpMaterializedRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackexpMaterializedRecordMatchesFresh, true);
  assert.equal(out.Ledger.some((entry) => (
    entry.phase === 'CheckPCCPackexpRecord' &&
    entry.status === 'pass'
  )), true);

  assert.equal(out.NF.generatedPCCPackexp, true);
  assert.equal(out.NF.generatedPCCPackexpEnvelopePresent, true);
  assert.match(out.NF.generatedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.generatedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(out.NF.generatedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpPackageMatchesAcceptRun, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordMatchesMaterialized, true);
  assert.equal(out.NF.generatedPCCPackexpRecordMatchesMaterialized, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordPresent, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(out.NF.checkGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordMatchesFresh, true);
  assert.equal(out.Ledger.some((entry) => (
    entry.phase === 'CheckGeneratedPCCPackexpRecord' &&
    entry.status === 'pass'
  )), true);

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
  assert.equal(out.NF.generatedPCCPackexpCodec0IntegerEncoding, 'sign-byte-plus-canonical-natural-no-negative-zero');
  assert.equal(out.NF.generatedPCCPackexpCodec0StringEncoding, 'utf8-nfc-length-prefixed');
  assert.equal(out.NF.generatedPCCPackexpCodec0TopLevelConsumesAllBytes, true);
  assert.equal(out.NF.generatedPCCPackexpCodec0NormalFormSerialization, 'canonical-json-v0');
  assert.equal(out.NF.generatedPCCPackexpCodec0PiBootDigestMatches, true);

  assert.equal(out.NF.generatedPCCPackexpDigest0, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpDigest0Kind, 'Digest0');
  assert.match(out.NF.generatedPCCPackexpDigest0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpDigest0Alg, 'SHA256');
  assert.equal(out.NF.generatedPCCPackexpDigest0Bytes, 'canonical-json-v0');
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
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0BatchCount, 13);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0FamilyCount, 39);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0ConcreteIfaceHash, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount, 0);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0ScaffoldMarkerCount, 0);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteRows0LinkedToPCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0Checker, 'CheckConcreteMaterializedGlobalProofDAG0');
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0NodeCount >= 90, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount, 4);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP, true);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0SchedHash.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount, 0);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0Checker, 'CheckConcreteMaterializedFinalIntegration0');
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAGDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0MaterializedFinalIntegrationDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0GPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0RowFamGDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0FinalTheoremDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0RowFamFinalDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteLinksDigest.hex, /^[0-9a-f]{64}$/);

  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteRows, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0ForbiddenMarkerCount, 0);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal, true);
  assert.equal(out.NF.generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack, true);

  assert.equal(out.Ledger.some((entry) => (
    entry.phase === 'CheckGeneratedPCCPackexp0' &&
    entry.status === 'pass'
  )), true);
  assert.equal(out.Ledger.some((entry) => (
    entry.phase === 'GeneratedPCCPackexpEnvelope' &&
    entry.status === 'pass'
  )), true);

  assert.equal(out.Ledger.some((entry) => (
    entry.phase === 'CheckPCCPackexp0' &&
    entry.status === 'pass'
  )), true);

  assert.equal(out.NF.pccPackLinkedToAcceptRun, true);
  assert.equal(out.NF.rowPackLinkedToPCCPack, true);
  assert.equal(out.NF.localPackagesLinkedToPCCPack, true);
  assert.equal(out.NF.globalFirewallsLinkedToPCCPack, true);
  assert.equal(out.NF.globalProofDAGLinkedToPCCPack, true);

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized generated accept-run accepts the concrete-chain run', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();
  const out = await CheckMaterializedGeneratedAcceptRun0(envelope.GeneratedAcceptRunEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 invokes the concrete PCCPack checker before chain validation', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      HardEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope,
        Coverage: {
          ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope.Coverage,
          noMinCoverageComplete: false,
        },
      },
    },
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkLinkage: false,
    concretePCCPackConfig: {
      checkMaterializedPCCPack: false,
      checkLinkage: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.ConcretePCCPack');
  assert.deepEqual(out.Path, ['GeneratedAcceptRunEnvelope', 'MaterializedPCCPack']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckConcreteMaterializedPCCPack0.concreteCoverage');
  assert.deepEqual(out.Witness.detail.inner.path, ['ConcreteCoverage', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a non-concrete global proof DAG envelope', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      GlobalProofDAGEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.GlobalProofDAGEnvelope,
        kind: 'MaterializedGlobalProofDAG0',
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteGeneratedAcceptRunChain0(
    envelope.GeneratedAcceptRunEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkGeneratedPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'concreteGlobalProofDAG']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects stale ConcreteChain summary', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      RowsEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.RowsEnvelope,
        kind: 'MaterializedRows0',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkGeneratedPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain']);
});

test('writeConcreteMaterializedGeneratedAcceptRunFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-accept-run-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedGeneratedAcceptRunFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.generatedAcceptRunPath,
    result.files.concreteChainPath,
    result.files.checkPCCPackexpRecordPath,
    result.files.generatedPCCPackexpEnvelopePath,
    result.files.checkGeneratedPCCPackexpRecordPath,
    result.files.acceptRunPath,
    result.files.pccPackPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects incomplete concrete HardCheck coverage', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      HardEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope,
        Coverage: {
          ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope.Coverage,
          noMinCoverageComplete: false,
        },
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteGeneratedAcceptRunChain0(
    envelope.GeneratedAcceptRunEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkGeneratedPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects incomplete concrete final-integration coverage', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      FinalIntegrationEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.FinalIntegrationEnvelope,
        ConcreteLinks: {
          ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.FinalIntegrationEnvelope.ConcreteLinks,
          rowFamGCoverageComplete: false,
        },
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteGeneratedAcceptRunChain0(
    envelope.GeneratedAcceptRunEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkGeneratedPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalIntegrationRowFamGCoverageComplete']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects through CheckPCCPackexp0 before chain validation', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      HardEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope,
        Coverage: {
          ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope.Coverage,
          noMinCoverageComplete: false,
        },
      },
    },
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkLinkage: false,
    checkPCCPackexpConfig: {
      checkConcreteMaterializedPCCPack: false,
      checkRecordAlignment: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.CheckPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedAcceptRunEnvelope', 'MaterializedPCCPack']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckPCCPackexp0.concreteCoverage');
  assert.deepEqual(out.Witness.detail.inner.path, ['ConcreteCoverage', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a missing materialized CheckPCCPackexp0 record', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  delete envelope.CheckPCCPackexpRecord;
  envelope.Linkage = {
    ...envelope.Linkage,
    checkPCCPackexpRecordDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.CheckPCCPackexp');
  assert.deepEqual(out.Path, ['CheckPCCPackexpRecord']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a stale materialized CheckPCCPackexp0 record', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.CheckPCCPackexpRecord = {
    ...envelope.CheckPCCPackexpRecord,
    NF: {
      ...envelope.CheckPCCPackexpRecord.NF,
      concreteHardCheck: false,
    },
    nf: {
      ...envelope.CheckPCCPackexpRecord.nf,
      concreteHardCheck: false,
    },
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.CheckPCCPackexp');
  assert.deepEqual(out.Path, ['CheckPCCPackexpRecord', 'Digest']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a missing GeneratedPCCPackexpEnvelope', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  delete envelope.GeneratedPCCPackexpEnvelope;
  envelope.Linkage = {
    ...envelope.Linkage,
    generatedPCCPackexpEnvelopeDigest: undefined,
    generatedPCCPackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp package drift', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedPCCPackexpEnvelope = {
    ...envelope.GeneratedPCCPackexpEnvelope,
    GeneratedPCCPack: {
      ...envelope.GeneratedPCCPackexpEnvelope.GeneratedPCCPack,
      MaterializedPCCPackEnvelope: {
        ...envelope.GeneratedPCCPackexpEnvelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
        PCCPack: {
          ...envelope.GeneratedPCCPackexpEnvelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.PCCPack,
          DriftWitness: 'changed-generated-package',
        },
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedPCCPackexpEnvelopeDigest: undefined,
    generatedPCCPackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkDeterministicGenerator: false,
      checkCheckPCCPackexpRecord: false,
      checkPublicClaimBoundary: false,
      checkLinkage: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'GeneratedPCCPack']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without Boot0 bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkMaterializedBoot0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageBoot0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a missing CheckGeneratedPCCPackexp0 record', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  delete envelope.CheckGeneratedPCCPackexpRecord;
  envelope.Linkage = {
    ...envelope.Linkage,
    checkGeneratedPCCPackexpRecordDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.CheckGeneratedPCCPackexpRecord');
  assert.deepEqual(out.Path, ['CheckGeneratedPCCPackexpRecord']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a stale CheckGeneratedPCCPackexp0 record', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.CheckGeneratedPCCPackexpRecord = {
    ...envelope.CheckGeneratedPCCPackexpRecord,
    NF: {
      ...envelope.CheckGeneratedPCCPackexpRecord.NF,
      generatedPackageBoot0: false,
    },
    nf: {
      ...envelope.CheckGeneratedPCCPackexpRecord.nf,
      generatedPackageBoot0: false,
    },
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.CheckGeneratedPCCPackexpRecord');
  assert.deepEqual(out.Path, ['CheckGeneratedPCCPackexpRecord', 'Digest']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without KernelSeed0 bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkKernelSeed0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageKernelSeed0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without Codec0/Digest0 evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkCodecDigest0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageCodec0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without IfaceDict0/Sched0 evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkIfaceSched0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageIfaceDict0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without ByteLang0 evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkByteLang0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageByteLang0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without BootAudit0/PiBoot evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkBootAuditPiBoot0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageBootAudit0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without ConcreteKBundle bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkConcreteKBundle0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageConcreteKBundle0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without ConcreteHard bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkConcreteHard0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageConcreteHard0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without ConcreteRows bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkConcreteRows0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageConcreteRows0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without ConcreteGlobalProofDAG bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkConcreteGlobalProofDAG0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageConcreteGlobalProofDAG0']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects GeneratedPCCPackexp without ConcreteFinalIntegration bridge evidence', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkConcretePCCPack: false,
    checkPCCPackexp: false,
    checkLinkage: false,
    generatedPCCPackexpConfig: {
      checkConcreteFinalIntegration0: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.GeneratedPCCPackexp');
  assert.deepEqual(out.Path, ['GeneratedPCCPackexpEnvelope', 'NF', 'generatedPackageConcreteFinalIntegration0']);
});
