import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import os from 'node:os';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedPublicStatusRoundtrip0,
} from './pcc-materialized-public-status-roundtrip0.mjs';

import {
  CheckRunAll0,
  RUNALL_CHECKER_COVERAGE0,
  RUNALL_PUBLIC_CONCLUSION0,
  RunAll0,
  makeSyntheticRunAllInput0,
} from './pcc-runall0.mjs';

import {
  CheckFinalCertificatePublicStatus0,
  makeFinalCertificatePublicStatus0,
  writeFinalCertificatePublicStatusFiles0,
} from './pcc-final-certificate-public-status0.mjs';

import {
  CheckConcreteFinalCertificatePublicStatus0,
  makeConcreteFinalCertificatePublicStatus0,
  writeConcreteFinalCertificatePublicStatusFiles0,
} from './pcc-final-certificate-public-status-concrete0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const RELEASE_AUDIT_REQUIRED_MODULES0 = Object.freeze([
  'index.mjs',
  'pcc-core.mjs',
  'pcc-verifier-frag0.mjs',
  'pcc-boot0.mjs',
  'pcc-kimpl0.mjs',
  'pcc-hard0.mjs',
  'pcc-rows0.mjs',
  'pcc-global-proof-dag0.mjs',
  'pcc-local-packages0.mjs',
  'pcc-global-firewalls0.mjs',
  'pcc-gpack0.mjs',
  'pcc-final-framework0.mjs',
  'pcc-final0.mjs',
  'pcc-pack-sufficiency0.mjs',
  'pcc-accept-run0.mjs',
  'pcc-integrated-pipeline0.mjs',
  'pcc-runall0.mjs',
  'pcc-release-audit0.mjs',
  'bin/runall0.mjs',
  'bin/release-audit0.mjs',
  'pcc-materialized0.mjs',
  'pcc-fixture-digests0.mjs',
  'pcc-synthetic-marker-inventory0.mjs',
  'pcc-materialized-pack0.mjs',
  'pcc-materialized-loader0.mjs',
  'bin/check-materialized-shell0.mjs',     
  'pcc-materialized-core-extractor0.mjs',
  'pcc-materialized-phase-manifest0.mjs',
  'pcc-materialized-artefact-inventory0.mjs',
  'pcc-materialized-artefact-deps0.mjs',
  'pcc-materialized-proof-refs0.mjs',
  'pcc-materialized-bounds0.mjs',
  'pcc-materialized-no-hidden-min0.mjs',
  'pcc-materialized-imports0.mjs',
  'pcc-materialized-aggregate0.mjs',
  'bin/check-materialized-aggregate0.mjs',
  'pcc-materialized-acceptance-bridge0.mjs',
  'bin/check-materialized-acceptance-bridge0.mjs',
  'pcc-materialized-fixture-writer0.mjs',
  'bin/write-materialized-fixtures0.mjs',
  'pcc-materialized-fixture-roundtrip0.mjs',
  'bin/check-materialized-fixture-roundtrip0.mjs',
  'pcc-materialized-digest-resolver0.mjs',
  'bin/resolve-materialized-digest0.mjs',
  'pcc-materialized-accept-run0.mjs',
  'bin/check-materialized-accept-run0.mjs',
  'pcc-materialized-accept-run-fixtures0.mjs',
  'bin/write-materialized-accept-run-fixtures0.mjs',
  'pcc-materialized-final-verdict0.mjs',
  'bin/check-materialized-final-verdict0.mjs',
  'pcc-materialized-final-run-fixtures0.mjs',
  'bin/write-materialized-final-run-fixtures0.mjs',
  'pcc-materialized-final-run-roundtrip0.mjs',
  'bin/check-materialized-final-run-roundtrip0.mjs',
  'pcc-materialized-public-status0.mjs',
  'bin/check-materialized-public-status0.mjs',
  'pcc-materialized-public-status-roundtrip0.mjs',
  'bin/check-materialized-public-status-roundtrip0.mjs',
  'pcc-boot-materialized0.mjs',
  'bin/write-materialized-boot0.mjs',
  'pcc-k-materialized0.mjs',
  'bin/write-materialized-kbundle0.mjs',
  'pcc-global-proof-dag-materialized0.mjs',
  'bin/write-materialized-global-proof-dag0.mjs',
  'pcc-global-proof-dag-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-global-proof-dag0.mjs',
  'pcc-hard-materialized0.mjs',
  'bin/write-materialized-hard0.mjs',
  'pcc-rows-materialized0.mjs',
  'bin/write-materialized-rows0.mjs',
  'pcc-rows-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-rows0.mjs',
  'pcc-local-packages-materialized0.mjs',
  'bin/write-materialized-local-packages0.mjs',
  'pcc-local-packages-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-local-packages0.mjs',
  'pcc-global-firewalls-materialized0.mjs',
  'bin/write-materialized-global-firewalls0.mjs',
  'pcc-global-firewalls-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-global-firewalls0.mjs',
  'pcc-final-integration-materialized0.mjs',
  'bin/write-materialized-final-integration0.mjs',
  'pcc-pack-materialized0.mjs',
  'bin/write-materialized-pcc-pack0.mjs',
  'pcc-accept-run-materialized0.mjs',
  'bin/write-materialized-accept-run0.mjs',
  'pcc-accept-run-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-accept-run0.mjs',
  'pcc-final-certificate-materialized0.mjs',
  'bin/write-materialized-final-certificate0.mjs',
  'pcc-final-certificate-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-final-certificate0.mjs',
  'pcc-final-certificate-public-status0.mjs',
  'bin/write-final-certificate-public-status0.mjs',
  'pcc-final-certificate-public-status-concrete0.mjs',
  'bin/write-concrete-final-certificate-public-status0.mjs',
  'pcc-release-audit-final-certificate-gate0.mjs',
  'bin/write-release-audit-final-certificate-gate0.mjs',  
  'pcc-public-surface-freeze0.mjs',
  'pcc-readme-release-boundary0.mjs',
  'pcc-release-audit-final-certificate-concrete-gate0.mjs',
  'bin/write-release-audit-concrete-final-certificate-gate0.mjs',
  'pcc-concrete-release-appendix0.mjs',
  'bin/write-concrete-release-appendix0.mjs',
  'pcc-k-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-kbundle0.mjs',
  'pcc-final-integration-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-final-integration0.mjs',
  'pcc-hard-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-hard0.mjs',
  'pcc-pack-concrete-materialized0.mjs',
  'bin/write-concrete-materialized-pcc-pack0.mjs',
  'pcc-check-pcc-pack-exp0.mjs',
  'pcc-generate-pcc-pack0.mjs',
]);

export const RELEASE_AUDIT_REQUIRED_TESTS0 = Object.freeze([
  'pcc-core.test.mjs',
  'pcc-core.negative.test.mjs',
  'pcc-release-audit0-negative.test.mjs',
  'pcc-verifier-frag0.test.mjs',
  'pcc-verifier-frag0-current-suite.test.mjs',
  'pcc-boot0.test.mjs',
  'pcc-boot0-batch0-coverage.test.mjs',
  'pcc-kimpl0.test.mjs',
  'pcc-hard0.test.mjs',
  'pcc-public-api0.test.mjs',
  'pcc-rows0.test.mjs',
  'pcc-global-proof-dag0.test.mjs',
  'pcc-local-packages0.test.mjs',
  'pcc-global-firewalls0.test.mjs',
  'pcc-gpack0.test.mjs',
  'pcc-final-framework0.test.mjs',
  'pcc-final0.test.mjs',
  'pcc-pack-sufficiency0.test.mjs',
  'pcc-accept-run0.test.mjs',
  'pcc-integrated-pipeline0.test.mjs',
  'pcc-runall0.test.mjs',
  'pcc-public-entry0.test.mjs',
  'pcc-release-audit0.test.mjs',
  'pcc-integrated-pipeline-tamper0.test.mjs',
  'pcc-materialized0.test.mjs',
  'pcc-fixture-digests0.test.mjs',
  'pcc-synthetic-marker-inventory0.test.mjs',
  'pcc-materialized-pack0.test.mjs',
  'pcc-materialized-loader0.test.mjs',
  'pcc-materialized-core-extractor0.test.mjs',
  'pcc-materialized-phase-manifest0.test.mjs',              
  'pcc-materialized-artefact-inventory0.test.mjs',
  'pcc-materialized-artefact-deps0.test.mjs',
  'pcc-materialized-proof-refs0.test.mjs',
  'pcc-materialized-bounds0.test.mjs',
  'pcc-materialized-no-hidden-min0.test.mjs',
  'pcc-materialized-imports0.test.mjs',
  'pcc-materialized-aggregate0.test.mjs',
  'pcc-materialized-aggregate-cli0.test.mjs',
  'pcc-materialized-acceptance-bridge0.test.mjs',
  'pcc-materialized-acceptance-bridge-cli0.test.mjs',
  'pcc-materialized-path-readme0.test.mjs',
  'pcc-materialized-fixture-writer0.test.mjs',
  'pcc-materialized-fixture-roundtrip0.test.mjs',
  'pcc-materialized-digest-resolver0.test.mjs',
  'pcc-materialized-accept-run0.test.mjs',
  'pcc-materialized-accept-run-cli0.test.mjs',
  'pcc-materialized-accept-run-fixtures0.test.mjs',
  'pcc-materialized-final-verdict0.test.mjs',
  'pcc-materialized-final-verdict-cli0.test.mjs',
  'pcc-materialized-final-run-fixtures0.test.mjs',
  'pcc-materialized-final-run-roundtrip0.test.mjs',
  'pcc-materialized-public-status0.test.mjs',
  'pcc-materialized-public-status-cli0.test.mjs',
  'pcc-materialized-public-status-roundtrip0.test.mjs',
  'pcc-materialized-public-status-release-gate0.test.mjs',
  'pcc-release-audit-materialized-gate0.test.mjs',
  'pcc-release-audit-materialized-gate-negative0.test.mjs',
  'pcc-release-audit-cli-materialized-gate0.test.mjs',
  'pcc-release-audit-full-mode-gate-summary0.test.mjs',
  'pcc-boot-materialized0.test.mjs',
  'pcc-k-materialized0.test.mjs',
  'pcc-global-proof-dag-materialized0.test.mjs',
  'pcc-global-proof-dag-concrete-materialized0.test.mjs',
  'pcc-hard-materialized0.test.mjs',
  'pcc-rows-materialized0.test.mjs',
  'pcc-rows-concrete-materialized0.test.mjs',
  'pcc-local-packages-materialized0.test.mjs',
  'pcc-local-packages-concrete-materialized0.test.mjs',
  'pcc-global-firewalls-materialized0.test.mjs',
  'pcc-global-firewalls-concrete-materialized0.test.mjs',
  'pcc-final-integration-materialized0.test.mjs',
  'pcc-pack-materialized0.test.mjs',
  'pcc-accept-run-materialized0.test.mjs',
  'pcc-accept-run-concrete-materialized0.test.mjs',
  'pcc-final-certificate-materialized0.test.mjs',
  'pcc-final-certificate-concrete-materialized0.test.mjs',
  'pcc-final-certificate-public-status0.test.mjs',
  'pcc-final-certificate-public-status-concrete0.test.mjs',
  'pcc-release-audit-final-certificate-gate0.test.mjs',  
  'pcc-release-audit-surface-freeze0.test.mjs',
  'pcc-public-surface-freeze0.test.mjs',
  'pcc-release-audit-public-surface-freeze0.test.mjs',
  'pcc-release-audit-public-surface-summary0.test.mjs', 
  'pcc-release-audit-public-surface-summary-negative0.test.mjs',
  'pcc-release-audit-phase-order-freeze0.test.mjs',
  'pcc-release-audit-cli-hard-gate0.test.mjs',
  'pcc-readme-release-boundary0.test.mjs',
  'pcc-release-audit-readme-negative0.test.mjs',
  'pcc-release-audit-final-certificate-surface0.test.mjs',
  'pcc-release-audit-final-certificate-concrete-gate0.test.mjs',
  'pcc-release-audit-concrete-final-certificate-surface0.test.mjs',
  'pcc-concrete-release-appendix0.test.mjs',
  'pcc-k-concrete-materialized0.test.mjs',
  'pcc-final-integration-concrete-materialized0.test.mjs',
  'pcc-hard-concrete-materialized0.test.mjs',
  'pcc-pack-concrete-materialized0.test.mjs',
  'pcc-check-pcc-pack-exp0.test.mjs',
  'pcc-generate-pcc-pack0.test.mjs',
]);    

export const RELEASE_AUDIT_REQUIRED_EXPORTS0 = Object.freeze([
  '.',
  './runall0',
  './integrated-pipeline0',
  './accept-run0',
  './release-audit0',
  './final-certificate0',
  './final-certificate-public-status0',
  './release-audit-final-certificate-gate0',
]);

export const RELEASE_AUDIT_REQUIRED_SCRIPTS0 = Object.freeze([
  'smoke',
  'smoke:full',
  'runall',
  'release:audit',
  'materialized:shell',
  'materialized:shell:full',
  'materialized:aggregate',
  'materialized:aggregate:full',
  'materialized:bridge',
  'materialized:bridge:full',
  'materialized:write-fixtures',
  'materialized:write-fixtures:full',
  'materialized:resolve-digest',
  'materialized:resolve-digest:full',
  'materialized:accept-run',
  'materialized:accept-run:full',
  'materialized:write-accept-runs',
  'materialized:write-accept-runs:full',
  'materialized:final-verdict',
  'materialized:final-verdict:full',
  'materialized:write-final-runs',
  'materialized:write-final-runs:full',
  'materialized:public-status',
  'materialized:public-status:full',
  'materialized:public-status-roundtrip',
  'materialized:public-status-roundtrip:full',                
]);

export const RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0 = Object.freeze([
  'kind',
  'enabled',
  'skipped',
  'outputDir',
  'canonicalEnvelopeBytes',
  'runCliChecks',
  'deterministic',
  'materializedPath',
  'syntheticRunAll',
  'acceptedPublicConclusionOnly',
  'fileCount',
  'directRecordCount',
  'cliRecordCount',
  'gateDigest',
]);

export const RELEASE_AUDIT_FINAL_CERTIFICATE_PUBLIC_STATUS_SUMMARY_KEYS0 = Object.freeze([
  'kind',
  'enabled',
  'skipped',
  'outputDir',
  'canonicalEnvelopeBytes',
  'status',
  'verdict',
  'materializedPath',
  'syntheticRunAll',
  'publicConclusionEmitted',
  'publicConclusion',
  'certificateDigest',
  'finalVerdictDigest',
  'acceptRunDigest',
  'pccPackDigest',
  'canonicalByteRoots',
  'acceptanceTranscript',
  'releaseAuditAttached',
  'releaseAuditDigest',
  'releaseAuditStatus',
  'gateDigest',
]);


export const RELEASE_AUDIT_CONCRETE_FINAL_CERTIFICATE_PUBLIC_STATUS_SUMMARY_KEYS0 = Object.freeze([
  'kind',
  'enabled',
  'skipped',
  'outputDir',
  'canonicalEnvelopeBytes',
  'status',
  'verdict',
  'materializedPath',
  'syntheticRunAll',
  'publicConclusionEmitted',
  'publicConclusion',
  'certificateDigest',
  'finalVerdictDigest',
  'acceptRunDigest',
  'pccPackDigest',
  'canonicalByteRoots',
  'acceptanceTranscript',
  'releaseAuditAttached',
  'releaseAuditDigest',
  'releaseAuditStatus',
  'concreteRows',
  'concreteLocalPackages',
  'concreteGlobalFirewalls',
  'concreteGlobalProofDAG',
  'concreteKBundle',
  'kBundleKernelRuleCoverageComplete',
  'kBundleSigmaProofRefsResolve',
  'kBundleReflectionProofRefsResolve',
  'concreteHardCheck',
  'hardCheckerCoverageComplete',
  'hardRowKeyCoverageComplete',
  'hardRoutePriorityComplete',
  'hardProofRefPolicyComplete',
  'hardHashDisciplineComplete',
  'hardNoMinCoverageComplete',
  'hardImportPolicyComplete',
  'hardReflectionPolicyComplete',
  'hardBoundsPolicyComplete',
  'hardDiagnosticsPolicyComplete',
  'concreteFinalIntegration',
  'finalIntegrationConcreteGlobalProofDAG',
  'finalIntegrationGPackFieldCoverageComplete',
  'finalIntegrationRowFamGCoverageComplete',
  'finalIntegrationUsesGPack',
  'rowFamGUsesGPack',
  'finalTheoremUsesFinalIntegration',
  'rowFamFinalUsesFinalTheorem',
  'finalMatchUsesGPack',
  'satDecisionUsesGPack',
  'concretePCCPack',
  'concretePCCPackCoverageDigest',
  'pccPackPublicConclusionOnlyAfterAcceptRun',
  'pccPackLinkedToKBundle',
  'pccPackLinkedToHardCheck',
  'pccPackLinkedToRows',
  'pccPackLinkedToLocalPackages',
  'pccPackLinkedToGlobalFirewalls',
  'pccPackLinkedToGlobalProofDAG',
  'pccPackLinkedToGPack',
  'pccPackLinkedToFinalIntegration',
  'pccPackLinkedToFinalTheorem',
  'checkPCCPackexpRecordPresent',
  'checkPCCPackexpRecordAccepted',
  'checkPCCPackexpRecordChecker',
  'checkPCCPackexpRecordDigest',
  'checkPCCPackexpRecordDigestMatchesNF',
  'checkPCCPackexpRecordConcretePCCPack',
  'checkPCCPackexpRecordPccPackDigest',
  'checkPCCPackexpRecordPccPackDigestMatchesConcreteRun',
  'checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun',
  'checkPCCPackexpRecordPublicConclusionNotEmitted',
  'checkPCCPackexpRecordClaimBoundaryConditional',
  'generatedPCCPackexpEnvelopePresent',
  'generatedPCCPackexpEnvelopeDigest',
  'generatedPCCPackexpGenCallGeneratePCCPack',
  'generatedPCCPackexpCoreOnly',
  'generatedPCCPackexpExcludesAcceptRun',
  'generatedPCCPackexpPackageMatchesConcreteRun',
  'generatedPCCPackexpCheckRecordMatchesConcreteRun',
  'generatedPCCPackexpCheckRecordAccepted',
  'generatedPCCPackexpCheckRecordChecker',
  'generatedPCCPackexpCheckRecordDigest',
  'generatedPCCPackexpCheckRecordDigestMatchesNF',
  'generatedPCCPackexpCheckRecordClaimBoundaryConditional',
  'generatedPCCPackexpLinkageGeneratedPackageDigestMatches',
  'generatedPCCPackexpLinkageCheckRecordDigestMatches',
  'checkGeneratedPCCPackexpRecordPresent',
  'checkGeneratedPCCPackexpRecordAccepted',
  'checkGeneratedPCCPackexpRecordChecker',
  'checkGeneratedPCCPackexpRecordDigest',
  'checkGeneratedPCCPackexpRecordDigestMatchesNF',
  'checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope',
  'checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope',
  'generatedPCCPackexpBoot0',
  'generatedPCCPackexpBoot0Accepted',
  'generatedPCCPackexpBoot0Kind',
  'generatedPCCPackexpBoot0Digest',
  'generatedPCCPackexpBoot0CheckDigest',
  'generatedPCCPackexpBoot0CanonicalByteDigest',
  'generatedPCCPackexpBoot0RowCount',
  'generatedPCCPackexpBoot0KernelRuleCount',
  'generatedPCCPackexpBoot0JsonMaterialized',
  'generatedPCCPackexpBoot0NoFixtureMarkers',
  'generatedPCCPackexpBoot0BootBatchDigest',
  'generatedPCCPackexpBoot0BootAuditDigest',
  'generatedPCCPackexpBoot0LinkedToPCCPack',
  'generatedPCCPackexpBoot0LinkedToCoreDigestMap',
  'generatedPCCPackexpBoot0DigestMatchesGeneratedPackage',
  'generatedPCCPackexpBoot0DigestMatchesCoreDigestMap',
  'generatedPCCPackexpBoot0B0Accepted',
  'generatedPCCPackexpBoot0B0Digest',
  'generatedPCCPackexpBoot0B0CoverageDigest',
  'generatedPCCPackexpBoot0B0FamilyCount',
  'generatedPCCPackexpBoot0B0RequiredFamilyCount',
  'generatedPCCPackexpBoot0B0Families',
  'generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent',
  'generatedPCCPackexpBoot0B0CoversIface',
  'generatedPCCPackexpBoot0B0CoversSched',
  'generatedPCCPackexpBoot0B0CoversNF',
  'generatedPCCPackexpBoot0B0CoversTruthEval',
  'generatedPCCPackexpBoot0B0CoversRel',
  'generatedPCCPackexpBoot0B0CoversCharge',
  'generatedPCCPackexpBoot0B0CoversObl',
  'generatedPCCPackexpBoot0B0CoversArith',
  'generatedPCCPackexpBoot0B0CoversMode',
  'generatedPCCPackexpBoot0B0CoversRoute',
  'generatedPCCPackexpBoot0B0CoversHash',
  'generatedPCCPackexpBoot0B0CoversImport',
  'generatedPCCPackexpKernelSeed0',
  'generatedPCCPackexpKernelSeed0Accepted',
  'generatedPCCPackexpKernelSeed0Kind',
  'generatedPCCPackexpKernelSeed0Digest',
  'generatedPCCPackexpKernelSeed0RuleCount',
  'generatedPCCPackexpKernelSeed0RequiredRuleCount',
  'generatedPCCPackexpKernelSeed0Rules',
  'generatedPCCPackexpKernelSeed0AllRequiredRulesPresent',
  'generatedPCCPackexpKernelSeed0HasEq',
  'generatedPCCPackexpKernelSeed0HasSubst',
  'generatedPCCPackexpKernelSeed0HasRecord',
  'generatedPCCPackexpKernelSeed0HasDAGInd',
  'generatedPCCPackexpKernelSeed0HasLedgerInd',
  'generatedPCCPackexpKernelSeed0HasOblTopoInd',
  'generatedPCCPackexpKernelSeed0HasTraceInd',
  'generatedPCCPackexpKernelSeed0HasFiniteExhaust',
  'generatedPCCPackexpKernelSeed0HasDPInd',
  'generatedPCCPackexpKernelSeed0HasHall',
  'generatedPCCPackexpKernelSeed0HasRankInd',
  'generatedPCCPackexpKernelSeed0HasMinCounterexample',
  'generatedPCCPackexpKernelSeed0HasIntArith',
  'generatedPCCPackexpKernelSeed0HasTransport',
  'generatedPCCPackexpKernelSeed0HasTruthVec',
  'generatedPCCPackexpKernelSeed0HasFiniteRel',
  'generatedPCCPackexpKernelSeed0ProofNodeKindCount',
  'generatedPCCPackexpKernelSeed0ProofNodeKinds',
  'generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent',
  'generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
  'generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic',
  'generatedPCCPackexpKernelSeed0ProofRefsHashIndependent',
  'generatedPCCPackexpKernelSeed0PiBootDigestMatches',
  'generatedPCCPackexpCodec0',
  'generatedPCCPackexpCodec0Accepted',
  'generatedPCCPackexpCodec0Kind',
  'generatedPCCPackexpCodec0Digest',
  'generatedPCCPackexpCodec0Canonical',
  'generatedPCCPackexpCodec0NaturalEncoding',
  'generatedPCCPackexpCodec0NaturalEncodingCanonical',
  'generatedPCCPackexpCodec0IntegerEncoding',
  'generatedPCCPackexpCodec0IntegerEncodingCanonical',
  'generatedPCCPackexpCodec0StringEncoding',
  'generatedPCCPackexpCodec0StringEncodingCanonical',
  'generatedPCCPackexpCodec0TopLevelConsumesAllBytes',
  'generatedPCCPackexpCodec0NormalFormSerialization',
  'generatedPCCPackexpCodec0NormalFormSerializationCanonical',
  'generatedPCCPackexpCodec0PiBootDigestMatches',
  'generatedPCCPackexpDigest0',
  'generatedPCCPackexpDigest0Accepted',
  'generatedPCCPackexpDigest0Kind',
  'generatedPCCPackexpDigest0Digest',
  'generatedPCCPackexpDigest0Alg',
  'generatedPCCPackexpDigest0AlgSHA256',
  'generatedPCCPackexpDigest0Bytes',
  'generatedPCCPackexpDigest0BytesCanonicalJson',
  'generatedPCCPackexpDigest0EqualityNotObjectEquality',
  'generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup',
  'generatedPCCPackexpDigest0PiBootDigestMatches',
  'generatedPCCPackexpIfaceDict0',
  'generatedPCCPackexpIfaceDict0Accepted',
  'generatedPCCPackexpIfaceDict0Kind',
  'generatedPCCPackexpIfaceDict0Digest',
  'generatedPCCPackexpIfaceDict0ForbiddenSymbolCount',
  'generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent',
  'generatedPCCPackexpIfaceDict0NoExecutableMinSymbols',
  'generatedPCCPackexpIfaceDict0PublicConstructorsPresent',
  'generatedPCCPackexpIfaceDict0CriticalKindsPresent',
  'generatedPCCPackexpIfaceDict0RouteTokensPresent',
  'generatedPCCPackexpIfaceDict0PiBootDigestMatches',
  'generatedPCCPackexpSched0',
  'generatedPCCPackexpSched0Accepted',
  'generatedPCCPackexpSched0Kind',
  'generatedPCCPackexpSched0Digest',
  'generatedPCCPackexpSched0CoreMatchesExpected',
  'generatedPCCPackexpSched0CoreB0',
  'generatedPCCPackexpSched0CoreK0',
  'generatedPCCPackexpSched0CoreR0',
  'generatedPCCPackexpSched0CoreH0',
  'generatedPCCPackexpSched0CoreO0',
  'generatedPCCPackexpSched0CoreRel0',
  'generatedPCCPackexpSched0ScaleFactorsPresent',
  'generatedPCCPackexpSched0SelectorBoundsPresent',
  'generatedPCCPackexpSched0SelectorBoundBH',
  'generatedPCCPackexpSched0SelectorBoundBTheta',
  'generatedPCCPackexpSched0PolynomialExponent',
  'generatedPCCPackexpSched0PiBootDigestMatches',
  'generatedPCCPackexpByteLang0',
  'generatedPCCPackexpByteLang0Accepted',
  'generatedPCCPackexpByteLang0Kind',
  'generatedPCCPackexpByteLang0Digest',
  'generatedPCCPackexpByteLang0TagCount',
  'generatedPCCPackexpByteLang0TagsUnique',
  'generatedPCCPackexpByteLang0RequiredTagsPresent',
  'generatedPCCPackexpByteLang0SortCount',
  'generatedPCCPackexpByteLang0RequiredSortsPresent',
  'generatedPCCPackexpByteLang0ConstructorCount',
  'generatedPCCPackexpByteLang0RequiredConstructorsPresent',
  'generatedPCCPackexpByteLang0RecordCount',
  'generatedPCCPackexpByteLang0RequiredRecordAritiesPresent',
  'generatedPCCPackexpByteLang0PiBootDigestMatches',
  'generatedPCCPackexpBootAudit0',
  'generatedPCCPackexpBootAudit0Accepted',
  'generatedPCCPackexpBootAudit0Checker',
  'generatedPCCPackexpBootAudit0Digest',
  'generatedPCCPackexpBootAudit0DigestMatchesNF',
  'generatedPCCPackexpBootAudit0NFKind',
  'generatedPCCPackexpBootAudit0SuiteId',
  'generatedPCCPackexpBootAudit0CaseCount',
  'generatedPCCPackexpBootAudit0PositiveCount',
  'generatedPCCPackexpBootAudit0NegativeCount',
  'generatedPCCPackexpBootAudit0CoversB0Accept',
  'generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject',
  'generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject',
  'generatedPCCPackexpPiBoot0',
  'generatedPCCPackexpPiBoot0Accepted',
  'generatedPCCPackexpPiBoot0Kind',
  'generatedPCCPackexpPiBoot0Digest',
  'generatedPCCPackexpPiBoot0Materialized',
  'generatedPCCPackexpPiBoot0ExternalJson',
  'generatedPCCPackexpPiBoot0RefCount',
  'generatedPCCPackexpPiBoot0AllBootRefsPresent',
  'generatedPCCPackexpPiBoot0RefsMatchBootObjects',
  'generatedPCCPackexpPiBoot0RefsIncludeByteLang0',
  'generatedPCCPackexpPiBoot0RefsIncludeCodec0',
  'generatedPCCPackexpPiBoot0RefsIncludeDigest0',
  'generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0',
  'generatedPCCPackexpPiBoot0RefsIncludeSched0',
  'generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0',
  'generatedPCCPackexpPiBoot0RefsIncludeB0',
  'generatedPCCPackexpPiBoot0RefsIncludeBootAudit0',
  'generatedPCCPackexpConcreteKBundle0',
  'generatedPCCPackexpConcreteKBundle0Accepted',
  'generatedPCCPackexpConcreteKBundle0Checker',
  'generatedPCCPackexpConcreteKBundle0Digest',
  'generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest',
  'generatedPCCPackexpConcreteKBundle0BootDigest',
  'generatedPCCPackexpConcreteKBundle0KImplDigest',
  'generatedPCCPackexpConcreteKBundle0K0Digest',
  'generatedPCCPackexpConcreteKBundle0SigmaDigest',
  'generatedPCCPackexpConcreteKBundle0ReflectionDigest',
  'generatedPCCPackexpConcreteKBundle0ProofInventoryDigest',
  'generatedPCCPackexpConcreteKBundle0KernelRuleCount',
  'generatedPCCPackexpConcreteKBundle0ConformanceNodeCount',
  'generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete',
  'generatedPCCPackexpConcreteKBundle0SigmaTheoremCount',
  'generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete',
  'generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve',
  'generatedPCCPackexpConcreteKBundle0ReflectionCount',
  'generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete',
  'generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve',
  'generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs',
  'generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols',
  'generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0',
  'finalCertificateUsesConcreteAcceptRun',
  'statusUsesConcreteFinalCertificate',
  'publicStatusCertificateDigestMatchesConcrete',
  'publicStatusFinalVerdictDigestMatchesConcrete',
  'publicStatusAcceptRunDigestMatchesConcrete',
  'publicStatusPccPackDigestMatchesConcrete',
  'gateDigest',
]);

export const RELEASE_AUDIT_NF_KEYS0 = Object.freeze([
  'kind',
  'checker',
  'version',
  'rootDir',
  'moduleCount',
  'testCount',
  'requiredExports',
  'requiredScripts',
  'checkerCoverageCount',

  'publicSurfaceFreeze',
  'publicSurfaceFreezeSummary',
  'publicSurfaceFreezeDigest',
  'publicSurfaceFreezePublicEntryExportCount',
  'publicSurfaceFreezePackageExportCount',
  'publicSurfaceFreezePackageBinCount',
  'publicSurfaceFreezePackageScriptCount',
  'publicSurfaceFreezeSurfaceFrozen',

  'materializedPublicStatusGate',
  'materializedPublicStatusGateSummary',
  'materializedPublicStatusGateDigest',
  'materializedPublicStatusGateFileCount',
  'materializedPublicStatusGateDirectRecordCount',
  'materializedPublicStatusGateCliRecordCount',
  'materializedPublicStatusGateAcceptedPublicConclusionOnly',

  'finalCertificatePublicStatusGate',
  'finalCertificatePublicStatusGateSummary',
  'finalCertificatePublicStatusGateDigest',
  'finalCertificatePublicStatusGateStatus',
  'finalCertificatePublicStatusGateVerdict',
  'finalCertificatePublicStatusGatePublicConclusionEmitted',
  'finalCertificatePublicStatusGateCertificateDigest',
  'finalCertificatePublicStatusGateFinalVerdictDigest',
  'finalCertificatePublicStatusGateAcceptRunDigest',
  'finalCertificatePublicStatusGatePccPackDigest',
  'finalCertificatePublicStatusGateReleaseAuditAttached',  

  'concreteFinalCertificatePublicStatusGate',
  'concreteFinalCertificatePublicStatusGateSummary',
  'concreteFinalCertificatePublicStatusGateDigest',
  'concreteFinalCertificatePublicStatusGateStatus',
  'concreteFinalCertificatePublicStatusGateVerdict',
  'concreteFinalCertificatePublicStatusGatePublicConclusionEmitted',
  'concreteFinalCertificatePublicStatusGateCertificateDigest',
  'concreteFinalCertificatePublicStatusGateFinalVerdictDigest',
  'concreteFinalCertificatePublicStatusGateAcceptRunDigest',
  'concreteFinalCertificatePublicStatusGatePccPackDigest',
  'concreteFinalCertificatePublicStatusGateReleaseAuditAttached',
  'concreteFinalCertificatePublicStatusGateConcreteRows',
  'concreteFinalCertificatePublicStatusGateConcreteLocalPackages',
  'concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls',
  'concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG',
  'concreteFinalCertificatePublicStatusGateConcreteKBundle',
  'concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete',
  'concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateConcreteHardCheck',
  'concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete',
  'concreteFinalCertificatePublicStatusGateHardRowKeyCoverageComplete',
  'concreteFinalCertificatePublicStatusGateHardRoutePriorityComplete',
  'concreteFinalCertificatePublicStatusGateHardProofRefPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardHashDisciplineComplete',
  'concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete',
  'concreteFinalCertificatePublicStatusGateHardImportPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardReflectionPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardBoundsPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardDiagnosticsPolicyComplete',
  'concreteFinalCertificatePublicStatusGateConcreteFinalIntegration',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationConcreteGlobalProofDAG',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationUsesGPack',
  'concreteFinalCertificatePublicStatusGateRowFamGUsesGPack',
  'concreteFinalCertificatePublicStatusGateFinalTheoremUsesFinalIntegration',
  'concreteFinalCertificatePublicStatusGateRowFamFinalUsesFinalTheorem',
  'concreteFinalCertificatePublicStatusGateFinalMatchUsesGPack',
  'concreteFinalCertificatePublicStatusGateSatDecisionUsesGPack',
  'concreteFinalCertificatePublicStatusGateConcretePCCPack',
  'concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest',
  'concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToRows',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Checker',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0MaterializedKBundleDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0BootDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KImplDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0K0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ProofInventoryDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ConformanceNodeCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaTheoremCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaCoverageComplete',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCoverageComplete',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoOpaqueProofRefs',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoExecutableMinSymbols',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0',
  'concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate',
  'publicConclusion',
]);

export const RELEASE_AUDIT_CLI_SUMMARY_KEYS0 = Object.freeze([
  'tag',
  'checker',
  'moduleCount',
  'testCount',
  'checkerCoverageCount',

  'publicSurfaceFreeze',
  'publicSurfaceFreezeSummary',
  'publicSurfaceFreezeDigest',
  'publicSurfaceFreezePublicEntryExportCount',
  'publicSurfaceFreezePackageExportCount',
  'publicSurfaceFreezePackageBinCount',
  'publicSurfaceFreezePackageScriptCount',
  'publicSurfaceFreezeSurfaceFrozen',

  'materializedPublicStatusGate',
  'materializedPublicStatusGateSummary',
  'materializedPublicStatusGateDigest',
  'materializedPublicStatusGateFileCount',
  'materializedPublicStatusGateDirectRecordCount',
  'materializedPublicStatusGateCliRecordCount',
  'materializedPublicStatusGateAcceptedPublicConclusionOnly',

  'finalCertificatePublicStatusGate',
  'finalCertificatePublicStatusGateSummary',
  'finalCertificatePublicStatusGateDigest',
  'finalCertificatePublicStatusGateStatus',
  'finalCertificatePublicStatusGateVerdict',
  'finalCertificatePublicStatusGatePublicConclusionEmitted',
  'finalCertificatePublicStatusGateCertificateDigest',
  'finalCertificatePublicStatusGateFinalVerdictDigest',
  'finalCertificatePublicStatusGateAcceptRunDigest',
  'finalCertificatePublicStatusGatePccPackDigest',
  'finalCertificatePublicStatusGateReleaseAuditAttached',  

  'concreteFinalCertificatePublicStatusGate',
  'concreteFinalCertificatePublicStatusGateSummary',
  'concreteFinalCertificatePublicStatusGateDigest',
  'concreteFinalCertificatePublicStatusGateStatus',
  'concreteFinalCertificatePublicStatusGateVerdict',
  'concreteFinalCertificatePublicStatusGatePublicConclusionEmitted',
  'concreteFinalCertificatePublicStatusGateCertificateDigest',
  'concreteFinalCertificatePublicStatusGateFinalVerdictDigest',
  'concreteFinalCertificatePublicStatusGateAcceptRunDigest',
  'concreteFinalCertificatePublicStatusGatePccPackDigest',
  'concreteFinalCertificatePublicStatusGateReleaseAuditAttached',
  'concreteFinalCertificatePublicStatusGateConcreteRows',
  'concreteFinalCertificatePublicStatusGateConcreteLocalPackages',
  'concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls',
  'concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG',
  'concreteFinalCertificatePublicStatusGateConcreteKBundle',
  'concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete',
  'concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateConcreteHardCheck',
  'concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete',
  'concreteFinalCertificatePublicStatusGateHardRowKeyCoverageComplete',
  'concreteFinalCertificatePublicStatusGateHardRoutePriorityComplete',
  'concreteFinalCertificatePublicStatusGateHardProofRefPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardHashDisciplineComplete',
  'concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete',
  'concreteFinalCertificatePublicStatusGateHardImportPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardReflectionPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardBoundsPolicyComplete',
  'concreteFinalCertificatePublicStatusGateHardDiagnosticsPolicyComplete',
  'concreteFinalCertificatePublicStatusGateConcreteFinalIntegration',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationConcreteGlobalProofDAG',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete',
  'concreteFinalCertificatePublicStatusGateFinalIntegrationUsesGPack',
  'concreteFinalCertificatePublicStatusGateRowFamGUsesGPack',
  'concreteFinalCertificatePublicStatusGateFinalTheoremUsesFinalIntegration',
  'concreteFinalCertificatePublicStatusGateRowFamFinalUsesFinalTheorem',
  'concreteFinalCertificatePublicStatusGateFinalMatchUsesGPack',
  'concreteFinalCertificatePublicStatusGateSatDecisionUsesGPack',
  'concreteFinalCertificatePublicStatusGateConcretePCCPack',
  'concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest',
  'concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToRows',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration',
  'concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted',
  'concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope',
  'concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Accepted',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Checker',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0MaterializedKBundleDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0BootDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KImplDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0K0Digest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ProofInventoryDigest',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ConformanceNodeCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaTheoremCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaCoverageComplete',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCount',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCoverageComplete',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoOpaqueProofRefs',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoExecutableMinSymbols',
  'concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0',
  'concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate',
  'publicConclusion',
  'digest',
]);

export const RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0 = Object.freeze([
  'kind',
  'enabled',
  'skipped',
  'publicEntryExportCount',
  'packageExportCount',
  'packageBinCount',
  'packageScriptCount',
  'surfaceFrozen',
  'publicSurfaceDigest',
]);

export const RELEASE_AUDIT_PHASE_ORDER0 = Object.freeze([
  'shape',
  'requiredFiles',
  'staleSrc',
  'packageJson',
  'testInventory',
  'readme',
  'syntax',
  'runAllDeterminism',
  'runAllMutation',
  'cliSmoke',
  'publicSurfaceFreeze',
  'materializedPublicStatusGate',
  'finalCertificatePublicStatusGate',  
  'concreteFinalCertificatePublicStatusGate',
  'surfaceFreeze',
]);

export function makeReleaseAuditConfig0(overrides = {}) {
  return {
    kind: 'ReleaseAuditConfig0',
    version: CHECKER_VERSION,
    rootDir: REPO_ROOT,
    runSyntaxCheck: true,
    runRunAll: true,
    runMutationCheck: true,
    runCliSmoke: false,
    readmeReleaseBoundaryRunner: null,
    runPublicSurfaceFreeze: true,
    publicSurfaceFreezeRunner: null,
    runMaterializedPublicStatusGate: true,
    materializedPublicStatusGateRunner: null,
    materializedPublicStatusGateOutputDir: null,
    materializedPublicStatusGateCanonicalEnvelopeBytes: false,
    materializedPublicStatusGateRunCliChecks: true,
    mutationInputFactory: null,
    mutationRunner: null,
    runFinalCertificatePublicStatusGate: true,
    finalCertificatePublicStatusGateRunner: null,
    finalCertificatePublicStatusGateOutputDir: null,
    finalCertificatePublicStatusGateCanonicalEnvelopeBytes: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: null,
    concreteFinalCertificatePublicStatusGateOutputDir: null,
    concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes: false,  
    ...overrides,
  };
}

export async function CheckReleaseAudit0(config = makeReleaseAuditConfig0()) {
  const checker = 'CheckReleaseAudit0';
  const ledger = [];
  const cfg = makeReleaseAuditConfig0(config);
  let finalCertificatePublicStatusGateNF = null;
  let concreteFinalCertificatePublicStatusGateNF = null;  
  let publicSurfaceFreezeNF = null;
  let materializedPublicStatusGateNF = null;

  const phases = [
    ['shape', `${checker}.input`, () => validateConfig0(cfg)],
    ['requiredFiles', `${checker}.requiredFiles`, () => validateRequiredFiles0(cfg)],
    ['staleSrc', `${checker}.staleSrc`, () => validateNoStaleSrcDuplicates0(cfg)],
    ['packageJson', `${checker}.packageJson`, () => validatePackageJson0(cfg)],
    ['testInventory', `${checker}.testInventory`, () => validateTestInventory0(cfg)],
    ['readme', `${checker}.readme`, () => validateReadme0(cfg)],
    ['syntax', `${checker}.syntax`, () => validateSyntax0(cfg)],
    ['runAllDeterminism', `${checker}.runAllDeterminism`, () => validateRunAllDeterminism0(cfg)],
    ['runAllMutation', `${checker}.runAllMutation`, () => validateRunAllMutation0(cfg)],
    ['cliSmoke', `${checker}.cliSmoke`, () => validateCliSmoke0(cfg)],
    ['publicSurfaceFreeze', `${checker}.publicSurfaceFreeze`, () => validatePublicSurfaceFreeze0(cfg)],
    ['materializedPublicStatusGate', `${checker}.materializedPublicStatusGate`, () => validateMaterializedPublicStatusGate0(cfg)],
    ['finalCertificatePublicStatusGate', `${checker}.finalCertificatePublicStatusGate`, () => validateFinalCertificatePublicStatusGate0(cfg)],
    ['concreteFinalCertificatePublicStatusGate', `${checker}.concreteFinalCertificatePublicStatusGate`, () => validateConcreteFinalCertificatePublicStatusGate0(cfg)],  
  ];

  for (const [phase, coord, run] of phases) {
    const result = await run();

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

    if (phase === 'publicSurfaceFreeze') {
      publicSurfaceFreezeNF = result.nf ?? null;
    }

    if (phase === 'materializedPublicStatusGate') {
      materializedPublicStatusGateNF = result.nf ?? null;
    }

    if (phase === 'finalCertificatePublicStatusGate') {
      finalCertificatePublicStatusGateNF = result.nf ?? null;
    }

    if (phase === 'concreteFinalCertificatePublicStatusGate') {
      concreteFinalCertificatePublicStatusGateNF = result.nf ?? null;
    }    
  }

  const publicSurfaceFreezeSummary = summarizePublicSurfaceFreezeNF0(
    publicSurfaceFreezeNF,
    cfg,
  );

  const materializedPublicStatusGateSummary = summarizeMaterializedPublicStatusGateNF0(
    materializedPublicStatusGateNF,
    cfg,
  );

  const finalCertificatePublicStatusGateSummary = summarizeFinalCertificatePublicStatusGateNF0(
    finalCertificatePublicStatusGateNF,
    cfg,
  );

  const concreteFinalCertificatePublicStatusGateSummary = summarizeConcreteFinalCertificatePublicStatusGateNF0(
    concreteFinalCertificatePublicStatusGateNF,
    cfg,
  );  

  const nf = {
    kind: 'ReleaseAudit0NF',
    checker,
    version: CHECKER_VERSION,
    rootDir: cfg.rootDir,
    moduleCount: RELEASE_AUDIT_REQUIRED_MODULES0.length,
    testCount: RELEASE_AUDIT_REQUIRED_TESTS0.length,
    requiredExports: RELEASE_AUDIT_REQUIRED_EXPORTS0,
    requiredScripts: RELEASE_AUDIT_REQUIRED_SCRIPTS0,
    checkerCoverageCount: RUNALL_CHECKER_COVERAGE0.length,

    publicSurfaceFreeze: cfg.runPublicSurfaceFreeze,
    publicSurfaceFreezeSummary,
    publicSurfaceFreezeDigest: publicSurfaceFreezeSummary.publicSurfaceDigest,
    publicSurfaceFreezePublicEntryExportCount: publicSurfaceFreezeSummary.publicEntryExportCount,
    publicSurfaceFreezePackageExportCount: publicSurfaceFreezeSummary.packageExportCount,
    publicSurfaceFreezePackageBinCount: publicSurfaceFreezeSummary.packageBinCount,
    publicSurfaceFreezePackageScriptCount: publicSurfaceFreezeSummary.packageScriptCount,
    publicSurfaceFreezeSurfaceFrozen: publicSurfaceFreezeSummary.surfaceFrozen,

    materializedPublicStatusGate: cfg.runMaterializedPublicStatusGate,
    materializedPublicStatusGateSummary,
    materializedPublicStatusGateDigest: materializedPublicStatusGateSummary.gateDigest,
    materializedPublicStatusGateFileCount: materializedPublicStatusGateSummary.fileCount,
    materializedPublicStatusGateDirectRecordCount: materializedPublicStatusGateSummary.directRecordCount,
    materializedPublicStatusGateCliRecordCount: materializedPublicStatusGateSummary.cliRecordCount,
    materializedPublicStatusGateAcceptedPublicConclusionOnly: materializedPublicStatusGateSummary.acceptedPublicConclusionOnly,

    finalCertificatePublicStatusGate: cfg.runFinalCertificatePublicStatusGate,
    finalCertificatePublicStatusGateSummary,
    finalCertificatePublicStatusGateDigest: finalCertificatePublicStatusGateSummary.gateDigest,
    finalCertificatePublicStatusGateStatus: finalCertificatePublicStatusGateSummary.status,
    finalCertificatePublicStatusGateVerdict: finalCertificatePublicStatusGateSummary.verdict,
    finalCertificatePublicStatusGatePublicConclusionEmitted: finalCertificatePublicStatusGateSummary.publicConclusionEmitted,
    finalCertificatePublicStatusGateCertificateDigest: finalCertificatePublicStatusGateSummary.certificateDigest,
    finalCertificatePublicStatusGateFinalVerdictDigest: finalCertificatePublicStatusGateSummary.finalVerdictDigest,
    finalCertificatePublicStatusGateAcceptRunDigest: finalCertificatePublicStatusGateSummary.acceptRunDigest,
    finalCertificatePublicStatusGatePccPackDigest: finalCertificatePublicStatusGateSummary.pccPackDigest,
    finalCertificatePublicStatusGateReleaseAuditAttached: finalCertificatePublicStatusGateSummary.releaseAuditAttached,

    concreteFinalCertificatePublicStatusGate: cfg.runConcreteFinalCertificatePublicStatusGate,
    concreteFinalCertificatePublicStatusGateSummary,
    concreteFinalCertificatePublicStatusGateDigest: concreteFinalCertificatePublicStatusGateSummary.gateDigest,
    concreteFinalCertificatePublicStatusGateStatus: concreteFinalCertificatePublicStatusGateSummary.status,
    concreteFinalCertificatePublicStatusGateVerdict: concreteFinalCertificatePublicStatusGateSummary.verdict,
    concreteFinalCertificatePublicStatusGatePublicConclusionEmitted: concreteFinalCertificatePublicStatusGateSummary.publicConclusionEmitted,
    concreteFinalCertificatePublicStatusGateCertificateDigest: concreteFinalCertificatePublicStatusGateSummary.certificateDigest,
    concreteFinalCertificatePublicStatusGateFinalVerdictDigest: concreteFinalCertificatePublicStatusGateSummary.finalVerdictDigest,
    concreteFinalCertificatePublicStatusGateAcceptRunDigest: concreteFinalCertificatePublicStatusGateSummary.acceptRunDigest,
    concreteFinalCertificatePublicStatusGatePccPackDigest: concreteFinalCertificatePublicStatusGateSummary.pccPackDigest,
    concreteFinalCertificatePublicStatusGateReleaseAuditAttached: concreteFinalCertificatePublicStatusGateSummary.releaseAuditAttached,
    concreteFinalCertificatePublicStatusGateConcreteRows: concreteFinalCertificatePublicStatusGateSummary.concreteRows,
    concreteFinalCertificatePublicStatusGateConcreteLocalPackages: concreteFinalCertificatePublicStatusGateSummary.concreteLocalPackages,
    concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls: concreteFinalCertificatePublicStatusGateSummary.concreteGlobalFirewalls,
    concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG: concreteFinalCertificatePublicStatusGateSummary.concreteGlobalProofDAG,
    concreteFinalCertificatePublicStatusGateConcreteKBundle: concreteFinalCertificatePublicStatusGateSummary.concreteKBundle,
    concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.kBundleKernelRuleCoverageComplete,
    concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve: concreteFinalCertificatePublicStatusGateSummary.kBundleSigmaProofRefsResolve,
    concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve: concreteFinalCertificatePublicStatusGateSummary.kBundleReflectionProofRefsResolve,
    concreteFinalCertificatePublicStatusGateConcreteHardCheck: concreteFinalCertificatePublicStatusGateSummary.concreteHardCheck,
    concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.hardCheckerCoverageComplete,
    concreteFinalCertificatePublicStatusGateHardRowKeyCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.hardRowKeyCoverageComplete,
    concreteFinalCertificatePublicStatusGateHardRoutePriorityComplete: concreteFinalCertificatePublicStatusGateSummary.hardRoutePriorityComplete,
    concreteFinalCertificatePublicStatusGateHardProofRefPolicyComplete: concreteFinalCertificatePublicStatusGateSummary.hardProofRefPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardHashDisciplineComplete: concreteFinalCertificatePublicStatusGateSummary.hardHashDisciplineComplete,
    concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.hardNoMinCoverageComplete,
    concreteFinalCertificatePublicStatusGateHardImportPolicyComplete: concreteFinalCertificatePublicStatusGateSummary.hardImportPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardReflectionPolicyComplete: concreteFinalCertificatePublicStatusGateSummary.hardReflectionPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardBoundsPolicyComplete: concreteFinalCertificatePublicStatusGateSummary.hardBoundsPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardDiagnosticsPolicyComplete: concreteFinalCertificatePublicStatusGateSummary.hardDiagnosticsPolicyComplete,
    concreteFinalCertificatePublicStatusGateConcreteFinalIntegration: concreteFinalCertificatePublicStatusGateSummary.concreteFinalIntegration,
    concreteFinalCertificatePublicStatusGateFinalIntegrationConcreteGlobalProofDAG: concreteFinalCertificatePublicStatusGateSummary.finalIntegrationConcreteGlobalProofDAG,
    concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.finalIntegrationGPackFieldCoverageComplete,
    concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.finalIntegrationRowFamGCoverageComplete,
    concreteFinalCertificatePublicStatusGateFinalIntegrationUsesGPack: concreteFinalCertificatePublicStatusGateSummary.finalIntegrationUsesGPack,
    concreteFinalCertificatePublicStatusGateRowFamGUsesGPack: concreteFinalCertificatePublicStatusGateSummary.rowFamGUsesGPack,
    concreteFinalCertificatePublicStatusGateFinalTheoremUsesFinalIntegration: concreteFinalCertificatePublicStatusGateSummary.finalTheoremUsesFinalIntegration,
    concreteFinalCertificatePublicStatusGateRowFamFinalUsesFinalTheorem: concreteFinalCertificatePublicStatusGateSummary.rowFamFinalUsesFinalTheorem,
    concreteFinalCertificatePublicStatusGateFinalMatchUsesGPack: concreteFinalCertificatePublicStatusGateSummary.finalMatchUsesGPack,
    concreteFinalCertificatePublicStatusGateSatDecisionUsesGPack: concreteFinalCertificatePublicStatusGateSummary.satDecisionUsesGPack,
    concreteFinalCertificatePublicStatusGateConcretePCCPack: concreteFinalCertificatePublicStatusGateSummary.concretePCCPack,
    concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest: concreteFinalCertificatePublicStatusGateSummary.concretePCCPackCoverageDigest,
    concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun: concreteFinalCertificatePublicStatusGateSummary.pccPackPublicConclusionOnlyAfterAcceptRun,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToKBundle,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToHardCheck,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToRows: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToRows,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToLocalPackages,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToGlobalFirewalls,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToGlobalProofDAG,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToGPack,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToFinalIntegration,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem: concreteFinalCertificatePublicStatusGateSummary.pccPackLinkedToFinalTheorem,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordPresent,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordAccepted,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordChecker,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordDigest,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordDigestMatchesNF,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordConcretePCCPack,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordPccPackDigest,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordPublicConclusionNotEmitted,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional: concreteFinalCertificatePublicStatusGateSummary.checkPCCPackexpRecordClaimBoundaryConditional,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpEnvelopePresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpEnvelopeDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpGenCallGeneratePCCPack,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCoreOnly,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpExcludesAcceptRun,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPackageMatchesConcreteRun,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCheckRecordMatchesConcreteRun,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCheckRecordAccepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCheckRecordChecker,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCheckRecordDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCheckRecordDigestMatchesNF,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCheckRecordClaimBoundaryConditional,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpLinkageGeneratedPackageDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpLinkageCheckRecordDigestMatches,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordPresent,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordAccepted,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordChecker,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordDigest,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordDigestMatchesNF,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: concreteFinalCertificatePublicStatusGateSummary.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0CheckDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0CanonicalByteDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0RowCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0KernelRuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0JsonMaterialized,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0NoFixtureMarkers,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0BootBatchDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0BootAuditDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0LinkedToPCCPack,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0LinkedToCoreDigestMap,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoverageDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0FamilyCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0RequiredFamilyCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0Families,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversIface,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversSched,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversNF,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversTruthEval,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversRel,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversCharge,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversObl,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversArith,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversMode,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversRoute,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversHash,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBoot0B0CoversImport,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0RuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0RequiredRuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0Rules,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasEq,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasSubst,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasRecord,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasDAGInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasLedgerInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasOblTopoInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasTraceInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasFiniteExhaust,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasDPInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasHall,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasRankInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasMinCounterexample,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasIntArith,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasTransport,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasTruthVec,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0HasFiniteRel,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0ProofNodeKindCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0ProofNodeKinds,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpKernelSeed0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0Canonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0NaturalEncoding,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0NaturalEncodingCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0IntegerEncoding,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0IntegerEncodingCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0StringEncoding,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0StringEncodingCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0TopLevelConsumesAllBytes,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0NormalFormSerialization,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0NormalFormSerializationCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpCodec0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0Alg,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0AlgSHA256,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0Bytes,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0BytesCanonicalJson,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0EqualityNotObjectEquality,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpDigest0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0PublicConstructorsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0CriticalKindsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0RouteTokensPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpIfaceDict0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreMatchesExpected,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreB0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreK0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreR0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreH0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreO0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0CoreRel0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0ScaleFactorsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0SelectorBoundsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0SelectorBoundBH,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0SelectorBoundBTheta,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0PolynomialExponent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpSched0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0TagCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0TagsUnique,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0RequiredTagsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0SortCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0RequiredSortsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0ConstructorCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0RequiredConstructorsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0RecordCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpByteLang0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0Checker,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0DigestMatchesNF,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0NFKind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0SuiteId,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0CaseCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0PositiveCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0NegativeCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0CoversB0Accept,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0Materialized,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0ExternalJson,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0AllBootRefsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsMatchBootObjects,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeByteLang0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeCodec0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeDigest0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeSched0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeB0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Accepted: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Checker: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0Checker,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0MaterializedKBundleDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0BootDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0BootDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KImplDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0KImplDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0K0Digest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0K0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0SigmaDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0ReflectionDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ProofInventoryDigest: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0ProofInventoryDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0KernelRuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ConformanceNodeCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0ConformanceNodeCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaTheoremCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0SigmaTheoremCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaProofRefsResolve: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCount: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0ReflectionCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCoverageComplete: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoOpaqueProofRefs: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoExecutableMinSymbols: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0: concreteFinalCertificatePublicStatusGateSummary.generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0,
    concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate: concreteFinalCertificatePublicStatusGateSummary.statusUsesConcreteFinalCertificate,

    publicConclusion: RUNALL_PUBLIC_CONCLUSION0,
  };

  const phaseOrderForSurfaceFreeze = [
    ...ledger.map((entry) => entry.phase),
    'surfaceFreeze',
  ];

  const surface = validateReleaseAuditSurface0(nf, phaseOrderForSurfaceFreeze);

  ledger.push({
    phase: 'surfaceFreeze',
    status: surface.ok ? 'pass' : 'fail',
    digest: digestCanonical0(surface.nf ?? surface.witness ?? null),
  });

  if (!surface.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.surfaceFreeze`,
      path: surface.path,
      witness: surface.witness,
      ledger,
    });
  }

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateConfig0(cfg) {
  if (!isPlainObject(cfg)) {
    return validationReject0([], 'ReleaseAuditConfig0 must be an object', {
      actual: typeof cfg,
    });
  }

  if (!isNonEmptyString(cfg.rootDir)) {
    return validationReject0(['rootDir'], 'ReleaseAuditConfig0 rootDir must be a non-empty string', {
      actual: cfg.rootDir,
    });
  }

  for (const field of [
    'runSyntaxCheck',
    'runRunAll',
    'runMutationCheck',
    'runCliSmoke',
    'runPublicSurfaceFreeze',
    'runMaterializedPublicStatusGate',
    'materializedPublicStatusGateCanonicalEnvelopeBytes',
    'materializedPublicStatusGateRunCliChecks',
    'runFinalCertificatePublicStatusGate',
    'finalCertificatePublicStatusGateCanonicalEnvelopeBytes',
    'runConcreteFinalCertificatePublicStatusGate',
    'concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes',    
  ]) {
    if (typeof cfg[field] !== 'boolean') {
      return validationReject0([field], `ReleaseAuditConfig0 ${field} must be boolean`, {
        actual: cfg[field],
      });
    }
  }

  if (
    cfg.readmeReleaseBoundaryRunner !== null &&
    typeof cfg.readmeReleaseBoundaryRunner !== 'function'
  ) {
    return validationReject0(['readmeReleaseBoundaryRunner'], 'ReleaseAuditConfig0 readmeReleaseBoundaryRunner must be null or a function', {
      actual: typeof cfg.readmeReleaseBoundaryRunner,
    });
  }

  if (
    cfg.publicSurfaceFreezeRunner !== null &&
    typeof cfg.publicSurfaceFreezeRunner !== 'function'
  ) {
    return validationReject0(['publicSurfaceFreezeRunner'], 'ReleaseAuditConfig0 publicSurfaceFreezeRunner must be null or a function', {
      actual: typeof cfg.publicSurfaceFreezeRunner,
    });
  }

  if (
    cfg.materializedPublicStatusGateRunner !== null &&
    typeof cfg.materializedPublicStatusGateRunner !== 'function'
  ) {
    return validationReject0(['materializedPublicStatusGateRunner'], 'ReleaseAuditConfig0 materializedPublicStatusGateRunner must be null or a function', {
      actual: typeof cfg.materializedPublicStatusGateRunner,
    });
  }

  if (
    cfg.finalCertificatePublicStatusGateRunner !== null &&
    typeof cfg.finalCertificatePublicStatusGateRunner !== 'function'
  ) {
    return validationReject0(['finalCertificatePublicStatusGateRunner'], 'ReleaseAuditConfig0 finalCertificatePublicStatusGateRunner must be null or a function', {
      actual: typeof cfg.finalCertificatePublicStatusGateRunner,
    });
  }

  if (
    cfg.finalCertificatePublicStatusGateOutputDir !== null &&
    !isNonEmptyString(cfg.finalCertificatePublicStatusGateOutputDir)
  ) {
    return validationReject0(['finalCertificatePublicStatusGateOutputDir'], 'ReleaseAuditConfig0 finalCertificatePublicStatusGateOutputDir must be null or a non-empty string', {
      actual: cfg.finalCertificatePublicStatusGateOutputDir,
    });
  }  

  if (
    cfg.materializedPublicStatusGateOutputDir !== null &&
    !isNonEmptyString(cfg.materializedPublicStatusGateOutputDir)
  ) {
    return validationReject0(['materializedPublicStatusGateOutputDir'], 'ReleaseAuditConfig0 materializedPublicStatusGateOutputDir must be null or a non-empty string', {
      actual: cfg.materializedPublicStatusGateOutputDir,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConfig0NF',
  });
}

async function validateRequiredFiles0(cfg) {
  for (const relativeFile of [
    ...RELEASE_AUDIT_REQUIRED_MODULES0,
    ...RELEASE_AUDIT_REQUIRED_TESTS0.map((file) => path.join('test', file)),
    'package.json',
    'README.md',
  ]) {
    const absoluteFile = path.join(cfg.rootDir, relativeFile);

    if (!(await pathExists0(absoluteFile))) {
      return validationReject0(['files', relativeFile], 'required release-audit file is missing', {
        relativeFile,
      });
    }
  }

  return validationAccept0({
    kind: 'ReleaseRequiredFiles0NF',
    moduleCount: RELEASE_AUDIT_REQUIRED_MODULES0.length,
    testCount: RELEASE_AUDIT_REQUIRED_TESTS0.length,
  });
}

async function validateNoStaleSrcDuplicates0(cfg) {
  const srcDir = path.join(cfg.rootDir, 'src');

  if (!(await pathExists0(srcDir))) {
    return validationAccept0({
      kind: 'NoStaleSrcDuplicates0NF',
      staleDuplicateCount: 0,
    });
  }

  const srcFiles = await walkFiles0(srcDir);
  const staleDuplicates = [];

  for (const srcFile of srcFiles) {
    if (!srcFile.endsWith('.mjs')) {
      continue;
    }

    const basename = path.basename(srcFile);
    const rootSibling = path.join(cfg.rootDir, basename);

    if (await pathExists0(rootSibling)) {
      staleDuplicates.push({
        srcFile: path.relative(cfg.rootDir, srcFile),
        rootSibling: basename,
      });
    }
  }

  if (staleDuplicates.length > 0) {
    return validationReject0(['src'], 'stale duplicate ES module exists under src', {
      staleDuplicates,
      fix: 'delete or move the stale src duplicate so the root module remains the single active implementation',
    });
  }

  return validationAccept0({
    kind: 'NoStaleSrcDuplicates0NF',
    staleDuplicateCount: 0,
  });
}

async function validatePackageJson0(cfg) {
  const pkg = await readJsonFile0(path.join(cfg.rootDir, 'package.json'));

  if (!pkg.ok) {
    return validationReject0(['package.json'], 'package.json must be readable JSON', pkg.witness);
  }

  const value = pkg.value;

  if (value.main !== './index.mjs') {
    return validationReject0(['package.json', 'main'], 'package.json main must point to ./index.mjs', {
      actual: value.main,
    });
  }

  if (!isPlainObject(value.exports)) {
    return validationReject0(['package.json', 'exports'], 'package.json exports must be an object', {
      actual: typeof value.exports,
    });
  }

  const expectedExports = {
    '.': './index.mjs',
    './runall0': './pcc-runall0.mjs',
    './integrated-pipeline0': './pcc-integrated-pipeline0.mjs',
    './accept-run0': './pcc-accept-run0.mjs',
    './release-audit0': './pcc-release-audit0.mjs',
    './final-certificate0': './pcc-final-certificate-materialized0.mjs',
    './final-certificate-public-status0': './pcc-final-certificate-public-status0.mjs',
    './release-audit-final-certificate-gate0': './pcc-release-audit-final-certificate-gate0.mjs',
  };

  for (const [key, expected] of Object.entries(expectedExports)) {
    if (value.exports[key] !== expected) {
      return validationReject0(['package.json', 'exports', key], 'package export mismatch', {
        expected,
        actual: value.exports[key],
      });
    }
  }

  if (!isPlainObject(value.bin)) {
    return validationReject0(['package.json', 'bin'], 'package.json bin must be an object', {
      actual: typeof value.bin,
    });
  }

  if (value.bin['pnp-runall0'] !== './bin/runall0.mjs') {
    return validationReject0(['package.json', 'bin', 'pnp-runall0'], 'pnp-runall0 bin target mismatch', {
      actual: value.bin['pnp-runall0'],
    });
  }

  if (value.bin['pnp-release-audit0'] !== './bin/release-audit0.mjs') {
    return validationReject0(['package.json', 'bin', 'pnp-release-audit0'], 'pnp-release-audit0 bin target mismatch', {
      actual: value.bin['pnp-release-audit0'],
    });
  }

  if (!isPlainObject(value.scripts)) {
    return validationReject0(['package.json', 'scripts'], 'package.json scripts must be an object', {
      actual: typeof value.scripts,
    });
  }

  for (const script of RELEASE_AUDIT_REQUIRED_SCRIPTS0) {
    if (!isNonEmptyString(value.scripts[script])) {
      return validationReject0(['package.json', 'scripts', script], 'required package script is missing', {
        script,
      });
    }
  }

  return validationAccept0({
    kind: 'PackageJsonReleaseSurface0NF',
  });
}

async function validateTestInventory0(cfg) {
  const testDir = path.join(cfg.rootDir, 'test');
  const actualTests = (await fs.readdir(testDir))
    .filter((file) => file.endsWith('.test.mjs'))
    .sort();

  for (const required of RELEASE_AUDIT_REQUIRED_TESTS0) {
    if (!actualTests.includes(required)) {
      return validationReject0(['test', required], 'required test file is missing', {
        required,
      });
    }
  }

  for (const testFile of actualTests) {
    const expectedModule = expectedModuleForTest0(testFile);

    if (expectedModule === null) {
      continue;
    }

    const modulePath = path.join(cfg.rootDir, expectedModule);

    if (!(await pathExists0(modulePath))) {
      return validationReject0(['test', testFile], 'test file appears orphaned because its expected module is missing', {
        testFile,
        expectedModule,
      });
    }
  }

  return validationAccept0({
    kind: 'TestInventory0NF',
    testCount: actualTests.length,
  });
}

async function validateReadme0(cfg) {
  const readmePath = path.join(cfg.rootDir, 'README.md');

  const runner = typeof cfg.readmeReleaseBoundaryRunner === 'function'
    ? cfg.readmeReleaseBoundaryRunner
    : async (runnerConfig) => {
        const {
          CheckReadmeReleaseBoundary0,
        } = await import('./pcc-readme-release-boundary0.mjs');

        return CheckReadmeReleaseBoundary0(runnerConfig);
      };

  const record = await runner({
    rootDir: cfg.rootDir,
    readmePath,
  });

  if (record?.tag !== 'accept') {
    return validationReject0(['README.md'], 'README release boundary checker rejected', {
      inner: compactReject0(record),
    });
  }

  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['README.md', 'NF'], 'README release boundary checker must emit an NF object', {
      actual: typeof nf,
    });
  }

  if (nf.kind !== 'ReadmeReleaseBoundary0NF') {
    return validationReject0(['README.md', 'NF', 'kind'], 'README release boundary checker emitted the wrong NF kind', {
      actual: nf.kind,
    });
  }

  if (!Number.isInteger(nf.requiredSnippetCount) || nf.requiredSnippetCount <= 0) {
    return validationReject0(['README.md', 'NF', 'requiredSnippetCount'], 'README release boundary checker must count required snippets', {
      actual: nf.requiredSnippetCount,
    });
  }

  if (!Number.isInteger(nf.forbiddenSnippetCount) || nf.forbiddenSnippetCount <= 0) {
    return validationReject0(['README.md', 'NF', 'forbiddenSnippetCount'], 'README release boundary checker must count forbidden snippets', {
      actual: nf.forbiddenSnippetCount,
    });
  }

  if (nf.conditionalClaimBoundaryFrozen !== true) {
    return validationReject0(['README.md', 'NF', 'conditionalClaimBoundaryFrozen'], 'README release boundary checker must certify conditionalClaimBoundaryFrozen=true', {
      actual: nf.conditionalClaimBoundaryFrozen,
    });
  }

  if (nf.staleLayoutWordingRejected !== true) {
    return validationReject0(['README.md', 'NF', 'staleLayoutWordingRejected'], 'README release boundary checker must certify staleLayoutWordingRejected=true', {
      actual: nf.staleLayoutWordingRejected,
    });
  }

  return validationAccept0({
    kind: 'ReadmeReleaseWording0NF',
    readmeBoundaryDigest: record.Digest ?? record.digest,
    requiredSnippetCount: nf.requiredSnippetCount,
    forbiddenSnippetCount: nf.forbiddenSnippetCount,
    conditionalClaimBoundaryFrozen: nf.conditionalClaimBoundaryFrozen,
    staleLayoutWordingRejected: nf.staleLayoutWordingRejected,
  });
}

async function validateSyntax0(cfg) {
  if (cfg.runSyntaxCheck !== true) {
    return validationAccept0({
      kind: 'SyntaxCheckSkipped0NF',
    });
  }

  for (const relativeFile of RELEASE_AUDIT_REQUIRED_MODULES0) {
    const absoluteFile = path.join(cfg.rootDir, relativeFile);
    const child = spawnSync(process.execPath, ['--check', absoluteFile], {
      cwd: cfg.rootDir,
      encoding: 'utf8',
    });

    if (child.status !== 0) {
      return validationReject0(['syntax', relativeFile], 'node --check failed for release module', {
        relativeFile,
        stdout: child.stdout,
        stderr: child.stderr,
      });
    }
  }

  return validationAccept0({
    kind: 'SyntaxCheck0NF',
    checkedCount: RELEASE_AUDIT_REQUIRED_MODULES0.length,
  });
}

async function validateRunAllDeterminism0(cfg) {
  if (cfg.runRunAll !== true) {
    return validationAccept0({
      kind: 'RunAllDeterminismSkipped0NF',
    });
  }

  const first = await RunAll0();
  const second = await RunAll0();

  if (first.tag !== 'accept') {
    return validationReject0(['RunAll0', 'first'], 'first RunAll0 execution did not accept', compactReject0(first));
  }

  if (second.tag !== 'accept') {
    return validationReject0(['RunAll0', 'second'], 'second RunAll0 execution did not accept', compactReject0(second));
  }

  if (stableStringify0(first.Digest) !== stableStringify0(second.Digest)) {
    return validationReject0(['RunAll0', 'Digest'], 'RunAll0 is not deterministic across fresh executions', {
      first: first.Digest,
      second: second.Digest,
    });
  }

  return validationAccept0({
    kind: 'RunAllDeterminism0NF',
    digest: first.Digest,
  });
}

async function validateRunAllMutation0(cfg) {
  if (cfg.runMutationCheck !== true) {
    return validationAccept0({
      kind: 'RunAllMutationCheckSkipped0NF',
    });
  }

  const input = typeof cfg.mutationInputFactory === 'function'
    ? cfg.mutationInputFactory()
    : makeSyntheticRunAllInput0();

  const runner = typeof cfg.mutationRunner === 'function'
    ? cfg.mutationRunner
    : CheckRunAll0;

  const before = stableStringify0(input);
  const out = await runner(input);
  const after = stableStringify0(input);

  if (out.tag !== 'accept') {
    return validationReject0(['CheckRunAll0'], 'CheckRunAll0 did not accept the mutation-check input', compactReject0(out));
  }

  if (before !== after) {
    return validationReject0(['CheckRunAll0', 'mutation'], 'CheckRunAll0 mutated its input object', {
      beforeDigest: digestCanonical0(before),
      afterDigest: digestCanonical0(after),
    });
  }

  return validationAccept0({
    kind: 'RunAllMutationCheck0NF',
    digest: out.Digest,
  });
}

async function validateCliSmoke0(cfg) {
  if (cfg.runCliSmoke !== true) {
    return validationAccept0({
      kind: 'CliSmokeSkipped0NF',
    });
  }

  const commands = [
    ['bin/runall0.mjs'],
    ['bin/runall0.mjs', '--full'],
    ['bin/release-audit0.mjs'],
  ];

  for (const args of commands) {
    const child = spawnSync(process.execPath, args.map((entry) => path.join(cfg.rootDir, entry)), {
      cwd: cfg.rootDir,
      encoding: 'utf8',
    });

    if (child.status !== 0) {
      return validationReject0(['cli', args[0]], 'release CLI smoke command failed', {
        args,
        stdout: child.stdout,
        stderr: child.stderr,
      });
    }

    let parsed;

    try {
      parsed = JSON.parse(child.stdout);
    } catch (error) {
      return validationReject0(['cli', args[0]], 'release CLI did not emit JSON', {
        args,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['cli', args[0]], 'release CLI emitted a non-accept record', {
        args,
        parsed,
      });
    }
  }

  return validationAccept0({
    kind: 'CliSmoke0NF',
    commandCount: commands.length,
  });
}

async function validatePublicSurfaceFreeze0(cfg) {
  if (cfg.runPublicSurfaceFreeze !== true) {
    return validationAccept0({
      kind: 'PublicSurfaceFreezeSkipped0NF',
    });
  }

  const runner = typeof cfg.publicSurfaceFreezeRunner === 'function'
    ? cfg.publicSurfaceFreezeRunner
    : async (runnerConfig) => {
        const mod = await import('./pcc-public-surface-freeze0.mjs');

        return mod.CheckPublicEntryReleaseSurface0(runnerConfig);
      };

  const record = await runner({
    rootDir: cfg.rootDir,
  });

  if (record?.tag !== 'accept') {
    return validationReject0(['publicSurfaceFreeze'], 'public release surface freeze checker rejected', {
      inner: compactReject0(record),
    });
  }

  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['publicSurfaceFreeze', 'NF'], 'public release surface freeze checker must emit an NF object', {
      actual: typeof nf,
    });
  }

  if (nf.kind !== 'PublicEntryReleaseSurface0NF') {
    return validationReject0(['publicSurfaceFreeze', 'NF', 'kind'], 'public release surface freeze checker emitted the wrong NF kind', {
      actual: nf.kind,
    });
  }

  if (nf.surfaceFrozen !== true) {
    return validationReject0(['publicSurfaceFreeze', 'NF', 'surfaceFrozen'], 'public release surface freeze checker must certify surfaceFrozen=true', {
      actual: nf.surfaceFrozen,
    });
  }

  if (!Number.isInteger(nf.publicEntryExportCount) || nf.publicEntryExportCount <= 0) {
    return validationReject0(['publicSurfaceFreeze', 'NF', 'publicEntryExportCount'], 'public release surface freeze checker must count public entry exports', {
      actual: nf.publicEntryExportCount,
    });
  }

  if (!Number.isInteger(nf.packageExportCount) || nf.packageExportCount <= 0) {
    return validationReject0(['publicSurfaceFreeze', 'NF', 'packageExportCount'], 'public release surface freeze checker must count package exports', {
      actual: nf.packageExportCount,
    });
  }

  if (!Number.isInteger(nf.packageBinCount) || nf.packageBinCount <= 0) {
    return validationReject0(['publicSurfaceFreeze', 'NF', 'packageBinCount'], 'public release surface freeze checker must count package bin entries', {
      actual: nf.packageBinCount,
    });
  }

  if (!Number.isInteger(nf.packageScriptCount) || nf.packageScriptCount <= 0) {
    return validationReject0(['publicSurfaceFreeze', 'NF', 'packageScriptCount'], 'public release surface freeze checker must count package scripts', {
      actual: nf.packageScriptCount,
    });
  }

  return validationAccept0({
    kind: 'ReleasePublicSurfaceFreeze0NF',
    publicEntryExportCount: nf.publicEntryExportCount,
    packageExportCount: nf.packageExportCount,
    packageBinCount: nf.packageBinCount,
    packageScriptCount: nf.packageScriptCount,
    surfaceFrozen: nf.surfaceFrozen,
    publicSurfaceDigest: record.Digest ?? record.digest,
  });
}

async function validateMaterializedPublicStatusGate0(cfg) {
  if (cfg.runMaterializedPublicStatusGate !== true) {
    return validationAccept0({
      kind: 'MaterializedPublicStatusGateSkipped0NF',
    });
  }

  const usesTemporaryOutputDir = !isNonEmptyString(cfg.materializedPublicStatusGateOutputDir);
  const outputDir = usesTemporaryOutputDir
    ? await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-materialized-public-status-'))
    : cfg.materializedPublicStatusGateOutputDir;

  const runner = typeof cfg.materializedPublicStatusGateRunner === 'function'
    ? cfg.materializedPublicStatusGateRunner
    : CheckMaterializedPublicStatusRoundtrip0;

  try {
    const record = await runner({
      outputDir,
      canonicalEnvelopeBytes: cfg.materializedPublicStatusGateCanonicalEnvelopeBytes,
      runCliChecks: cfg.materializedPublicStatusGateRunCliChecks,
    });

    if (record?.tag !== 'accept') {
      return validationReject0(['materializedPublicStatusGate'], 'materialized public status roundtrip gate rejected', {
        inner: compactReject0(record),
      });
    }

    const nf = record.NF ?? record.nf;

    if (!isPlainObject(nf)) {
      return validationReject0(['materializedPublicStatusGate', 'NF'], 'materialized public status roundtrip gate must emit an NF object', {
        actual: typeof nf,
      });
    }

    if (nf.kind !== 'MaterializedPublicStatusRoundtrip0NF') {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'kind'], 'materialized public status roundtrip gate emitted the wrong NF kind', {
        actual: nf.kind,
      });
    }

    if (nf.deterministic !== true) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'deterministic'], 'materialized public status roundtrip gate must prove deterministic fixture bytes', {
        actual: nf.deterministic,
      });
    }

    if (nf.materializedPath !== true) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'materializedPath'], 'materialized public status roundtrip gate must certify materializedPath=true', {
        actual: nf.materializedPath,
      });
    }

    if (nf.syntheticRunAll !== false) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'syntheticRunAll'], 'materialized public status roundtrip gate must remain separate from synthetic RunAll0', {
        actual: nf.syntheticRunAll,
      });
    }

    if (nf.acceptedPublicConclusionOnly !== true) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'acceptedPublicConclusionOnly'], 'materialized public status roundtrip gate must prove only accepted replay emits the public conclusion', {
        actual: nf.acceptedPublicConclusionOnly,
      });
    }

    if (!Number.isInteger(nf.fileCount) || nf.fileCount < 4) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'fileCount'], 'materialized public status roundtrip gate must check the package plus all public status fixtures', {
        actual: nf.fileCount,
      });
    }

    if (!Array.isArray(nf.directRecords) || nf.directRecords.length < 4) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'directRecords'], 'materialized public status roundtrip gate must include direct checker records', {
        actual: nf.directRecords,
      });
    }

    if (
      cfg.materializedPublicStatusGateRunCliChecks === true &&
      (!Array.isArray(nf.cliRecords) || nf.cliRecords.length < 4)
    ) {
      return validationReject0(['materializedPublicStatusGate', 'NF', 'cliRecords'], 'materialized public status roundtrip gate must include CLI checker records when CLI checks are enabled', {
        actual: nf.cliRecords,
      });
    }

    return validationAccept0({
      kind: 'ReleaseMaterializedPublicStatusGate0NF',
      outputDir: usesTemporaryOutputDir ? 'temporary' : outputDir,
      canonicalEnvelopeBytes: cfg.materializedPublicStatusGateCanonicalEnvelopeBytes,
      runCliChecks: cfg.materializedPublicStatusGateRunCliChecks,
      deterministic: nf.deterministic,
      materializedPath: nf.materializedPath,
      syntheticRunAll: nf.syntheticRunAll,
      acceptedPublicConclusionOnly: nf.acceptedPublicConclusionOnly,
      fileCount: nf.fileCount,
      directRecordCount: nf.directRecords.length,
      cliRecordCount: Array.isArray(nf.cliRecords) ? nf.cliRecords.length : 0,
      gateDigest: record.Digest ?? record.digest,
    });
  } finally {
    if (usesTemporaryOutputDir) {
      await fs.rm(outputDir, {
        recursive: true,
        force: true,
      });
    }
  }
}async function validateFinalCertificatePublicStatusGate0(cfg) {
  if (cfg.runFinalCertificatePublicStatusGate !== true) {
    return validationAccept0({
      kind: 'ReleaseAuditFinalCertificatePublicStatusGate0NF',
      enabled: false,
      skipped: true,
      outputDir: cfg.finalCertificatePublicStatusGateOutputDir,
      canonicalEnvelopeBytes: cfg.finalCertificatePublicStatusGateCanonicalEnvelopeBytes,
      status: null,
      verdict: null,
      materializedPath: false,
      syntheticRunAll: null,
      publicConclusionEmitted: false,
      publicConclusion: null,
      certificateDigest: null,
      finalVerdictDigest: null,
      acceptRunDigest: null,
      pccPackDigest: null,
      canonicalByteRoots: null,
      acceptanceTranscript: null,
      releaseAuditAttached: false,
      releaseAuditDigest: null,
      releaseAuditStatus: 'skipped',
      gateDigest: null,
    });
  }

  const runner = typeof cfg.finalCertificatePublicStatusGateRunner === 'function'
    ? cfg.finalCertificatePublicStatusGateRunner
    : async () => {
        if (cfg.finalCertificatePublicStatusGateOutputDir !== null) {
          const written = await writeFinalCertificatePublicStatusFiles0(
            cfg.finalCertificatePublicStatusGateOutputDir,
          );

          return written.checked;
        }

        const envelope = await makeFinalCertificatePublicStatus0();

        return CheckFinalCertificatePublicStatus0(envelope, {
          checkReleaseAuditRecord: false,
        });
      };

  const record = await runner({
    outputDir: cfg.finalCertificatePublicStatusGateOutputDir,
    canonicalEnvelopeBytes: cfg.finalCertificatePublicStatusGateCanonicalEnvelopeBytes,
  });

  if (record?.tag !== 'accept') {
    return validationReject0(['finalCertificatePublicStatusGate'], 'final-certificate public-status gate rejected', {
      inner: compactReject0(record),
    });
  }

  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF'], 'final-certificate public-status gate must emit an NF object', {
      actual: typeof nf,
    });
  }

  if (nf.kind !== 'FinalCertificatePublicStatus0NF') {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'kind'], 'final-certificate public-status gate emitted wrong NF kind', {
      actual: nf.kind,
    });
  }

  if (nf.materializedPath !== true) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'materializedPath'], 'final-certificate public-status gate must certify materializedPath=true', {
      actual: nf.materializedPath,
    });
  }

  if (nf.syntheticRunAll !== false) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'syntheticRunAll'], 'final-certificate public-status gate must remain separate from synthetic RunAll0', {
      actual: nf.syntheticRunAll,
    });
  }

  if (nf.status !== 'accepted' || nf.verdict !== 'accept') {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'status'], 'final-certificate public-status gate must be accepted', {
      status: nf.status,
      verdict: nf.verdict,
    });
  }

  if (nf.publicConclusionEmitted !== true) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'publicConclusionEmitted'], 'accepted final-certificate public-status gate must emit the public conclusion', {
      actual: nf.publicConclusionEmitted,
    });
  }

  if (!sameReleaseAuditPublicConclusion0(nf.publicConclusion)) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'publicConclusion'], 'final-certificate public conclusion mismatch', {
      actual: nf.publicConclusion,
    });
  }

  for (const field of [
    'certificateDigest',
    'finalVerdictDigest',
    'acceptRunDigest',
    'pccPackDigest',
  ]) {
    if (!isDigestLike0(nf[field])) {
      return validationReject0(['finalCertificatePublicStatusGate', 'NF', field], `final-certificate public-status gate must expose ${field}`, {
        actual: nf[field],
      });
    }
  }

  if (!isPlainObject(nf.canonicalByteRoots)) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'canonicalByteRoots'], 'final-certificate public-status gate must expose canonicalByteRoots', {
      actual: typeof nf.canonicalByteRoots,
    });
  }

  if (!isPlainObject(nf.acceptanceTranscript)) {
    return validationReject0(['finalCertificatePublicStatusGate', 'NF', 'acceptanceTranscript'], 'final-certificate public-status gate must expose acceptanceTranscript', {
      actual: typeof nf.acceptanceTranscript,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditFinalCertificatePublicStatusGate0NF',
    enabled: true,
    skipped: false,
    outputDir: cfg.finalCertificatePublicStatusGateOutputDir,
    canonicalEnvelopeBytes: cfg.finalCertificatePublicStatusGateCanonicalEnvelopeBytes,
    status: nf.status,
    verdict: nf.verdict,
    materializedPath: nf.materializedPath,
    syntheticRunAll: nf.syntheticRunAll,
    publicConclusionEmitted: nf.publicConclusionEmitted,
    publicConclusion: nf.publicConclusion,
    certificateDigest: nf.certificateDigest,
    finalVerdictDigest: nf.finalVerdictDigest,
    acceptRunDigest: nf.acceptRunDigest,
    pccPackDigest: nf.pccPackDigest,
    canonicalByteRoots: nf.canonicalByteRoots,
    acceptanceTranscript: nf.acceptanceTranscript,
    releaseAuditAttached: nf.releaseAuditAttached,
    releaseAuditDigest: nf.releaseAuditDigest,
    releaseAuditStatus: nf.releaseAuditStatus,
    gateDigest: record.Digest ?? record.digest,
  });
}

function summarizeFinalCertificatePublicStatusGateNF0(nf, cfg) {
  const summary = {
    kind: 'ReleaseAuditFinalCertificatePublicStatusGateSummary0',
    enabled: cfg.runFinalCertificatePublicStatusGate,
    skipped: cfg.runFinalCertificatePublicStatusGate !== true,
    outputDir: cfg.finalCertificatePublicStatusGateOutputDir,
    canonicalEnvelopeBytes: cfg.finalCertificatePublicStatusGateCanonicalEnvelopeBytes,
    status: null,
    verdict: null,
    materializedPath: false,
    syntheticRunAll: null,
    publicConclusionEmitted: false,
    publicConclusion: null,
    certificateDigest: null,
    finalVerdictDigest: null,
    acceptRunDigest: null,
    pccPackDigest: null,
    canonicalByteRoots: null,
    acceptanceTranscript: null,
    releaseAuditAttached: false,
    releaseAuditDigest: null,
    releaseAuditStatus: cfg.runFinalCertificatePublicStatusGate === true ? 'not-attached' : 'skipped',
    gateDigest: null,
  };

  if (!isPlainObject(nf)) {
    return summary;
  }

  return {
    ...summary,
    skipped: nf.skipped === true,
    status: nf.status ?? null,
    verdict: nf.verdict ?? null,
    materializedPath: nf.materializedPath ?? false,
    syntheticRunAll: nf.syntheticRunAll ?? null,
    publicConclusionEmitted: nf.publicConclusionEmitted ?? false,
    publicConclusion: nf.publicConclusion ?? null,
    certificateDigest: nf.certificateDigest ?? null,
    finalVerdictDigest: nf.finalVerdictDigest ?? null,
    acceptRunDigest: nf.acceptRunDigest ?? null,
    pccPackDigest: nf.pccPackDigest ?? null,
    canonicalByteRoots: nf.canonicalByteRoots ?? null,
    acceptanceTranscript: nf.acceptanceTranscript ?? null,
    releaseAuditAttached: nf.releaseAuditAttached ?? false,
    releaseAuditDigest: nf.releaseAuditDigest ?? null,
    releaseAuditStatus: nf.releaseAuditStatus ?? null,
    gateDigest: nf.gateDigest ?? null,
  };
}

function sameReleaseAuditPublicConclusion0(value) {
  return (
    isPlainObject(value) &&
    value.antecedent === 'CheckPCCPackexp(GeneratePCCPack())=accept' &&
    value.consequent === 'P = NP' &&
    value.conditional === true
  );
}

function isDigestLike0(value) {
  return (
    isPlainObject(value) &&
    typeof value.hex === 'string' &&
    /^[0-9a-f]{64}$/.test(value.hex)
  );
}

function summarizeMaterializedPublicStatusGateNF0(gateNF, cfg) {
  if (!isPlainObject(gateNF) || gateNF.kind === 'MaterializedPublicStatusGateSkipped0NF') {
    return {
      kind: 'ReleaseMaterializedPublicStatusGateSummary0',
      enabled: cfg.runMaterializedPublicStatusGate === true,
      skipped: true,
      outputDir: null,
      canonicalEnvelopeBytes: cfg.materializedPublicStatusGateCanonicalEnvelopeBytes,
      runCliChecks: cfg.materializedPublicStatusGateRunCliChecks,
      deterministic: null,
      materializedPath: null,
      syntheticRunAll: null,
      acceptedPublicConclusionOnly: null,
      fileCount: 0,
      directRecordCount: 0,
      cliRecordCount: 0,
      gateDigest: null,
    };
  }

  return {
    kind: 'ReleaseMaterializedPublicStatusGateSummary0',
    enabled: true,
    skipped: false,
    outputDir: gateNF.outputDir ?? null,
    canonicalEnvelopeBytes: gateNF.canonicalEnvelopeBytes ?? cfg.materializedPublicStatusGateCanonicalEnvelopeBytes,
    runCliChecks: gateNF.runCliChecks ?? cfg.materializedPublicStatusGateRunCliChecks,
    deterministic: gateNF.deterministic === true,
    materializedPath: gateNF.materializedPath === true,
    syntheticRunAll: gateNF.syntheticRunAll === false ? false : gateNF.syntheticRunAll ?? null,
    acceptedPublicConclusionOnly: gateNF.acceptedPublicConclusionOnly === true,
    fileCount: gateNF.fileCount ?? null,
    directRecordCount: gateNF.directRecordCount ?? null,
    cliRecordCount: gateNF.cliRecordCount ?? null,
    gateDigest: gateNF.gateDigest ?? null,
  };
}

function summarizePublicSurfaceFreezeNF0(publicSurfaceNF, cfg) {
  if (!isPlainObject(publicSurfaceNF) || publicSurfaceNF.kind === 'PublicSurfaceFreezeSkipped0NF') {
    return {
      kind: 'ReleasePublicSurfaceFreezeSummary0',
      enabled: cfg.runPublicSurfaceFreeze === true,
      skipped: true,
      publicEntryExportCount: 0,
      packageExportCount: 0,
      packageBinCount: 0,
      packageScriptCount: 0,
      surfaceFrozen: null,
      publicSurfaceDigest: null,
    };
  }

  return {
    kind: 'ReleasePublicSurfaceFreezeSummary0',
    enabled: true,
    skipped: false,
    publicEntryExportCount: publicSurfaceNF.publicEntryExportCount ?? null,
    packageExportCount: publicSurfaceNF.packageExportCount ?? null,
    packageBinCount: publicSurfaceNF.packageBinCount ?? null,
    packageScriptCount: publicSurfaceNF.packageScriptCount ?? null,
    surfaceFrozen: publicSurfaceNF.surfaceFrozen === true,
    publicSurfaceDigest: publicSurfaceNF.publicSurfaceDigest ?? null,
  };
}


async function validateConcreteFinalCertificatePublicStatusGate0(cfg) {
  if (cfg.runConcreteFinalCertificatePublicStatusGate !== true) {
    return validationAccept0({
      kind: 'ReleaseAuditConcreteFinalCertificatePublicStatusGate0NF',
      enabled: false,
      skipped: true,
      outputDir: cfg.concreteFinalCertificatePublicStatusGateOutputDir,
      canonicalEnvelopeBytes: cfg.concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes,
      status: null,
      verdict: null,
      materializedPath: false,
      syntheticRunAll: null,
      publicConclusionEmitted: false,
      publicConclusion: null,
      certificateDigest: null,
      finalVerdictDigest: null,
      acceptRunDigest: null,
      pccPackDigest: null,
      canonicalByteRoots: null,
      acceptanceTranscript: null,
      releaseAuditAttached: false,
      releaseAuditDigest: null,
      releaseAuditStatus: 'skipped',
      concreteRows: false,
      concreteLocalPackages: false,
      concreteGlobalFirewalls: false,
      concreteGlobalProofDAG: false,
    concreteKBundle: false,
    kBundleKernelRuleCoverageComplete: false,
    kBundleSigmaProofRefsResolve: false,
    kBundleReflectionProofRefsResolve: false,
    concreteHardCheck: false,
    hardCheckerCoverageComplete: false,
    hardRowKeyCoverageComplete: false,
    hardRoutePriorityComplete: false,
    hardProofRefPolicyComplete: false,
    hardHashDisciplineComplete: false,
    hardNoMinCoverageComplete: false,
    hardImportPolicyComplete: false,
    hardReflectionPolicyComplete: false,
    hardBoundsPolicyComplete: false,
    hardDiagnosticsPolicyComplete: false,
    concreteFinalIntegration: false,
    finalIntegrationConcreteGlobalProofDAG: false,
    finalIntegrationGPackFieldCoverageComplete: false,
    finalIntegrationRowFamGCoverageComplete: false,
    finalIntegrationUsesGPack: false,
    rowFamGUsesGPack: false,
    finalTheoremUsesFinalIntegration: false,
    rowFamFinalUsesFinalTheorem: false,
    finalMatchUsesGPack: false,
    satDecisionUsesGPack: false,
    concretePCCPack: false,
    concretePCCPackCoverageDigest: false,
    pccPackPublicConclusionOnlyAfterAcceptRun: false,
    pccPackLinkedToKBundle: false,
    pccPackLinkedToHardCheck: false,
    pccPackLinkedToRows: false,
    pccPackLinkedToLocalPackages: false,
    pccPackLinkedToGlobalFirewalls: false,
    pccPackLinkedToGlobalProofDAG: false,
    pccPackLinkedToGPack: false,
    pccPackLinkedToFinalIntegration: false,
    pccPackLinkedToFinalTheorem: false,
    checkPCCPackexpRecordPresent: false,
    checkPCCPackexpRecordAccepted: false,
    checkPCCPackexpRecordChecker: false,
    checkPCCPackexpRecordDigest: false,
    checkPCCPackexpRecordDigestMatchesNF: false,
    checkPCCPackexpRecordConcretePCCPack: false,
    checkPCCPackexpRecordPccPackDigest: false,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: false,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: false,
    checkPCCPackexpRecordPublicConclusionNotEmitted: false,
    checkPCCPackexpRecordClaimBoundaryConditional: false,
    generatedPCCPackexpEnvelopePresent: false,
    generatedPCCPackexpEnvelopeDigest: false,
    generatedPCCPackexpGenCallGeneratePCCPack: false,
    generatedPCCPackexpCoreOnly: false,
    generatedPCCPackexpExcludesAcceptRun: false,
    generatedPCCPackexpPackageMatchesConcreteRun: false,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: false,
    generatedPCCPackexpCheckRecordAccepted: false,
    generatedPCCPackexpCheckRecordChecker: false,
    generatedPCCPackexpCheckRecordDigest: false,
    generatedPCCPackexpCheckRecordDigestMatchesNF: false,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: false,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: false,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: false,
    checkGeneratedPCCPackexpRecordPresent: false,
    checkGeneratedPCCPackexpRecordAccepted: false,
    checkGeneratedPCCPackexpRecordChecker: false,
    checkGeneratedPCCPackexpRecordDigest: false,
    checkGeneratedPCCPackexpRecordDigestMatchesNF: false,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: false,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: false,
    generatedPCCPackexpBoot0: false,
    generatedPCCPackexpBoot0Accepted: false,
    generatedPCCPackexpBoot0Kind: false,
    generatedPCCPackexpBoot0Digest: false,
    generatedPCCPackexpBoot0CheckDigest: false,
    generatedPCCPackexpBoot0CanonicalByteDigest: false,
    generatedPCCPackexpBoot0RowCount: false,
    generatedPCCPackexpBoot0KernelRuleCount: false,
    generatedPCCPackexpBoot0JsonMaterialized: false,
    generatedPCCPackexpBoot0NoFixtureMarkers: false,
    generatedPCCPackexpBoot0BootBatchDigest: false,
    generatedPCCPackexpBoot0BootAuditDigest: false,
    generatedPCCPackexpBoot0LinkedToPCCPack: false,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap: false,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage: false,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap: false,
    generatedPCCPackexpBoot0B0Accepted: false,
    generatedPCCPackexpBoot0B0Digest: false,
    generatedPCCPackexpBoot0B0CoverageDigest: false,
    generatedPCCPackexpBoot0B0FamilyCount: false,
    generatedPCCPackexpBoot0B0RequiredFamilyCount: false,
    generatedPCCPackexpBoot0B0Families: false,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent: false,
    generatedPCCPackexpBoot0B0CoversIface: false,
    generatedPCCPackexpBoot0B0CoversSched: false,
    generatedPCCPackexpBoot0B0CoversNF: false,
    generatedPCCPackexpBoot0B0CoversTruthEval: false,
    generatedPCCPackexpBoot0B0CoversRel: false,
    generatedPCCPackexpBoot0B0CoversCharge: false,
    generatedPCCPackexpBoot0B0CoversObl: false,
    generatedPCCPackexpBoot0B0CoversArith: false,
    generatedPCCPackexpBoot0B0CoversMode: false,
    generatedPCCPackexpBoot0B0CoversRoute: false,
    generatedPCCPackexpBoot0B0CoversHash: false,
    generatedPCCPackexpBoot0B0CoversImport: false,
    generatedPCCPackexpKernelSeed0: false,
    generatedPCCPackexpKernelSeed0Accepted: false,
    generatedPCCPackexpKernelSeed0Kind: false,
    generatedPCCPackexpKernelSeed0Digest: false,
    generatedPCCPackexpKernelSeed0RuleCount: false,
    generatedPCCPackexpKernelSeed0RequiredRuleCount: false,
    generatedPCCPackexpKernelSeed0Rules: false,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent: false,
    generatedPCCPackexpKernelSeed0HasEq: false,
    generatedPCCPackexpKernelSeed0HasSubst: false,
    generatedPCCPackexpKernelSeed0HasRecord: false,
    generatedPCCPackexpKernelSeed0HasDAGInd: false,
    generatedPCCPackexpKernelSeed0HasLedgerInd: false,
    generatedPCCPackexpKernelSeed0HasOblTopoInd: false,
    generatedPCCPackexpKernelSeed0HasTraceInd: false,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust: false,
    generatedPCCPackexpKernelSeed0HasDPInd: false,
    generatedPCCPackexpKernelSeed0HasHall: false,
    generatedPCCPackexpKernelSeed0HasRankInd: false,
    generatedPCCPackexpKernelSeed0HasMinCounterexample: false,
    generatedPCCPackexpKernelSeed0HasIntArith: false,
    generatedPCCPackexpKernelSeed0HasTransport: false,
    generatedPCCPackexpKernelSeed0HasTruthVec: false,
    generatedPCCPackexpKernelSeed0HasFiniteRel: false,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount: false,
    generatedPCCPackexpKernelSeed0ProofNodeKinds: false,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: false,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: false,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: false,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent: false,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches: false,
    generatedPCCPackexpCodec0: false,
    generatedPCCPackexpCodec0Accepted: false,
    generatedPCCPackexpCodec0Kind: false,
    generatedPCCPackexpCodec0Digest: false,
    generatedPCCPackexpCodec0Canonical: false,
    generatedPCCPackexpCodec0NaturalEncoding: false,
    generatedPCCPackexpCodec0NaturalEncodingCanonical: false,
    generatedPCCPackexpCodec0IntegerEncoding: false,
    generatedPCCPackexpCodec0IntegerEncodingCanonical: false,
    generatedPCCPackexpCodec0StringEncoding: false,
    generatedPCCPackexpCodec0StringEncodingCanonical: false,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes: false,
    generatedPCCPackexpCodec0NormalFormSerialization: false,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical: false,
    generatedPCCPackexpCodec0PiBootDigestMatches: false,
    generatedPCCPackexpDigest0: false,
    generatedPCCPackexpDigest0Accepted: false,
    generatedPCCPackexpDigest0Kind: false,
    generatedPCCPackexpDigest0Digest: false,
    generatedPCCPackexpDigest0Alg: false,
    generatedPCCPackexpDigest0AlgSHA256: false,
    generatedPCCPackexpDigest0Bytes: false,
    generatedPCCPackexpDigest0BytesCanonicalJson: false,
    generatedPCCPackexpDigest0EqualityNotObjectEquality: false,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: false,
    generatedPCCPackexpDigest0PiBootDigestMatches: false,
    generatedPCCPackexpIfaceDict0: false,
    generatedPCCPackexpIfaceDict0Accepted: false,
    generatedPCCPackexpIfaceDict0Kind: false,
    generatedPCCPackexpIfaceDict0Digest: false,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount: false,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: false,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols: false,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent: false,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent: false,
    generatedPCCPackexpIfaceDict0RouteTokensPresent: false,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches: false,
    generatedPCCPackexpSched0: false,
    generatedPCCPackexpSched0Accepted: false,
    generatedPCCPackexpSched0Kind: false,
    generatedPCCPackexpSched0Digest: false,
    generatedPCCPackexpSched0CoreMatchesExpected: false,
    generatedPCCPackexpSched0CoreB0: false,
    generatedPCCPackexpSched0CoreK0: false,
    generatedPCCPackexpSched0CoreR0: false,
    generatedPCCPackexpSched0CoreH0: false,
    generatedPCCPackexpSched0CoreO0: false,
    generatedPCCPackexpSched0CoreRel0: false,
    generatedPCCPackexpSched0ScaleFactorsPresent: false,
    generatedPCCPackexpSched0SelectorBoundsPresent: false,
    generatedPCCPackexpSched0SelectorBoundBH: false,
    generatedPCCPackexpSched0SelectorBoundBTheta: false,
    generatedPCCPackexpSched0PolynomialExponent: false,
    generatedPCCPackexpSched0PiBootDigestMatches: false,
    generatedPCCPackexpByteLang0: false,
    generatedPCCPackexpByteLang0Accepted: false,
    generatedPCCPackexpByteLang0Kind: false,
    generatedPCCPackexpByteLang0Digest: false,
    generatedPCCPackexpByteLang0TagCount: false,
    generatedPCCPackexpByteLang0TagsUnique: false,
    generatedPCCPackexpByteLang0RequiredTagsPresent: false,
    generatedPCCPackexpByteLang0SortCount: false,
    generatedPCCPackexpByteLang0RequiredSortsPresent: false,
    generatedPCCPackexpByteLang0ConstructorCount: false,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent: false,
    generatedPCCPackexpByteLang0RecordCount: false,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent: false,
    generatedPCCPackexpByteLang0PiBootDigestMatches: false,
    generatedPCCPackexpBootAudit0: false,
    generatedPCCPackexpBootAudit0Accepted: false,
    generatedPCCPackexpBootAudit0Checker: false,
    generatedPCCPackexpBootAudit0Digest: false,
    generatedPCCPackexpBootAudit0DigestMatchesNF: false,
    generatedPCCPackexpBootAudit0NFKind: false,
    generatedPCCPackexpBootAudit0SuiteId: false,
    generatedPCCPackexpBootAudit0CaseCount: false,
    generatedPCCPackexpBootAudit0PositiveCount: false,
    generatedPCCPackexpBootAudit0NegativeCount: false,
    generatedPCCPackexpBootAudit0CoversB0Accept: false,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject: false,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: false,
    generatedPCCPackexpPiBoot0: false,
    generatedPCCPackexpPiBoot0Accepted: false,
    generatedPCCPackexpPiBoot0Kind: false,
    generatedPCCPackexpPiBoot0Digest: false,
    generatedPCCPackexpPiBoot0Materialized: false,
    generatedPCCPackexpPiBoot0ExternalJson: false,
    generatedPCCPackexpPiBoot0RefCount: false,
    generatedPCCPackexpPiBoot0AllBootRefsPresent: false,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects: false,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0: false,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0: false,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0: false,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0: false,
    generatedPCCPackexpPiBoot0RefsIncludeSched0: false,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0: false,
    generatedPCCPackexpPiBoot0RefsIncludeB0: false,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0: false,
    generatedPCCPackexpConcreteKBundle0: false,
    generatedPCCPackexpConcreteKBundle0Accepted: false,
    generatedPCCPackexpConcreteKBundle0Checker: false,
    generatedPCCPackexpConcreteKBundle0Digest: false,
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest: false,
    generatedPCCPackexpConcreteKBundle0BootDigest: false,
    generatedPCCPackexpConcreteKBundle0KImplDigest: false,
    generatedPCCPackexpConcreteKBundle0K0Digest: false,
    generatedPCCPackexpConcreteKBundle0SigmaDigest: false,
    generatedPCCPackexpConcreteKBundle0ReflectionDigest: false,
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest: false,
    generatedPCCPackexpConcreteKBundle0KernelRuleCount: false,
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount: false,
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete: false,
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount: false,
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete: false,
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve: false,
    generatedPCCPackexpConcreteKBundle0ReflectionCount: false,
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete: false,
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve: false,
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs: false,
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols: false,
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0: false,
      finalCertificateUsesConcreteAcceptRun: false,
      statusUsesConcreteFinalCertificate: false,
      publicStatusCertificateDigestMatchesConcrete: false,
      publicStatusFinalVerdictDigestMatchesConcrete: false,
      publicStatusAcceptRunDigestMatchesConcrete: false,
      publicStatusPccPackDigestMatchesConcrete: false,
      gateDigest: null,
    });
  }

  const runner = typeof cfg.concreteFinalCertificatePublicStatusGateRunner === 'function'
    ? cfg.concreteFinalCertificatePublicStatusGateRunner
    : async () => {
        if (cfg.concreteFinalCertificatePublicStatusGateOutputDir !== null) {
          const written = await writeConcreteFinalCertificatePublicStatusFiles0(
            cfg.concreteFinalCertificatePublicStatusGateOutputDir,
          );

          return written.checked;
        }

        const envelope = await makeConcreteFinalCertificatePublicStatus0();

        return CheckConcreteFinalCertificatePublicStatus0(envelope, {
          finalCertificatePublicStatusConfig: {
            checkReleaseAuditRecord: false,
          },
        });
      };

  const record = await runner({
    outputDir: cfg.concreteFinalCertificatePublicStatusGateOutputDir,
    canonicalEnvelopeBytes: cfg.concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes,
  });

  if (record?.tag !== 'accept') {
    return validationReject0(['concreteFinalCertificatePublicStatusGate'], 'concrete final-certificate public-status gate rejected', {
      inner: compactReject0(record),
    });
  }

  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF'], 'concrete final-certificate public-status gate must emit an NF object', {
      actual: typeof nf,
    });
  }

  if (nf.kind !== 'ConcreteFinalCertificatePublicStatus0NF') {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', 'kind'], 'concrete final-certificate public-status gate emitted wrong NF kind', {
      actual: nf.kind,
    });
  }

  const requiredTrue = [
    'materializedPath',
    'publicConclusionEmitted',
    'concreteRows',
    'concreteLocalPackages',
    'concreteGlobalFirewalls',
    'concreteGlobalProofDAG',
    'concreteKBundle',
    'kBundleKernelRuleCoverageComplete',
    'kBundleSigmaProofRefsResolve',
    'kBundleReflectionProofRefsResolve',
    'concreteHardCheck',
    'hardCheckerCoverageComplete',
    'hardRowKeyCoverageComplete',
    'hardRoutePriorityComplete',
    'hardProofRefPolicyComplete',
    'hardHashDisciplineComplete',
    'hardNoMinCoverageComplete',
    'hardImportPolicyComplete',
    'hardReflectionPolicyComplete',
    'hardBoundsPolicyComplete',
    'hardDiagnosticsPolicyComplete',
    'concreteFinalIntegration',
    'finalIntegrationConcreteGlobalProofDAG',
    'finalIntegrationGPackFieldCoverageComplete',
    'finalIntegrationRowFamGCoverageComplete',
    'finalIntegrationUsesGPack',
    'rowFamGUsesGPack',
    'finalTheoremUsesFinalIntegration',
    'rowFamFinalUsesFinalTheorem',
    'finalMatchUsesGPack',
    'satDecisionUsesGPack',
    'concretePCCPack',
    'pccPackPublicConclusionOnlyAfterAcceptRun',
    'pccPackLinkedToKBundle',
    'pccPackLinkedToHardCheck',
    'pccPackLinkedToRows',
    'pccPackLinkedToLocalPackages',
    'pccPackLinkedToGlobalFirewalls',
    'pccPackLinkedToGlobalProofDAG',
    'pccPackLinkedToGPack',
    'pccPackLinkedToFinalIntegration',
    'pccPackLinkedToFinalTheorem',
    'checkPCCPackexpRecordPresent',
    'checkPCCPackexpRecordAccepted',
    'checkPCCPackexpRecordDigestMatchesNF',
    'checkPCCPackexpRecordConcretePCCPack',
    'checkPCCPackexpRecordPccPackDigestMatchesConcreteRun',
    'checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun',
    'checkPCCPackexpRecordPublicConclusionNotEmitted',
    'checkPCCPackexpRecordClaimBoundaryConditional',
    'generatedPCCPackexpEnvelopePresent',
    'generatedPCCPackexpGenCallGeneratePCCPack',
    'generatedPCCPackexpCoreOnly',
    'generatedPCCPackexpExcludesAcceptRun',
    'generatedPCCPackexpPackageMatchesConcreteRun',
    'generatedPCCPackexpCheckRecordMatchesConcreteRun',
    'generatedPCCPackexpCheckRecordAccepted',
    'generatedPCCPackexpCheckRecordDigestMatchesNF',
    'generatedPCCPackexpCheckRecordClaimBoundaryConditional',
    'generatedPCCPackexpLinkageGeneratedPackageDigestMatches',
    'generatedPCCPackexpLinkageCheckRecordDigestMatches',
    'checkGeneratedPCCPackexpRecordPresent',
    'checkGeneratedPCCPackexpRecordAccepted',
    'checkGeneratedPCCPackexpRecordDigestMatchesNF',
    'checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope',
    'checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope',
    'generatedPCCPackexpBoot0',
    'generatedPCCPackexpBoot0Accepted',
    'generatedPCCPackexpBoot0JsonMaterialized',
    'generatedPCCPackexpBoot0NoFixtureMarkers',
    'generatedPCCPackexpBoot0LinkedToPCCPack',
    'generatedPCCPackexpBoot0LinkedToCoreDigestMap',
    'generatedPCCPackexpBoot0DigestMatchesGeneratedPackage',
    'generatedPCCPackexpBoot0DigestMatchesCoreDigestMap',
    'generatedPCCPackexpBoot0B0Accepted',
    'generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent',
    'generatedPCCPackexpBoot0B0CoversIface',
    'generatedPCCPackexpBoot0B0CoversSched',
    'generatedPCCPackexpBoot0B0CoversNF',
    'generatedPCCPackexpBoot0B0CoversTruthEval',
    'generatedPCCPackexpBoot0B0CoversRel',
    'generatedPCCPackexpBoot0B0CoversCharge',
    'generatedPCCPackexpBoot0B0CoversObl',
    'generatedPCCPackexpBoot0B0CoversArith',
    'generatedPCCPackexpBoot0B0CoversMode',
    'generatedPCCPackexpBoot0B0CoversRoute',
    'generatedPCCPackexpBoot0B0CoversHash',
    'generatedPCCPackexpBoot0B0CoversImport',
    'generatedPCCPackexpKernelSeed0',
    'generatedPCCPackexpKernelSeed0Accepted',
    'generatedPCCPackexpKernelSeed0AllRequiredRulesPresent',
    'generatedPCCPackexpKernelSeed0HasEq',
    'generatedPCCPackexpKernelSeed0HasSubst',
    'generatedPCCPackexpKernelSeed0HasRecord',
    'generatedPCCPackexpKernelSeed0HasDAGInd',
    'generatedPCCPackexpKernelSeed0HasLedgerInd',
    'generatedPCCPackexpKernelSeed0HasOblTopoInd',
    'generatedPCCPackexpKernelSeed0HasTraceInd',
    'generatedPCCPackexpKernelSeed0HasFiniteExhaust',
    'generatedPCCPackexpKernelSeed0HasDPInd',
    'generatedPCCPackexpKernelSeed0HasHall',
    'generatedPCCPackexpKernelSeed0HasRankInd',
    'generatedPCCPackexpKernelSeed0HasMinCounterexample',
    'generatedPCCPackexpKernelSeed0HasIntArith',
    'generatedPCCPackexpKernelSeed0HasTransport',
    'generatedPCCPackexpKernelSeed0HasTruthVec',
    'generatedPCCPackexpKernelSeed0HasFiniteRel',
    'generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent',
    'generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
    'generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic',
    'generatedPCCPackexpKernelSeed0ProofRefsHashIndependent',
    'generatedPCCPackexpKernelSeed0PiBootDigestMatches',
    'generatedPCCPackexpCodec0',
    'generatedPCCPackexpCodec0Accepted',
    'generatedPCCPackexpCodec0Canonical',
    'generatedPCCPackexpCodec0NaturalEncodingCanonical',
    'generatedPCCPackexpCodec0IntegerEncodingCanonical',
    'generatedPCCPackexpCodec0StringEncodingCanonical',
    'generatedPCCPackexpCodec0TopLevelConsumesAllBytes',
    'generatedPCCPackexpCodec0NormalFormSerializationCanonical',
    'generatedPCCPackexpCodec0PiBootDigestMatches',
    'generatedPCCPackexpDigest0',
    'generatedPCCPackexpDigest0Accepted',
    'generatedPCCPackexpDigest0AlgSHA256',
    'generatedPCCPackexpDigest0BytesCanonicalJson',
    'generatedPCCPackexpDigest0EqualityNotObjectEquality',
    'generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup',
    'generatedPCCPackexpDigest0PiBootDigestMatches',
    'generatedPCCPackexpIfaceDict0',
    'generatedPCCPackexpIfaceDict0Accepted',
    'generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent',
    'generatedPCCPackexpIfaceDict0NoExecutableMinSymbols',
    'generatedPCCPackexpIfaceDict0PublicConstructorsPresent',
    'generatedPCCPackexpIfaceDict0CriticalKindsPresent',
    'generatedPCCPackexpIfaceDict0RouteTokensPresent',
    'generatedPCCPackexpIfaceDict0PiBootDigestMatches',
    'generatedPCCPackexpSched0',
    'generatedPCCPackexpSched0Accepted',
    'generatedPCCPackexpSched0CoreMatchesExpected',
    'generatedPCCPackexpSched0ScaleFactorsPresent',
    'generatedPCCPackexpSched0SelectorBoundsPresent',
    'generatedPCCPackexpSched0PiBootDigestMatches',
    'generatedPCCPackexpByteLang0',
    'generatedPCCPackexpByteLang0Accepted',
    'generatedPCCPackexpByteLang0TagsUnique',
    'generatedPCCPackexpByteLang0RequiredTagsPresent',
    'generatedPCCPackexpByteLang0RequiredSortsPresent',
    'generatedPCCPackexpByteLang0RequiredConstructorsPresent',
    'generatedPCCPackexpByteLang0RequiredRecordAritiesPresent',
    'generatedPCCPackexpByteLang0PiBootDigestMatches',
    'generatedPCCPackexpBootAudit0',
    'generatedPCCPackexpBootAudit0Accepted',
    'generatedPCCPackexpBootAudit0DigestMatchesNF',
    'generatedPCCPackexpBootAudit0CoversB0Accept',
    'generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject',
    'generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject',
    'generatedPCCPackexpPiBoot0',
    'generatedPCCPackexpPiBoot0Accepted',
    'generatedPCCPackexpPiBoot0Materialized',
    'generatedPCCPackexpPiBoot0ExternalJson',
    'generatedPCCPackexpPiBoot0AllBootRefsPresent',
    'generatedPCCPackexpPiBoot0RefsMatchBootObjects',
    'generatedPCCPackexpPiBoot0RefsIncludeByteLang0',
    'generatedPCCPackexpPiBoot0RefsIncludeCodec0',
    'generatedPCCPackexpPiBoot0RefsIncludeDigest0',
    'generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0',
    'generatedPCCPackexpPiBoot0RefsIncludeSched0',
    'generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0',
    'generatedPCCPackexpPiBoot0RefsIncludeB0',
    'generatedPCCPackexpPiBoot0RefsIncludeBootAudit0',
    'generatedPCCPackexpConcreteKBundle0',
    'generatedPCCPackexpConcreteKBundle0Accepted',
    'generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete',
    'generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete',
    'generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve',
    'generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete',
    'generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve',
    'generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs',
    'generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols',
    'generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0',
    'finalCertificateUsesConcreteAcceptRun',
    'statusUsesConcreteFinalCertificate',
    'publicStatusCertificateDigestMatchesConcrete',
    'publicStatusFinalVerdictDigestMatchesConcrete',
    'publicStatusAcceptRunDigestMatchesConcrete',
    'publicStatusPccPackDigestMatchesConcrete',
  ];

  for (const field of requiredTrue) {
    if (nf[field] !== true) {
      return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', field], `concrete final-certificate public-status gate must certify ${field}`, {
        actual: nf[field],
      });
    }
  }

  if (nf.syntheticRunAll !== false) {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', 'syntheticRunAll'], 'concrete final-certificate public-status gate must remain separate from synthetic RunAll0', {
      actual: nf.syntheticRunAll,
    });
  }

  if (nf.status !== 'accepted' || nf.verdict !== 'accept') {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', 'status'], 'concrete final-certificate public-status gate must be accepted', {
      status: nf.status,
      verdict: nf.verdict,
    });
  }

  if (!sameConcreteReleaseAuditPublicConclusion0(nf.publicConclusion)) {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', 'publicConclusion'], 'concrete final-certificate public conclusion mismatch', {
      actual: nf.publicConclusion,
    });
  }

  for (const field of [
    'certificateDigest',
    'finalVerdictDigest',
    'acceptRunDigest',
    'pccPackDigest',
  ]) {
    if (!isConcreteDigestLike0(nf[field])) {
      return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', field], `concrete final-certificate public-status gate must expose ${field}`, {
        actual: nf[field],
      });
    }
  }

  if (!isPlainObject(nf.canonicalByteRoots)) {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', 'canonicalByteRoots'], 'concrete final-certificate public-status gate must expose canonicalByteRoots', {
      actual: typeof nf.canonicalByteRoots,
    });
  }

  if (!isPlainObject(nf.acceptanceTranscript)) {
    return validationReject0(['concreteFinalCertificatePublicStatusGate', 'NF', 'acceptanceTranscript'], 'concrete final-certificate public-status gate must expose acceptanceTranscript', {
      actual: typeof nf.acceptanceTranscript,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConcreteFinalCertificatePublicStatusGate0NF',
    enabled: true,
    skipped: false,
    outputDir: cfg.concreteFinalCertificatePublicStatusGateOutputDir,
    canonicalEnvelopeBytes: cfg.concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes,
    status: nf.status,
    verdict: nf.verdict,
    materializedPath: nf.materializedPath,
    syntheticRunAll: nf.syntheticRunAll,
    publicConclusionEmitted: nf.publicConclusionEmitted,
    publicConclusion: nf.publicConclusion,
    certificateDigest: nf.certificateDigest,
    finalVerdictDigest: nf.finalVerdictDigest,
    acceptRunDigest: nf.acceptRunDigest,
    pccPackDigest: nf.pccPackDigest,
    canonicalByteRoots: nf.canonicalByteRoots,
    acceptanceTranscript: nf.acceptanceTranscript,
    releaseAuditAttached: nf.releaseAuditAttached,
    releaseAuditDigest: nf.releaseAuditDigest,
    releaseAuditStatus: nf.releaseAuditStatus,
    concreteRows: nf.concreteRows,
    concreteLocalPackages: nf.concreteLocalPackages,
    concreteGlobalFirewalls: nf.concreteGlobalFirewalls,
    concreteGlobalProofDAG: nf.concreteGlobalProofDAG,
    concreteKBundle: nf.concreteKBundle,
    kBundleKernelRuleCoverageComplete: nf.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: nf.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: nf.kBundleReflectionProofRefsResolve,
    concreteHardCheck: nf.concreteHardCheck,
    hardCheckerCoverageComplete: nf.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: nf.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: nf.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: nf.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: nf.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: nf.hardNoMinCoverageComplete,
    hardImportPolicyComplete: nf.hardImportPolicyComplete,
    hardReflectionPolicyComplete: nf.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: nf.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: nf.hardDiagnosticsPolicyComplete,
    concreteFinalIntegration: nf.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: nf.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: nf.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: nf.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: nf.finalIntegrationUsesGPack,
    rowFamGUsesGPack: nf.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: nf.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: nf.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: nf.finalMatchUsesGPack,
    satDecisionUsesGPack: nf.satDecisionUsesGPack,
    concretePCCPack: nf.concretePCCPack,
    concretePCCPackCoverageDigest: nf.concretePCCPackCoverageDigest,
    pccPackPublicConclusionOnlyAfterAcceptRun: nf.pccPackPublicConclusionOnlyAfterAcceptRun,
    pccPackLinkedToKBundle: nf.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: nf.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: nf.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: nf.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: nf.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: nf.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: nf.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: nf.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: nf.pccPackLinkedToFinalTheorem,
    checkPCCPackexpRecordPresent: nf.checkPCCPackexpRecordPresent,
    checkPCCPackexpRecordAccepted: nf.checkPCCPackexpRecordAccepted,
    checkPCCPackexpRecordChecker: nf.checkPCCPackexpRecordChecker,
    checkPCCPackexpRecordDigest: nf.checkPCCPackexpRecordDigest,
    checkPCCPackexpRecordDigestMatchesNF: nf.checkPCCPackexpRecordDigestMatchesNF,
    checkPCCPackexpRecordConcretePCCPack: nf.checkPCCPackexpRecordConcretePCCPack,
    checkPCCPackexpRecordPccPackDigest: nf.checkPCCPackexpRecordPccPackDigest,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: nf.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: nf.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun,
    checkPCCPackexpRecordPublicConclusionNotEmitted: nf.checkPCCPackexpRecordPublicConclusionNotEmitted,
    checkPCCPackexpRecordClaimBoundaryConditional: nf.checkPCCPackexpRecordClaimBoundaryConditional,
    generatedPCCPackexpEnvelopePresent: nf.generatedPCCPackexpEnvelopePresent,
    generatedPCCPackexpEnvelopeDigest: nf.generatedPCCPackexpEnvelopeDigest,
    generatedPCCPackexpGenCallGeneratePCCPack: nf.generatedPCCPackexpGenCallGeneratePCCPack,
    generatedPCCPackexpCoreOnly: nf.generatedPCCPackexpCoreOnly,
    generatedPCCPackexpExcludesAcceptRun: nf.generatedPCCPackexpExcludesAcceptRun,
    generatedPCCPackexpPackageMatchesConcreteRun: nf.generatedPCCPackexpPackageMatchesConcreteRun,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: nf.generatedPCCPackexpCheckRecordMatchesConcreteRun,
    generatedPCCPackexpCheckRecordAccepted: nf.generatedPCCPackexpCheckRecordAccepted,
    generatedPCCPackexpCheckRecordChecker: nf.generatedPCCPackexpCheckRecordChecker,
    generatedPCCPackexpCheckRecordDigest: nf.generatedPCCPackexpCheckRecordDigest,
    generatedPCCPackexpCheckRecordDigestMatchesNF: nf.generatedPCCPackexpCheckRecordDigestMatchesNF,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: nf.generatedPCCPackexpCheckRecordClaimBoundaryConditional,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: nf.generatedPCCPackexpLinkageGeneratedPackageDigestMatches,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: nf.generatedPCCPackexpLinkageCheckRecordDigestMatches,
    checkGeneratedPCCPackexpRecordPresent: nf.checkGeneratedPCCPackexpRecordPresent,
    checkGeneratedPCCPackexpRecordAccepted: nf.checkGeneratedPCCPackexpRecordAccepted,
    checkGeneratedPCCPackexpRecordChecker: nf.checkGeneratedPCCPackexpRecordChecker,
    checkGeneratedPCCPackexpRecordDigest: nf.checkGeneratedPCCPackexpRecordDigest,
    checkGeneratedPCCPackexpRecordDigestMatchesNF: nf.checkGeneratedPCCPackexpRecordDigestMatchesNF,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: nf.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: nf.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope,
    generatedPCCPackexpBoot0: nf.generatedPCCPackexpBoot0,
    generatedPCCPackexpBoot0Accepted: nf.generatedPCCPackexpBoot0Accepted,
    generatedPCCPackexpBoot0Kind: nf.generatedPCCPackexpBoot0Kind,
    generatedPCCPackexpBoot0Digest: nf.generatedPCCPackexpBoot0Digest,
    generatedPCCPackexpBoot0CheckDigest: nf.generatedPCCPackexpBoot0CheckDigest,
    generatedPCCPackexpBoot0CanonicalByteDigest: nf.generatedPCCPackexpBoot0CanonicalByteDigest,
    generatedPCCPackexpBoot0RowCount: nf.generatedPCCPackexpBoot0RowCount,
    generatedPCCPackexpBoot0KernelRuleCount: nf.generatedPCCPackexpBoot0KernelRuleCount,
    generatedPCCPackexpBoot0JsonMaterialized: nf.generatedPCCPackexpBoot0JsonMaterialized,
    generatedPCCPackexpBoot0NoFixtureMarkers: nf.generatedPCCPackexpBoot0NoFixtureMarkers,
    generatedPCCPackexpBoot0BootBatchDigest: nf.generatedPCCPackexpBoot0BootBatchDigest,
    generatedPCCPackexpBoot0BootAuditDigest: nf.generatedPCCPackexpBoot0BootAuditDigest,
    generatedPCCPackexpBoot0LinkedToPCCPack: nf.generatedPCCPackexpBoot0LinkedToPCCPack,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap: nf.generatedPCCPackexpBoot0LinkedToCoreDigestMap,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage: nf.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap: nf.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap,
    generatedPCCPackexpBoot0B0Accepted: nf.generatedPCCPackexpBoot0B0Accepted,
    generatedPCCPackexpBoot0B0Digest: nf.generatedPCCPackexpBoot0B0Digest,
    generatedPCCPackexpBoot0B0CoverageDigest: nf.generatedPCCPackexpBoot0B0CoverageDigest,
    generatedPCCPackexpBoot0B0FamilyCount: nf.generatedPCCPackexpBoot0B0FamilyCount,
    generatedPCCPackexpBoot0B0RequiredFamilyCount: nf.generatedPCCPackexpBoot0B0RequiredFamilyCount,
    generatedPCCPackexpBoot0B0Families: nf.generatedPCCPackexpBoot0B0Families,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent: nf.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent,
    generatedPCCPackexpBoot0B0CoversIface: nf.generatedPCCPackexpBoot0B0CoversIface,
    generatedPCCPackexpBoot0B0CoversSched: nf.generatedPCCPackexpBoot0B0CoversSched,
    generatedPCCPackexpBoot0B0CoversNF: nf.generatedPCCPackexpBoot0B0CoversNF,
    generatedPCCPackexpBoot0B0CoversTruthEval: nf.generatedPCCPackexpBoot0B0CoversTruthEval,
    generatedPCCPackexpBoot0B0CoversRel: nf.generatedPCCPackexpBoot0B0CoversRel,
    generatedPCCPackexpBoot0B0CoversCharge: nf.generatedPCCPackexpBoot0B0CoversCharge,
    generatedPCCPackexpBoot0B0CoversObl: nf.generatedPCCPackexpBoot0B0CoversObl,
    generatedPCCPackexpBoot0B0CoversArith: nf.generatedPCCPackexpBoot0B0CoversArith,
    generatedPCCPackexpBoot0B0CoversMode: nf.generatedPCCPackexpBoot0B0CoversMode,
    generatedPCCPackexpBoot0B0CoversRoute: nf.generatedPCCPackexpBoot0B0CoversRoute,
    generatedPCCPackexpBoot0B0CoversHash: nf.generatedPCCPackexpBoot0B0CoversHash,
    generatedPCCPackexpBoot0B0CoversImport: nf.generatedPCCPackexpBoot0B0CoversImport,
    generatedPCCPackexpKernelSeed0: nf.generatedPCCPackexpKernelSeed0,
    generatedPCCPackexpKernelSeed0Accepted: nf.generatedPCCPackexpKernelSeed0Accepted,
    generatedPCCPackexpKernelSeed0Kind: nf.generatedPCCPackexpKernelSeed0Kind,
    generatedPCCPackexpKernelSeed0Digest: nf.generatedPCCPackexpKernelSeed0Digest,
    generatedPCCPackexpKernelSeed0RuleCount: nf.generatedPCCPackexpKernelSeed0RuleCount,
    generatedPCCPackexpKernelSeed0RequiredRuleCount: nf.generatedPCCPackexpKernelSeed0RequiredRuleCount,
    generatedPCCPackexpKernelSeed0Rules: nf.generatedPCCPackexpKernelSeed0Rules,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent: nf.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent,
    generatedPCCPackexpKernelSeed0HasEq: nf.generatedPCCPackexpKernelSeed0HasEq,
    generatedPCCPackexpKernelSeed0HasSubst: nf.generatedPCCPackexpKernelSeed0HasSubst,
    generatedPCCPackexpKernelSeed0HasRecord: nf.generatedPCCPackexpKernelSeed0HasRecord,
    generatedPCCPackexpKernelSeed0HasDAGInd: nf.generatedPCCPackexpKernelSeed0HasDAGInd,
    generatedPCCPackexpKernelSeed0HasLedgerInd: nf.generatedPCCPackexpKernelSeed0HasLedgerInd,
    generatedPCCPackexpKernelSeed0HasOblTopoInd: nf.generatedPCCPackexpKernelSeed0HasOblTopoInd,
    generatedPCCPackexpKernelSeed0HasTraceInd: nf.generatedPCCPackexpKernelSeed0HasTraceInd,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust: nf.generatedPCCPackexpKernelSeed0HasFiniteExhaust,
    generatedPCCPackexpKernelSeed0HasDPInd: nf.generatedPCCPackexpKernelSeed0HasDPInd,
    generatedPCCPackexpKernelSeed0HasHall: nf.generatedPCCPackexpKernelSeed0HasHall,
    generatedPCCPackexpKernelSeed0HasRankInd: nf.generatedPCCPackexpKernelSeed0HasRankInd,
    generatedPCCPackexpKernelSeed0HasMinCounterexample: nf.generatedPCCPackexpKernelSeed0HasMinCounterexample,
    generatedPCCPackexpKernelSeed0HasIntArith: nf.generatedPCCPackexpKernelSeed0HasIntArith,
    generatedPCCPackexpKernelSeed0HasTransport: nf.generatedPCCPackexpKernelSeed0HasTransport,
    generatedPCCPackexpKernelSeed0HasTruthVec: nf.generatedPCCPackexpKernelSeed0HasTruthVec,
    generatedPCCPackexpKernelSeed0HasFiniteRel: nf.generatedPCCPackexpKernelSeed0HasFiniteRel,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount: nf.generatedPCCPackexpKernelSeed0ProofNodeKindCount,
    generatedPCCPackexpKernelSeed0ProofNodeKinds: nf.generatedPCCPackexpKernelSeed0ProofNodeKinds,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: nf.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: nf.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: nf.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent: nf.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches: nf.generatedPCCPackexpKernelSeed0PiBootDigestMatches,
    generatedPCCPackexpCodec0: nf.generatedPCCPackexpCodec0,
    generatedPCCPackexpCodec0Accepted: nf.generatedPCCPackexpCodec0Accepted,
    generatedPCCPackexpCodec0Kind: nf.generatedPCCPackexpCodec0Kind,
    generatedPCCPackexpCodec0Digest: nf.generatedPCCPackexpCodec0Digest,
    generatedPCCPackexpCodec0Canonical: nf.generatedPCCPackexpCodec0Canonical,
    generatedPCCPackexpCodec0NaturalEncoding: nf.generatedPCCPackexpCodec0NaturalEncoding,
    generatedPCCPackexpCodec0NaturalEncodingCanonical: nf.generatedPCCPackexpCodec0NaturalEncodingCanonical,
    generatedPCCPackexpCodec0IntegerEncoding: nf.generatedPCCPackexpCodec0IntegerEncoding,
    generatedPCCPackexpCodec0IntegerEncodingCanonical: nf.generatedPCCPackexpCodec0IntegerEncodingCanonical,
    generatedPCCPackexpCodec0StringEncoding: nf.generatedPCCPackexpCodec0StringEncoding,
    generatedPCCPackexpCodec0StringEncodingCanonical: nf.generatedPCCPackexpCodec0StringEncodingCanonical,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes: nf.generatedPCCPackexpCodec0TopLevelConsumesAllBytes,
    generatedPCCPackexpCodec0NormalFormSerialization: nf.generatedPCCPackexpCodec0NormalFormSerialization,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical: nf.generatedPCCPackexpCodec0NormalFormSerializationCanonical,
    generatedPCCPackexpCodec0PiBootDigestMatches: nf.generatedPCCPackexpCodec0PiBootDigestMatches,
    generatedPCCPackexpDigest0: nf.generatedPCCPackexpDigest0,
    generatedPCCPackexpDigest0Accepted: nf.generatedPCCPackexpDigest0Accepted,
    generatedPCCPackexpDigest0Kind: nf.generatedPCCPackexpDigest0Kind,
    generatedPCCPackexpDigest0Digest: nf.generatedPCCPackexpDigest0Digest,
    generatedPCCPackexpDigest0Alg: nf.generatedPCCPackexpDigest0Alg,
    generatedPCCPackexpDigest0AlgSHA256: nf.generatedPCCPackexpDigest0AlgSHA256,
    generatedPCCPackexpDigest0Bytes: nf.generatedPCCPackexpDigest0Bytes,
    generatedPCCPackexpDigest0BytesCanonicalJson: nf.generatedPCCPackexpDigest0BytesCanonicalJson,
    generatedPCCPackexpDigest0EqualityNotObjectEquality: nf.generatedPCCPackexpDigest0EqualityNotObjectEquality,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: nf.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup,
    generatedPCCPackexpDigest0PiBootDigestMatches: nf.generatedPCCPackexpDigest0PiBootDigestMatches,
    generatedPCCPackexpIfaceDict0: nf.generatedPCCPackexpIfaceDict0,
    generatedPCCPackexpIfaceDict0Accepted: nf.generatedPCCPackexpIfaceDict0Accepted,
    generatedPCCPackexpIfaceDict0Kind: nf.generatedPCCPackexpIfaceDict0Kind,
    generatedPCCPackexpIfaceDict0Digest: nf.generatedPCCPackexpIfaceDict0Digest,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount: nf.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: nf.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols: nf.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent: nf.generatedPCCPackexpIfaceDict0PublicConstructorsPresent,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent: nf.generatedPCCPackexpIfaceDict0CriticalKindsPresent,
    generatedPCCPackexpIfaceDict0RouteTokensPresent: nf.generatedPCCPackexpIfaceDict0RouteTokensPresent,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches: nf.generatedPCCPackexpIfaceDict0PiBootDigestMatches,
    generatedPCCPackexpSched0: nf.generatedPCCPackexpSched0,
    generatedPCCPackexpSched0Accepted: nf.generatedPCCPackexpSched0Accepted,
    generatedPCCPackexpSched0Kind: nf.generatedPCCPackexpSched0Kind,
    generatedPCCPackexpSched0Digest: nf.generatedPCCPackexpSched0Digest,
    generatedPCCPackexpSched0CoreMatchesExpected: nf.generatedPCCPackexpSched0CoreMatchesExpected,
    generatedPCCPackexpSched0CoreB0: nf.generatedPCCPackexpSched0CoreB0,
    generatedPCCPackexpSched0CoreK0: nf.generatedPCCPackexpSched0CoreK0,
    generatedPCCPackexpSched0CoreR0: nf.generatedPCCPackexpSched0CoreR0,
    generatedPCCPackexpSched0CoreH0: nf.generatedPCCPackexpSched0CoreH0,
    generatedPCCPackexpSched0CoreO0: nf.generatedPCCPackexpSched0CoreO0,
    generatedPCCPackexpSched0CoreRel0: nf.generatedPCCPackexpSched0CoreRel0,
    generatedPCCPackexpSched0ScaleFactorsPresent: nf.generatedPCCPackexpSched0ScaleFactorsPresent,
    generatedPCCPackexpSched0SelectorBoundsPresent: nf.generatedPCCPackexpSched0SelectorBoundsPresent,
    generatedPCCPackexpSched0SelectorBoundBH: nf.generatedPCCPackexpSched0SelectorBoundBH,
    generatedPCCPackexpSched0SelectorBoundBTheta: nf.generatedPCCPackexpSched0SelectorBoundBTheta,
    generatedPCCPackexpSched0PolynomialExponent: nf.generatedPCCPackexpSched0PolynomialExponent,
    generatedPCCPackexpSched0PiBootDigestMatches: nf.generatedPCCPackexpSched0PiBootDigestMatches,
    generatedPCCPackexpByteLang0: nf.generatedPCCPackexpByteLang0,
    generatedPCCPackexpByteLang0Accepted: nf.generatedPCCPackexpByteLang0Accepted,
    generatedPCCPackexpByteLang0Kind: nf.generatedPCCPackexpByteLang0Kind,
    generatedPCCPackexpByteLang0Digest: nf.generatedPCCPackexpByteLang0Digest,
    generatedPCCPackexpByteLang0TagCount: nf.generatedPCCPackexpByteLang0TagCount,
    generatedPCCPackexpByteLang0TagsUnique: nf.generatedPCCPackexpByteLang0TagsUnique,
    generatedPCCPackexpByteLang0RequiredTagsPresent: nf.generatedPCCPackexpByteLang0RequiredTagsPresent,
    generatedPCCPackexpByteLang0SortCount: nf.generatedPCCPackexpByteLang0SortCount,
    generatedPCCPackexpByteLang0RequiredSortsPresent: nf.generatedPCCPackexpByteLang0RequiredSortsPresent,
    generatedPCCPackexpByteLang0ConstructorCount: nf.generatedPCCPackexpByteLang0ConstructorCount,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent: nf.generatedPCCPackexpByteLang0RequiredConstructorsPresent,
    generatedPCCPackexpByteLang0RecordCount: nf.generatedPCCPackexpByteLang0RecordCount,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent: nf.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent,
    generatedPCCPackexpByteLang0PiBootDigestMatches: nf.generatedPCCPackexpByteLang0PiBootDigestMatches,
    generatedPCCPackexpBootAudit0: nf.generatedPCCPackexpBootAudit0,
    generatedPCCPackexpBootAudit0Accepted: nf.generatedPCCPackexpBootAudit0Accepted,
    generatedPCCPackexpBootAudit0Checker: nf.generatedPCCPackexpBootAudit0Checker,
    generatedPCCPackexpBootAudit0Digest: nf.generatedPCCPackexpBootAudit0Digest,
    generatedPCCPackexpBootAudit0DigestMatchesNF: nf.generatedPCCPackexpBootAudit0DigestMatchesNF,
    generatedPCCPackexpBootAudit0NFKind: nf.generatedPCCPackexpBootAudit0NFKind,
    generatedPCCPackexpBootAudit0SuiteId: nf.generatedPCCPackexpBootAudit0SuiteId,
    generatedPCCPackexpBootAudit0CaseCount: nf.generatedPCCPackexpBootAudit0CaseCount,
    generatedPCCPackexpBootAudit0PositiveCount: nf.generatedPCCPackexpBootAudit0PositiveCount,
    generatedPCCPackexpBootAudit0NegativeCount: nf.generatedPCCPackexpBootAudit0NegativeCount,
    generatedPCCPackexpBootAudit0CoversB0Accept: nf.generatedPCCPackexpBootAudit0CoversB0Accept,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject: nf.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: nf.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject,
    generatedPCCPackexpPiBoot0: nf.generatedPCCPackexpPiBoot0,
    generatedPCCPackexpPiBoot0Accepted: nf.generatedPCCPackexpPiBoot0Accepted,
    generatedPCCPackexpPiBoot0Kind: nf.generatedPCCPackexpPiBoot0Kind,
    generatedPCCPackexpPiBoot0Digest: nf.generatedPCCPackexpPiBoot0Digest,
    generatedPCCPackexpPiBoot0Materialized: nf.generatedPCCPackexpPiBoot0Materialized,
    generatedPCCPackexpPiBoot0ExternalJson: nf.generatedPCCPackexpPiBoot0ExternalJson,
    generatedPCCPackexpPiBoot0RefCount: nf.generatedPCCPackexpPiBoot0RefCount,
    generatedPCCPackexpPiBoot0AllBootRefsPresent: nf.generatedPCCPackexpPiBoot0AllBootRefsPresent,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects: nf.generatedPCCPackexpPiBoot0RefsMatchBootObjects,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0: nf.generatedPCCPackexpPiBoot0RefsIncludeByteLang0,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0: nf.generatedPCCPackexpPiBoot0RefsIncludeCodec0,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0: nf.generatedPCCPackexpPiBoot0RefsIncludeDigest0,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0: nf.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0,
    generatedPCCPackexpPiBoot0RefsIncludeSched0: nf.generatedPCCPackexpPiBoot0RefsIncludeSched0,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0: nf.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0,
    generatedPCCPackexpPiBoot0RefsIncludeB0: nf.generatedPCCPackexpPiBoot0RefsIncludeB0,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0: nf.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0,
    generatedPCCPackexpConcreteKBundle0: nf.generatedPCCPackexpConcreteKBundle0,
    generatedPCCPackexpConcreteKBundle0Accepted: nf.generatedPCCPackexpConcreteKBundle0Accepted,
    generatedPCCPackexpConcreteKBundle0Checker: nf.generatedPCCPackexpConcreteKBundle0Checker,
    generatedPCCPackexpConcreteKBundle0Digest: nf.generatedPCCPackexpConcreteKBundle0Digest,
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest: nf.generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest,
    generatedPCCPackexpConcreteKBundle0BootDigest: nf.generatedPCCPackexpConcreteKBundle0BootDigest,
    generatedPCCPackexpConcreteKBundle0KImplDigest: nf.generatedPCCPackexpConcreteKBundle0KImplDigest,
    generatedPCCPackexpConcreteKBundle0K0Digest: nf.generatedPCCPackexpConcreteKBundle0K0Digest,
    generatedPCCPackexpConcreteKBundle0SigmaDigest: nf.generatedPCCPackexpConcreteKBundle0SigmaDigest,
    generatedPCCPackexpConcreteKBundle0ReflectionDigest: nf.generatedPCCPackexpConcreteKBundle0ReflectionDigest,
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest: nf.generatedPCCPackexpConcreteKBundle0ProofInventoryDigest,
    generatedPCCPackexpConcreteKBundle0KernelRuleCount: nf.generatedPCCPackexpConcreteKBundle0KernelRuleCount,
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount: nf.generatedPCCPackexpConcreteKBundle0ConformanceNodeCount,
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete: nf.generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete,
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount: nf.generatedPCCPackexpConcreteKBundle0SigmaTheoremCount,
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete: nf.generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete,
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve: nf.generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve,
    generatedPCCPackexpConcreteKBundle0ReflectionCount: nf.generatedPCCPackexpConcreteKBundle0ReflectionCount,
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete: nf.generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete,
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve: nf.generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve,
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs: nf.generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs,
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols: nf.generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols,
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0: nf.generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0,
    finalCertificateUsesConcreteAcceptRun: nf.finalCertificateUsesConcreteAcceptRun,
    statusUsesConcreteFinalCertificate: nf.statusUsesConcreteFinalCertificate,
    publicStatusCertificateDigestMatchesConcrete: nf.publicStatusCertificateDigestMatchesConcrete,
    publicStatusFinalVerdictDigestMatchesConcrete: nf.publicStatusFinalVerdictDigestMatchesConcrete,
    publicStatusAcceptRunDigestMatchesConcrete: nf.publicStatusAcceptRunDigestMatchesConcrete,
    publicStatusPccPackDigestMatchesConcrete: nf.publicStatusPccPackDigestMatchesConcrete,
    gateDigest: record.Digest ?? record.digest,
  });
}

function summarizeConcreteFinalCertificatePublicStatusGateNF0(nf, cfg) {
  const summary = {
    kind: 'ReleaseAuditConcreteFinalCertificatePublicStatusGateSummary0',
    enabled: cfg.runConcreteFinalCertificatePublicStatusGate,
    skipped: cfg.runConcreteFinalCertificatePublicStatusGate !== true,
    outputDir: cfg.concreteFinalCertificatePublicStatusGateOutputDir,
    canonicalEnvelopeBytes: cfg.concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes,
    status: null,
    verdict: null,
    materializedPath: false,
    syntheticRunAll: null,
    publicConclusionEmitted: false,
    publicConclusion: null,
    certificateDigest: null,
    finalVerdictDigest: null,
    acceptRunDigest: null,
    pccPackDigest: null,
    canonicalByteRoots: null,
    acceptanceTranscript: null,
    releaseAuditAttached: false,
    releaseAuditDigest: null,
    releaseAuditStatus: cfg.runConcreteFinalCertificatePublicStatusGate === true ? 'not-attached' : 'skipped',
    concreteRows: false,
    concreteLocalPackages: false,
    concreteGlobalFirewalls: false,
    concreteGlobalProofDAG: false,
    finalCertificateUsesConcreteAcceptRun: false,
    statusUsesConcreteFinalCertificate: false,
    publicStatusCertificateDigestMatchesConcrete: false,
    publicStatusFinalVerdictDigestMatchesConcrete: false,
    publicStatusAcceptRunDigestMatchesConcrete: false,
    publicStatusPccPackDigestMatchesConcrete: false,
    gateDigest: null,
  };

  if (!isPlainObject(nf)) {
    return summary;
  }

  return {
    ...summary,
    skipped: nf.skipped === true,
    status: nf.status ?? null,
    verdict: nf.verdict ?? null,
    materializedPath: nf.materializedPath ?? false,
    syntheticRunAll: nf.syntheticRunAll ?? null,
    publicConclusionEmitted: nf.publicConclusionEmitted ?? false,
    publicConclusion: nf.publicConclusion ?? null,
    certificateDigest: nf.certificateDigest ?? null,
    finalVerdictDigest: nf.finalVerdictDigest ?? null,
    acceptRunDigest: nf.acceptRunDigest ?? null,
    pccPackDigest: nf.pccPackDigest ?? null,
    canonicalByteRoots: nf.canonicalByteRoots ?? null,
    acceptanceTranscript: nf.acceptanceTranscript ?? null,
    releaseAuditAttached: nf.releaseAuditAttached ?? false,
    releaseAuditDigest: nf.releaseAuditDigest ?? null,
    releaseAuditStatus: nf.releaseAuditStatus ?? null,
    concreteRows: nf.concreteRows ?? false,
    concreteLocalPackages: nf.concreteLocalPackages ?? false,
    concreteGlobalFirewalls: nf.concreteGlobalFirewalls ?? false,
    concreteGlobalProofDAG: nf.concreteGlobalProofDAG ?? false,
    concreteKBundle: nf.concreteKBundle ?? false,
    kBundleKernelRuleCoverageComplete: nf.kBundleKernelRuleCoverageComplete ?? false,
    kBundleSigmaProofRefsResolve: nf.kBundleSigmaProofRefsResolve ?? false,
    kBundleReflectionProofRefsResolve: nf.kBundleReflectionProofRefsResolve ?? false,
    concreteHardCheck: nf.concreteHardCheck ?? false,
    hardCheckerCoverageComplete: nf.hardCheckerCoverageComplete ?? false,
    hardRowKeyCoverageComplete: nf.hardRowKeyCoverageComplete ?? false,
    hardRoutePriorityComplete: nf.hardRoutePriorityComplete ?? false,
    hardProofRefPolicyComplete: nf.hardProofRefPolicyComplete ?? false,
    hardHashDisciplineComplete: nf.hardHashDisciplineComplete ?? false,
    hardNoMinCoverageComplete: nf.hardNoMinCoverageComplete ?? false,
    hardImportPolicyComplete: nf.hardImportPolicyComplete ?? false,
    hardReflectionPolicyComplete: nf.hardReflectionPolicyComplete ?? false,
    hardBoundsPolicyComplete: nf.hardBoundsPolicyComplete ?? false,
    hardDiagnosticsPolicyComplete: nf.hardDiagnosticsPolicyComplete ?? false,
    concreteFinalIntegration: nf.concreteFinalIntegration ?? false,
    finalIntegrationConcreteGlobalProofDAG: nf.finalIntegrationConcreteGlobalProofDAG ?? false,
    finalIntegrationGPackFieldCoverageComplete: nf.finalIntegrationGPackFieldCoverageComplete ?? false,
    finalIntegrationRowFamGCoverageComplete: nf.finalIntegrationRowFamGCoverageComplete ?? false,
    finalIntegrationUsesGPack: nf.finalIntegrationUsesGPack ?? false,
    rowFamGUsesGPack: nf.rowFamGUsesGPack ?? false,
    finalTheoremUsesFinalIntegration: nf.finalTheoremUsesFinalIntegration ?? false,
    rowFamFinalUsesFinalTheorem: nf.rowFamFinalUsesFinalTheorem ?? false,
    finalMatchUsesGPack: nf.finalMatchUsesGPack ?? false,
    satDecisionUsesGPack: nf.satDecisionUsesGPack ?? false,
    concretePCCPack: nf.concretePCCPack ?? false,
    concretePCCPackCoverageDigest: nf.concretePCCPackCoverageDigest ?? false,
    pccPackPublicConclusionOnlyAfterAcceptRun: nf.pccPackPublicConclusionOnlyAfterAcceptRun ?? false,
    pccPackLinkedToKBundle: nf.pccPackLinkedToKBundle ?? false,
    pccPackLinkedToHardCheck: nf.pccPackLinkedToHardCheck ?? false,
    pccPackLinkedToRows: nf.pccPackLinkedToRows ?? false,
    pccPackLinkedToLocalPackages: nf.pccPackLinkedToLocalPackages ?? false,
    pccPackLinkedToGlobalFirewalls: nf.pccPackLinkedToGlobalFirewalls ?? false,
    pccPackLinkedToGlobalProofDAG: nf.pccPackLinkedToGlobalProofDAG ?? false,
    pccPackLinkedToGPack: nf.pccPackLinkedToGPack ?? false,
    pccPackLinkedToFinalIntegration: nf.pccPackLinkedToFinalIntegration ?? false,
    pccPackLinkedToFinalTheorem: nf.pccPackLinkedToFinalTheorem ?? false,
    checkPCCPackexpRecordPresent: nf.checkPCCPackexpRecordPresent ?? false,
    checkPCCPackexpRecordAccepted: nf.checkPCCPackexpRecordAccepted ?? false,
    checkPCCPackexpRecordChecker: nf.checkPCCPackexpRecordChecker ?? false,
    checkPCCPackexpRecordDigest: nf.checkPCCPackexpRecordDigest ?? false,
    checkPCCPackexpRecordDigestMatchesNF: nf.checkPCCPackexpRecordDigestMatchesNF ?? false,
    checkPCCPackexpRecordConcretePCCPack: nf.checkPCCPackexpRecordConcretePCCPack ?? false,
    checkPCCPackexpRecordPccPackDigest: nf.checkPCCPackexpRecordPccPackDigest ?? false,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: nf.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun ?? false,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: nf.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun ?? false,
    checkPCCPackexpRecordPublicConclusionNotEmitted: nf.checkPCCPackexpRecordPublicConclusionNotEmitted ?? false,
    checkPCCPackexpRecordClaimBoundaryConditional: nf.checkPCCPackexpRecordClaimBoundaryConditional ?? false,
    generatedPCCPackexpEnvelopePresent: nf.generatedPCCPackexpEnvelopePresent ?? false,
    generatedPCCPackexpEnvelopeDigest: nf.generatedPCCPackexpEnvelopeDigest ?? false,
    generatedPCCPackexpGenCallGeneratePCCPack: nf.generatedPCCPackexpGenCallGeneratePCCPack ?? false,
    generatedPCCPackexpCoreOnly: nf.generatedPCCPackexpCoreOnly ?? false,
    generatedPCCPackexpExcludesAcceptRun: nf.generatedPCCPackexpExcludesAcceptRun ?? false,
    generatedPCCPackexpPackageMatchesConcreteRun: nf.generatedPCCPackexpPackageMatchesConcreteRun ?? false,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: nf.generatedPCCPackexpCheckRecordMatchesConcreteRun ?? false,
    generatedPCCPackexpCheckRecordAccepted: nf.generatedPCCPackexpCheckRecordAccepted ?? false,
    generatedPCCPackexpCheckRecordChecker: nf.generatedPCCPackexpCheckRecordChecker ?? false,
    generatedPCCPackexpCheckRecordDigest: nf.generatedPCCPackexpCheckRecordDigest ?? false,
    generatedPCCPackexpCheckRecordDigestMatchesNF: nf.generatedPCCPackexpCheckRecordDigestMatchesNF ?? false,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: nf.generatedPCCPackexpCheckRecordClaimBoundaryConditional ?? false,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: nf.generatedPCCPackexpLinkageGeneratedPackageDigestMatches ?? false,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: nf.generatedPCCPackexpLinkageCheckRecordDigestMatches ?? false,
    checkGeneratedPCCPackexpRecordPresent: nf.checkGeneratedPCCPackexpRecordPresent ?? false,
    checkGeneratedPCCPackexpRecordAccepted: nf.checkGeneratedPCCPackexpRecordAccepted ?? false,
    checkGeneratedPCCPackexpRecordChecker: nf.checkGeneratedPCCPackexpRecordChecker ?? false,
    checkGeneratedPCCPackexpRecordDigest: nf.checkGeneratedPCCPackexpRecordDigest ?? false,
    checkGeneratedPCCPackexpRecordDigestMatchesNF: nf.checkGeneratedPCCPackexpRecordDigestMatchesNF ?? false,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: nf.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope ?? false,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: nf.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope ?? false,
    generatedPCCPackexpBoot0: nf.generatedPCCPackexpBoot0 ?? false,
    generatedPCCPackexpBoot0Accepted: nf.generatedPCCPackexpBoot0Accepted ?? false,
    generatedPCCPackexpBoot0Kind: nf.generatedPCCPackexpBoot0Kind ?? false,
    generatedPCCPackexpBoot0Digest: nf.generatedPCCPackexpBoot0Digest ?? false,
    generatedPCCPackexpBoot0CheckDigest: nf.generatedPCCPackexpBoot0CheckDigest ?? false,
    generatedPCCPackexpBoot0CanonicalByteDigest: nf.generatedPCCPackexpBoot0CanonicalByteDigest ?? false,
    generatedPCCPackexpBoot0RowCount: nf.generatedPCCPackexpBoot0RowCount ?? false,
    generatedPCCPackexpBoot0KernelRuleCount: nf.generatedPCCPackexpBoot0KernelRuleCount ?? false,
    generatedPCCPackexpBoot0JsonMaterialized: nf.generatedPCCPackexpBoot0JsonMaterialized ?? false,
    generatedPCCPackexpBoot0NoFixtureMarkers: nf.generatedPCCPackexpBoot0NoFixtureMarkers ?? false,
    generatedPCCPackexpBoot0BootBatchDigest: nf.generatedPCCPackexpBoot0BootBatchDigest ?? false,
    generatedPCCPackexpBoot0BootAuditDigest: nf.generatedPCCPackexpBoot0BootAuditDigest ?? false,
    generatedPCCPackexpBoot0LinkedToPCCPack: nf.generatedPCCPackexpBoot0LinkedToPCCPack ?? false,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap: nf.generatedPCCPackexpBoot0LinkedToCoreDigestMap ?? false,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage: nf.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage ?? false,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap: nf.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap ?? false,
    generatedPCCPackexpBoot0B0Accepted: nf.generatedPCCPackexpBoot0B0Accepted ?? false,
    generatedPCCPackexpBoot0B0Digest: nf.generatedPCCPackexpBoot0B0Digest ?? false,
    generatedPCCPackexpBoot0B0CoverageDigest: nf.generatedPCCPackexpBoot0B0CoverageDigest ?? false,
    generatedPCCPackexpBoot0B0FamilyCount: nf.generatedPCCPackexpBoot0B0FamilyCount ?? false,
    generatedPCCPackexpBoot0B0RequiredFamilyCount: nf.generatedPCCPackexpBoot0B0RequiredFamilyCount ?? false,
    generatedPCCPackexpBoot0B0Families: nf.generatedPCCPackexpBoot0B0Families ?? false,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent: nf.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent ?? false,
    generatedPCCPackexpBoot0B0CoversIface: nf.generatedPCCPackexpBoot0B0CoversIface ?? false,
    generatedPCCPackexpBoot0B0CoversSched: nf.generatedPCCPackexpBoot0B0CoversSched ?? false,
    generatedPCCPackexpBoot0B0CoversNF: nf.generatedPCCPackexpBoot0B0CoversNF ?? false,
    generatedPCCPackexpBoot0B0CoversTruthEval: nf.generatedPCCPackexpBoot0B0CoversTruthEval ?? false,
    generatedPCCPackexpBoot0B0CoversRel: nf.generatedPCCPackexpBoot0B0CoversRel ?? false,
    generatedPCCPackexpBoot0B0CoversCharge: nf.generatedPCCPackexpBoot0B0CoversCharge ?? false,
    generatedPCCPackexpBoot0B0CoversObl: nf.generatedPCCPackexpBoot0B0CoversObl ?? false,
    generatedPCCPackexpBoot0B0CoversArith: nf.generatedPCCPackexpBoot0B0CoversArith ?? false,
    generatedPCCPackexpBoot0B0CoversMode: nf.generatedPCCPackexpBoot0B0CoversMode ?? false,
    generatedPCCPackexpBoot0B0CoversRoute: nf.generatedPCCPackexpBoot0B0CoversRoute ?? false,
    generatedPCCPackexpBoot0B0CoversHash: nf.generatedPCCPackexpBoot0B0CoversHash ?? false,
    generatedPCCPackexpBoot0B0CoversImport: nf.generatedPCCPackexpBoot0B0CoversImport ?? false,
    generatedPCCPackexpKernelSeed0: nf.generatedPCCPackexpKernelSeed0 ?? false,
    generatedPCCPackexpKernelSeed0Accepted: nf.generatedPCCPackexpKernelSeed0Accepted ?? false,
    generatedPCCPackexpKernelSeed0Kind: nf.generatedPCCPackexpKernelSeed0Kind ?? false,
    generatedPCCPackexpKernelSeed0Digest: nf.generatedPCCPackexpKernelSeed0Digest ?? false,
    generatedPCCPackexpKernelSeed0RuleCount: nf.generatedPCCPackexpKernelSeed0RuleCount ?? false,
    generatedPCCPackexpKernelSeed0RequiredRuleCount: nf.generatedPCCPackexpKernelSeed0RequiredRuleCount ?? false,
    generatedPCCPackexpKernelSeed0Rules: nf.generatedPCCPackexpKernelSeed0Rules ?? false,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent: nf.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent ?? false,
    generatedPCCPackexpKernelSeed0HasEq: nf.generatedPCCPackexpKernelSeed0HasEq ?? false,
    generatedPCCPackexpKernelSeed0HasSubst: nf.generatedPCCPackexpKernelSeed0HasSubst ?? false,
    generatedPCCPackexpKernelSeed0HasRecord: nf.generatedPCCPackexpKernelSeed0HasRecord ?? false,
    generatedPCCPackexpKernelSeed0HasDAGInd: nf.generatedPCCPackexpKernelSeed0HasDAGInd ?? false,
    generatedPCCPackexpKernelSeed0HasLedgerInd: nf.generatedPCCPackexpKernelSeed0HasLedgerInd ?? false,
    generatedPCCPackexpKernelSeed0HasOblTopoInd: nf.generatedPCCPackexpKernelSeed0HasOblTopoInd ?? false,
    generatedPCCPackexpKernelSeed0HasTraceInd: nf.generatedPCCPackexpKernelSeed0HasTraceInd ?? false,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust: nf.generatedPCCPackexpKernelSeed0HasFiniteExhaust ?? false,
    generatedPCCPackexpKernelSeed0HasDPInd: nf.generatedPCCPackexpKernelSeed0HasDPInd ?? false,
    generatedPCCPackexpKernelSeed0HasHall: nf.generatedPCCPackexpKernelSeed0HasHall ?? false,
    generatedPCCPackexpKernelSeed0HasRankInd: nf.generatedPCCPackexpKernelSeed0HasRankInd ?? false,
    generatedPCCPackexpKernelSeed0HasMinCounterexample: nf.generatedPCCPackexpKernelSeed0HasMinCounterexample ?? false,
    generatedPCCPackexpKernelSeed0HasIntArith: nf.generatedPCCPackexpKernelSeed0HasIntArith ?? false,
    generatedPCCPackexpKernelSeed0HasTransport: nf.generatedPCCPackexpKernelSeed0HasTransport ?? false,
    generatedPCCPackexpKernelSeed0HasTruthVec: nf.generatedPCCPackexpKernelSeed0HasTruthVec ?? false,
    generatedPCCPackexpKernelSeed0HasFiniteRel: nf.generatedPCCPackexpKernelSeed0HasFiniteRel ?? false,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount: nf.generatedPCCPackexpKernelSeed0ProofNodeKindCount ?? false,
    generatedPCCPackexpKernelSeed0ProofNodeKinds: nf.generatedPCCPackexpKernelSeed0ProofNodeKinds ?? false,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: nf.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent ?? false,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: nf.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque ?? false,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: nf.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic ?? false,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent: nf.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent ?? false,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches: nf.generatedPCCPackexpKernelSeed0PiBootDigestMatches ?? false,
    generatedPCCPackexpCodec0: nf.generatedPCCPackexpCodec0 ?? false,
    generatedPCCPackexpCodec0Accepted: nf.generatedPCCPackexpCodec0Accepted ?? false,
    generatedPCCPackexpCodec0Kind: nf.generatedPCCPackexpCodec0Kind ?? false,
    generatedPCCPackexpCodec0Digest: nf.generatedPCCPackexpCodec0Digest ?? false,
    generatedPCCPackexpCodec0Canonical: nf.generatedPCCPackexpCodec0Canonical ?? false,
    generatedPCCPackexpCodec0NaturalEncoding: nf.generatedPCCPackexpCodec0NaturalEncoding ?? false,
    generatedPCCPackexpCodec0NaturalEncodingCanonical: nf.generatedPCCPackexpCodec0NaturalEncodingCanonical ?? false,
    generatedPCCPackexpCodec0IntegerEncoding: nf.generatedPCCPackexpCodec0IntegerEncoding ?? false,
    generatedPCCPackexpCodec0IntegerEncodingCanonical: nf.generatedPCCPackexpCodec0IntegerEncodingCanonical ?? false,
    generatedPCCPackexpCodec0StringEncoding: nf.generatedPCCPackexpCodec0StringEncoding ?? false,
    generatedPCCPackexpCodec0StringEncodingCanonical: nf.generatedPCCPackexpCodec0StringEncodingCanonical ?? false,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes: nf.generatedPCCPackexpCodec0TopLevelConsumesAllBytes ?? false,
    generatedPCCPackexpCodec0NormalFormSerialization: nf.generatedPCCPackexpCodec0NormalFormSerialization ?? false,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical: nf.generatedPCCPackexpCodec0NormalFormSerializationCanonical ?? false,
    generatedPCCPackexpCodec0PiBootDigestMatches: nf.generatedPCCPackexpCodec0PiBootDigestMatches ?? false,
    generatedPCCPackexpDigest0: nf.generatedPCCPackexpDigest0 ?? false,
    generatedPCCPackexpDigest0Accepted: nf.generatedPCCPackexpDigest0Accepted ?? false,
    generatedPCCPackexpDigest0Kind: nf.generatedPCCPackexpDigest0Kind ?? false,
    generatedPCCPackexpDigest0Digest: nf.generatedPCCPackexpDigest0Digest ?? false,
    generatedPCCPackexpDigest0Alg: nf.generatedPCCPackexpDigest0Alg ?? false,
    generatedPCCPackexpDigest0AlgSHA256: nf.generatedPCCPackexpDigest0AlgSHA256 ?? false,
    generatedPCCPackexpDigest0Bytes: nf.generatedPCCPackexpDigest0Bytes ?? false,
    generatedPCCPackexpDigest0BytesCanonicalJson: nf.generatedPCCPackexpDigest0BytesCanonicalJson ?? false,
    generatedPCCPackexpDigest0EqualityNotObjectEquality: nf.generatedPCCPackexpDigest0EqualityNotObjectEquality ?? false,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: nf.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup ?? false,
    generatedPCCPackexpDigest0PiBootDigestMatches: nf.generatedPCCPackexpDigest0PiBootDigestMatches ?? false,
    generatedPCCPackexpIfaceDict0: nf.generatedPCCPackexpIfaceDict0 ?? false,
    generatedPCCPackexpIfaceDict0Accepted: nf.generatedPCCPackexpIfaceDict0Accepted ?? false,
    generatedPCCPackexpIfaceDict0Kind: nf.generatedPCCPackexpIfaceDict0Kind ?? false,
    generatedPCCPackexpIfaceDict0Digest: nf.generatedPCCPackexpIfaceDict0Digest ?? false,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount: nf.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount ?? false,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: nf.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent ?? false,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols: nf.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols ?? false,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent: nf.generatedPCCPackexpIfaceDict0PublicConstructorsPresent ?? false,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent: nf.generatedPCCPackexpIfaceDict0CriticalKindsPresent ?? false,
    generatedPCCPackexpIfaceDict0RouteTokensPresent: nf.generatedPCCPackexpIfaceDict0RouteTokensPresent ?? false,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches: nf.generatedPCCPackexpIfaceDict0PiBootDigestMatches ?? false,
    generatedPCCPackexpSched0: nf.generatedPCCPackexpSched0 ?? false,
    generatedPCCPackexpSched0Accepted: nf.generatedPCCPackexpSched0Accepted ?? false,
    generatedPCCPackexpSched0Kind: nf.generatedPCCPackexpSched0Kind ?? false,
    generatedPCCPackexpSched0Digest: nf.generatedPCCPackexpSched0Digest ?? false,
    generatedPCCPackexpSched0CoreMatchesExpected: nf.generatedPCCPackexpSched0CoreMatchesExpected ?? false,
    generatedPCCPackexpSched0CoreB0: nf.generatedPCCPackexpSched0CoreB0 ?? false,
    generatedPCCPackexpSched0CoreK0: nf.generatedPCCPackexpSched0CoreK0 ?? false,
    generatedPCCPackexpSched0CoreR0: nf.generatedPCCPackexpSched0CoreR0 ?? false,
    generatedPCCPackexpSched0CoreH0: nf.generatedPCCPackexpSched0CoreH0 ?? false,
    generatedPCCPackexpSched0CoreO0: nf.generatedPCCPackexpSched0CoreO0 ?? false,
    generatedPCCPackexpSched0CoreRel0: nf.generatedPCCPackexpSched0CoreRel0 ?? false,
    generatedPCCPackexpSched0ScaleFactorsPresent: nf.generatedPCCPackexpSched0ScaleFactorsPresent ?? false,
    generatedPCCPackexpSched0SelectorBoundsPresent: nf.generatedPCCPackexpSched0SelectorBoundsPresent ?? false,
    generatedPCCPackexpSched0SelectorBoundBH: nf.generatedPCCPackexpSched0SelectorBoundBH ?? false,
    generatedPCCPackexpSched0SelectorBoundBTheta: nf.generatedPCCPackexpSched0SelectorBoundBTheta ?? false,
    generatedPCCPackexpSched0PolynomialExponent: nf.generatedPCCPackexpSched0PolynomialExponent ?? false,
    generatedPCCPackexpSched0PiBootDigestMatches: nf.generatedPCCPackexpSched0PiBootDigestMatches ?? false,
    generatedPCCPackexpByteLang0: nf.generatedPCCPackexpByteLang0 ?? false,
    generatedPCCPackexpByteLang0Accepted: nf.generatedPCCPackexpByteLang0Accepted ?? false,
    generatedPCCPackexpByteLang0Kind: nf.generatedPCCPackexpByteLang0Kind ?? false,
    generatedPCCPackexpByteLang0Digest: nf.generatedPCCPackexpByteLang0Digest ?? false,
    generatedPCCPackexpByteLang0TagCount: nf.generatedPCCPackexpByteLang0TagCount ?? false,
    generatedPCCPackexpByteLang0TagsUnique: nf.generatedPCCPackexpByteLang0TagsUnique ?? false,
    generatedPCCPackexpByteLang0RequiredTagsPresent: nf.generatedPCCPackexpByteLang0RequiredTagsPresent ?? false,
    generatedPCCPackexpByteLang0SortCount: nf.generatedPCCPackexpByteLang0SortCount ?? false,
    generatedPCCPackexpByteLang0RequiredSortsPresent: nf.generatedPCCPackexpByteLang0RequiredSortsPresent ?? false,
    generatedPCCPackexpByteLang0ConstructorCount: nf.generatedPCCPackexpByteLang0ConstructorCount ?? false,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent: nf.generatedPCCPackexpByteLang0RequiredConstructorsPresent ?? false,
    generatedPCCPackexpByteLang0RecordCount: nf.generatedPCCPackexpByteLang0RecordCount ?? false,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent: nf.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent ?? false,
    generatedPCCPackexpByteLang0PiBootDigestMatches: nf.generatedPCCPackexpByteLang0PiBootDigestMatches ?? false,
    generatedPCCPackexpBootAudit0: nf.generatedPCCPackexpBootAudit0 ?? false,
    generatedPCCPackexpBootAudit0Accepted: nf.generatedPCCPackexpBootAudit0Accepted ?? false,
    generatedPCCPackexpBootAudit0Checker: nf.generatedPCCPackexpBootAudit0Checker ?? false,
    generatedPCCPackexpBootAudit0Digest: nf.generatedPCCPackexpBootAudit0Digest ?? false,
    generatedPCCPackexpBootAudit0DigestMatchesNF: nf.generatedPCCPackexpBootAudit0DigestMatchesNF ?? false,
    generatedPCCPackexpBootAudit0NFKind: nf.generatedPCCPackexpBootAudit0NFKind ?? false,
    generatedPCCPackexpBootAudit0SuiteId: nf.generatedPCCPackexpBootAudit0SuiteId ?? false,
    generatedPCCPackexpBootAudit0CaseCount: nf.generatedPCCPackexpBootAudit0CaseCount ?? false,
    generatedPCCPackexpBootAudit0PositiveCount: nf.generatedPCCPackexpBootAudit0PositiveCount ?? false,
    generatedPCCPackexpBootAudit0NegativeCount: nf.generatedPCCPackexpBootAudit0NegativeCount ?? false,
    generatedPCCPackexpBootAudit0CoversB0Accept: nf.generatedPCCPackexpBootAudit0CoversB0Accept ?? false,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject: nf.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject ?? false,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: nf.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject ?? false,
    generatedPCCPackexpPiBoot0: nf.generatedPCCPackexpPiBoot0 ?? false,
    generatedPCCPackexpPiBoot0Accepted: nf.generatedPCCPackexpPiBoot0Accepted ?? false,
    generatedPCCPackexpPiBoot0Kind: nf.generatedPCCPackexpPiBoot0Kind ?? false,
    generatedPCCPackexpPiBoot0Digest: nf.generatedPCCPackexpPiBoot0Digest ?? false,
    generatedPCCPackexpPiBoot0Materialized: nf.generatedPCCPackexpPiBoot0Materialized ?? false,
    generatedPCCPackexpPiBoot0ExternalJson: nf.generatedPCCPackexpPiBoot0ExternalJson ?? false,
    generatedPCCPackexpPiBoot0RefCount: nf.generatedPCCPackexpPiBoot0RefCount ?? false,
    generatedPCCPackexpPiBoot0AllBootRefsPresent: nf.generatedPCCPackexpPiBoot0AllBootRefsPresent ?? false,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects: nf.generatedPCCPackexpPiBoot0RefsMatchBootObjects ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0: nf.generatedPCCPackexpPiBoot0RefsIncludeByteLang0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0: nf.generatedPCCPackexpPiBoot0RefsIncludeCodec0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0: nf.generatedPCCPackexpPiBoot0RefsIncludeDigest0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0: nf.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeSched0: nf.generatedPCCPackexpPiBoot0RefsIncludeSched0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0: nf.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeB0: nf.generatedPCCPackexpPiBoot0RefsIncludeB0 ?? false,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0: nf.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0 ?? false,
    generatedPCCPackexpConcreteKBundle0: nf.generatedPCCPackexpConcreteKBundle0 ?? false,
    generatedPCCPackexpConcreteKBundle0Accepted: nf.generatedPCCPackexpConcreteKBundle0Accepted ?? false,
    generatedPCCPackexpConcreteKBundle0Checker: nf.generatedPCCPackexpConcreteKBundle0Checker ?? false,
    generatedPCCPackexpConcreteKBundle0Digest: nf.generatedPCCPackexpConcreteKBundle0Digest ?? false,
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest: nf.generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest ?? false,
    generatedPCCPackexpConcreteKBundle0BootDigest: nf.generatedPCCPackexpConcreteKBundle0BootDigest ?? false,
    generatedPCCPackexpConcreteKBundle0KImplDigest: nf.generatedPCCPackexpConcreteKBundle0KImplDigest ?? false,
    generatedPCCPackexpConcreteKBundle0K0Digest: nf.generatedPCCPackexpConcreteKBundle0K0Digest ?? false,
    generatedPCCPackexpConcreteKBundle0SigmaDigest: nf.generatedPCCPackexpConcreteKBundle0SigmaDigest ?? false,
    generatedPCCPackexpConcreteKBundle0ReflectionDigest: nf.generatedPCCPackexpConcreteKBundle0ReflectionDigest ?? false,
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest: nf.generatedPCCPackexpConcreteKBundle0ProofInventoryDigest ?? false,
    generatedPCCPackexpConcreteKBundle0KernelRuleCount: nf.generatedPCCPackexpConcreteKBundle0KernelRuleCount ?? false,
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount: nf.generatedPCCPackexpConcreteKBundle0ConformanceNodeCount ?? false,
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete: nf.generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete ?? false,
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount: nf.generatedPCCPackexpConcreteKBundle0SigmaTheoremCount ?? false,
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete: nf.generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete ?? false,
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve: nf.generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve ?? false,
    generatedPCCPackexpConcreteKBundle0ReflectionCount: nf.generatedPCCPackexpConcreteKBundle0ReflectionCount ?? false,
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete: nf.generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete ?? false,
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve: nf.generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve ?? false,
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs: nf.generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs ?? false,
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols: nf.generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols ?? false,
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0: nf.generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0 ?? false,
    finalCertificateUsesConcreteAcceptRun: nf.finalCertificateUsesConcreteAcceptRun ?? false,
    statusUsesConcreteFinalCertificate: nf.statusUsesConcreteFinalCertificate ?? false,
    publicStatusCertificateDigestMatchesConcrete: nf.publicStatusCertificateDigestMatchesConcrete ?? false,
    publicStatusFinalVerdictDigestMatchesConcrete: nf.publicStatusFinalVerdictDigestMatchesConcrete ?? false,
    publicStatusAcceptRunDigestMatchesConcrete: nf.publicStatusAcceptRunDigestMatchesConcrete ?? false,
    publicStatusPccPackDigestMatchesConcrete: nf.publicStatusPccPackDigestMatchesConcrete ?? false,
    gateDigest: nf.gateDigest ?? null,
  };
}

function sameConcreteReleaseAuditPublicConclusion0(value) {
  return (
    isPlainObject(value) &&
    value.antecedent === 'CheckPCCPackexp(GeneratePCCPack())=accept' &&
    value.consequent === 'P = NP' &&
    value.conditional === true
  );
}

function isConcreteDigestLike0(value) {
  return (
    isPlainObject(value) &&
    typeof value.hex === 'string' &&
    /^[0-9a-f]{64}$/.test(value.hex)
  );
}


export function summarizeReleaseAudit0(out) {
  const nf = out?.NF ?? out?.nf ?? {};

  if (out.tag === 'accept') {
    const summary = {
      tag: out.tag,
      checker: out.checker,
      moduleCount: out.NF.moduleCount,
      testCount: out.NF.testCount,
      checkerCoverageCount: out.NF.checkerCoverageCount,

      publicSurfaceFreeze: out.NF.publicSurfaceFreeze,
      publicSurfaceFreezeSummary: out.NF.publicSurfaceFreezeSummary,
      publicSurfaceFreezeDigest: out.NF.publicSurfaceFreezeDigest,
      publicSurfaceFreezePublicEntryExportCount: out.NF.publicSurfaceFreezePublicEntryExportCount,
      publicSurfaceFreezePackageExportCount: out.NF.publicSurfaceFreezePackageExportCount,
      publicSurfaceFreezePackageBinCount: out.NF.publicSurfaceFreezePackageBinCount,
      publicSurfaceFreezePackageScriptCount: out.NF.publicSurfaceFreezePackageScriptCount,
      publicSurfaceFreezeSurfaceFrozen: out.NF.publicSurfaceFreezeSurfaceFrozen,

      materializedPublicStatusGate: out.NF.materializedPublicStatusGate,
      materializedPublicStatusGateSummary: out.NF.materializedPublicStatusGateSummary,
      materializedPublicStatusGateDigest: out.NF.materializedPublicStatusGateDigest,
      materializedPublicStatusGateFileCount: out.NF.materializedPublicStatusGateFileCount,
      materializedPublicStatusGateDirectRecordCount: out.NF.materializedPublicStatusGateDirectRecordCount,
      materializedPublicStatusGateCliRecordCount: out.NF.materializedPublicStatusGateCliRecordCount,
      materializedPublicStatusGateAcceptedPublicConclusionOnly: out.NF.materializedPublicStatusGateAcceptedPublicConclusionOnly,

      finalCertificatePublicStatusGate: nf.finalCertificatePublicStatusGate,

      finalCertificatePublicStatusGateSummary: nf.finalCertificatePublicStatusGateSummary,

      finalCertificatePublicStatusGateDigest: nf.finalCertificatePublicStatusGateDigest,

      finalCertificatePublicStatusGateStatus: nf.finalCertificatePublicStatusGateStatus,

      finalCertificatePublicStatusGateVerdict: nf.finalCertificatePublicStatusGateVerdict,

      finalCertificatePublicStatusGatePublicConclusionEmitted: nf.finalCertificatePublicStatusGatePublicConclusionEmitted,

      finalCertificatePublicStatusGateCertificateDigest: nf.finalCertificatePublicStatusGateCertificateDigest,

      finalCertificatePublicStatusGateFinalVerdictDigest: nf.finalCertificatePublicStatusGateFinalVerdictDigest,

      finalCertificatePublicStatusGateAcceptRunDigest: nf.finalCertificatePublicStatusGateAcceptRunDigest,

      finalCertificatePublicStatusGatePccPackDigest: nf.finalCertificatePublicStatusGatePccPackDigest,

      finalCertificatePublicStatusGateReleaseAuditAttached: nf.finalCertificatePublicStatusGateReleaseAuditAttached,

      concreteFinalCertificatePublicStatusGate: nf.concreteFinalCertificatePublicStatusGate,

      concreteFinalCertificatePublicStatusGateSummary: nf.concreteFinalCertificatePublicStatusGateSummary,

      concreteFinalCertificatePublicStatusGateDigest: nf.concreteFinalCertificatePublicStatusGateDigest,

      concreteFinalCertificatePublicStatusGateStatus: nf.concreteFinalCertificatePublicStatusGateStatus,

      concreteFinalCertificatePublicStatusGateVerdict: nf.concreteFinalCertificatePublicStatusGateVerdict,

      concreteFinalCertificatePublicStatusGatePublicConclusionEmitted: nf.concreteFinalCertificatePublicStatusGatePublicConclusionEmitted,

      concreteFinalCertificatePublicStatusGateCertificateDigest: nf.concreteFinalCertificatePublicStatusGateCertificateDigest,

      concreteFinalCertificatePublicStatusGateFinalVerdictDigest: nf.concreteFinalCertificatePublicStatusGateFinalVerdictDigest,

      concreteFinalCertificatePublicStatusGateAcceptRunDigest: nf.concreteFinalCertificatePublicStatusGateAcceptRunDigest,

      concreteFinalCertificatePublicStatusGatePccPackDigest: nf.concreteFinalCertificatePublicStatusGatePccPackDigest,

      concreteFinalCertificatePublicStatusGateReleaseAuditAttached: nf.concreteFinalCertificatePublicStatusGateReleaseAuditAttached,

      concreteFinalCertificatePublicStatusGateConcreteRows: nf.concreteFinalCertificatePublicStatusGateConcreteRows,

      concreteFinalCertificatePublicStatusGateConcreteLocalPackages: nf.concreteFinalCertificatePublicStatusGateConcreteLocalPackages,

      concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls: nf.concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls,

      concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG: nf.concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG,
    concreteFinalCertificatePublicStatusGateConcreteKBundle: nf.concreteFinalCertificatePublicStatusGateConcreteKBundle,
    concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete: nf.concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete,
    concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve: nf.concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve,
    concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve: nf.concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve,
    concreteFinalCertificatePublicStatusGateConcreteHardCheck: nf.concreteFinalCertificatePublicStatusGateConcreteHardCheck,
    concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete: nf.concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete,
    concreteFinalCertificatePublicStatusGateHardRowKeyCoverageComplete: nf.concreteFinalCertificatePublicStatusGateHardRowKeyCoverageComplete,
    concreteFinalCertificatePublicStatusGateHardRoutePriorityComplete: nf.concreteFinalCertificatePublicStatusGateHardRoutePriorityComplete,
    concreteFinalCertificatePublicStatusGateHardProofRefPolicyComplete: nf.concreteFinalCertificatePublicStatusGateHardProofRefPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardHashDisciplineComplete: nf.concreteFinalCertificatePublicStatusGateHardHashDisciplineComplete,
    concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete: nf.concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete,
    concreteFinalCertificatePublicStatusGateHardImportPolicyComplete: nf.concreteFinalCertificatePublicStatusGateHardImportPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardReflectionPolicyComplete: nf.concreteFinalCertificatePublicStatusGateHardReflectionPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardBoundsPolicyComplete: nf.concreteFinalCertificatePublicStatusGateHardBoundsPolicyComplete,
    concreteFinalCertificatePublicStatusGateHardDiagnosticsPolicyComplete: nf.concreteFinalCertificatePublicStatusGateHardDiagnosticsPolicyComplete,
    concreteFinalCertificatePublicStatusGateConcreteFinalIntegration: nf.concreteFinalCertificatePublicStatusGateConcreteFinalIntegration,
    concreteFinalCertificatePublicStatusGateFinalIntegrationConcreteGlobalProofDAG: nf.concreteFinalCertificatePublicStatusGateFinalIntegrationConcreteGlobalProofDAG,
    concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete: nf.concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete,
    concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete: nf.concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete,
    concreteFinalCertificatePublicStatusGateFinalIntegrationUsesGPack: nf.concreteFinalCertificatePublicStatusGateFinalIntegrationUsesGPack,
    concreteFinalCertificatePublicStatusGateRowFamGUsesGPack: nf.concreteFinalCertificatePublicStatusGateRowFamGUsesGPack,
    concreteFinalCertificatePublicStatusGateFinalTheoremUsesFinalIntegration: nf.concreteFinalCertificatePublicStatusGateFinalTheoremUsesFinalIntegration,
    concreteFinalCertificatePublicStatusGateRowFamFinalUsesFinalTheorem: nf.concreteFinalCertificatePublicStatusGateRowFamFinalUsesFinalTheorem,
    concreteFinalCertificatePublicStatusGateFinalMatchUsesGPack: nf.concreteFinalCertificatePublicStatusGateFinalMatchUsesGPack,
    concreteFinalCertificatePublicStatusGateSatDecisionUsesGPack: nf.concreteFinalCertificatePublicStatusGateSatDecisionUsesGPack,
    concreteFinalCertificatePublicStatusGateConcretePCCPack: nf.concreteFinalCertificatePublicStatusGateConcretePCCPack,
    concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest: nf.concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest,
    concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun: nf.concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToRows: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToRows,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration,
    concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem: nf.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted,
    concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional: nf.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope,
    concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: nf.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoverageDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0FamilyCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0RequiredFamilyCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0Families,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0AllRequiredFamiliesPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversIface,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversSched,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversNF,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversTruthEval,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRel,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversCharge,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversObl,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversArith,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversMode,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversRoute,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversHash,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0B0CoversImport,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0RequiredRuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0Rules,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredRulesPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasEq,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasSubst,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRecord,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDAGInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasLedgerInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasOblTopoInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTraceInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteExhaust,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasDPInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasHall,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasRankInd,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasMinCounterexample,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasIntArith,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTransport,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasTruthVec,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0HasFiniteRel,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKindCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofNodeKinds,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsRejectOpaque,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsTypedAcyclic,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0ProofRefsHashIndependent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpKernelSeed0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0Canonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncoding,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NaturalEncodingCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncoding,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0IntegerEncodingCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncoding,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0StringEncodingCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0TopLevelConsumesAllBytes,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerialization,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0NormalFormSerializationCanonical,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCodec0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Alg,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0AlgSHA256,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0Bytes,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0BytesCanonicalJson,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0EqualityNotObjectEquality,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0FullKeyComparisonAfterHashLookup,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpDigest0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0ForbiddenSymbolCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0NoExecutableMinSymbols,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PublicConstructorsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0CriticalKindsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0RouteTokensPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpIfaceDict0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreMatchesExpected,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreB0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreK0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreR0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreH0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreO0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0CoreRel0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0ScaleFactorsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBH,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0SelectorBoundBTheta,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PolynomialExponent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpSched0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0TagsUnique,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredTagsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0SortCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredSortsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0ConstructorCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredConstructorsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RecordCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0RequiredRecordAritiesPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpByteLang0PiBootDigestMatches,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Checker,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0DigestMatchesNF,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NFKind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0SuiteId,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CaseCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0PositiveCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0NegativeCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0Accept,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0MissingCoverageReject,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBootAudit0CoversB0HashKeyTamperReject,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Kind,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0Materialized,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0ExternalJson,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0AllBootRefsPresent,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsMatchBootObjects,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeByteLang0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeCodec0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeDigest0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeIfaceDict0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeSched0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeKernelSeed0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeB0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPiBoot0RefsIncludeBootAudit0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Accepted: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Accepted,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Checker: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Checker,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0MaterializedKBundleDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0MaterializedKBundleDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0BootDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0BootDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KImplDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KImplDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0K0Digest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0K0Digest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ProofInventoryDigest: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ProofInventoryDigest,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ConformanceNodeCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ConformanceNodeCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaTheoremCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaTheoremCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaCoverageComplete: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaCoverageComplete,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaProofRefsResolve: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0SigmaProofRefsResolve,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCount: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCount,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCoverageComplete: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionCoverageComplete,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoOpaqueProofRefs: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoOpaqueProofRefs,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoExecutableMinSymbols: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0NoExecutableMinSymbols,
    concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0: nf.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0,

      concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate: nf.concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate,

      publicConclusion: out.NF.publicConclusion,
      digest: out.Digest,
    };

    const surface = validateReleaseAuditCliSummarySurface0(summary);

    if (!surface.ok) {
      return {
        tag: 'reject',
        checker: 'summarizeReleaseAudit0',
        coord: 'summarizeReleaseAudit0.surface',
        path: surface.path,
        witness: surface.witness,
        digest: digestCanonical0(surface.witness),
      };
    }

    return summary;
  }

  return {
    tag: out.tag,
    checker: out.checker,
    coord: out.Coord,
    path: out.Path,
    witness: out.Witness,
    digest: out.Digest,
  };
}

export function validateReleaseAuditSurface0(nf, phaseOrder = null) {
  const nfKeys = validateExactObjectKeys0(nf, RELEASE_AUDIT_NF_KEYS0, ['NF']);

  if (!nfKeys.ok) {
    return nfKeys;
  }

  const publicSurfaceSummaryKeys = validateExactObjectKeys0(
    nf.publicSurfaceFreezeSummary,
    RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0,
    ['NF', 'publicSurfaceFreezeSummary'],
  );

  if (!publicSurfaceSummaryKeys.ok) {
    return publicSurfaceSummaryKeys;
  }

  const gateSummaryKeys = validateExactObjectKeys0(
    nf.materializedPublicStatusGateSummary,
    RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0,
    ['NF', 'materializedPublicStatusGateSummary'],
  );

  if (!gateSummaryKeys.ok) {
    return gateSummaryKeys;
  }

  if (phaseOrder !== null) {
    const phaseOrderCheck = validateReleaseAuditPhaseOrder0(phaseOrder);

    if (!phaseOrderCheck.ok) {
      return phaseOrderCheck;
    }
  }

  return validationAccept0({
    kind: 'ReleaseAuditSurfaceFreeze0NF',
    nfKeys: RELEASE_AUDIT_NF_KEYS0,
    publicSurfaceSummaryKeys: RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0,
    materializedGateSummaryKeys: RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0,
    phaseOrder: phaseOrder ?? RELEASE_AUDIT_PHASE_ORDER0,
  });
}

export function validateReleaseAuditPhaseOrder0(phaseOrder) {
  if (!Array.isArray(phaseOrder)) {
    return validationReject0(['Ledger'], 'release audit phase order must be an array', {
      actual: typeof phaseOrder,
    });
  }

  if (stableStringify0(phaseOrder) !== stableStringify0(RELEASE_AUDIT_PHASE_ORDER0)) {
    return validationReject0(['Ledger', 'phaseOrder'], 'release audit phase order changed', {
      expectedPhaseOrder: RELEASE_AUDIT_PHASE_ORDER0,
      actualPhaseOrder: phaseOrder,
      missingPhases: RELEASE_AUDIT_PHASE_ORDER0.filter((phase) => !phaseOrder.includes(phase)),
      extraPhases: phaseOrder.filter((phase) => !RELEASE_AUDIT_PHASE_ORDER0.includes(phase)),
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditPhaseOrderFreeze0NF',
    phaseOrder,
  });
}

export function validateReleaseAuditCliSummarySurface0(summary) {
  const summaryKeys = validateExactObjectKeys0(summary, RELEASE_AUDIT_CLI_SUMMARY_KEYS0, ['summary']);

  if (!summaryKeys.ok) {
    return summaryKeys;
  }

  const publicSurfaceSummaryKeys = validateExactObjectKeys0(
    summary.publicSurfaceFreezeSummary,
    RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0,
    ['summary', 'publicSurfaceFreezeSummary'],
  );

  if (!publicSurfaceSummaryKeys.ok) {
    return publicSurfaceSummaryKeys;
  }

  const gateSummaryKeys = validateExactObjectKeys0(
    summary.materializedPublicStatusGateSummary,
    RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0,
    ['summary', 'materializedPublicStatusGateSummary'],
  );

  if (!gateSummaryKeys.ok) {
    return gateSummaryKeys;
  }

  return validationAccept0({
    kind: 'ReleaseAuditCliSummarySurfaceFreeze0NF',
    summaryKeys: RELEASE_AUDIT_CLI_SUMMARY_KEYS0,
    publicSurfaceSummaryKeys: RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0,
    materializedGateSummaryKeys: RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0,
  });
}

function validateExactObjectKeys0(value, expectedKeys, path) {
  if (!isPlainObject(value)) {
    return validationReject0(path, 'surface freeze target must be an object', {
      actual: typeof value,
    });
  }

  const actualKeys = Object.keys(value);

  if (stableStringify0(actualKeys) !== stableStringify0(expectedKeys)) {
    return validationReject0(path, 'release audit surface keys changed', {
      expectedKeys,
      actualKeys,
      missingKeys: expectedKeys.filter((key) => !actualKeys.includes(key)),
      extraKeys: actualKeys.filter((key) => !expectedKeys.includes(key)),
    });
  }

  return validationAccept0({
    kind: 'ExactObjectKeys0NF',
    keys: actualKeys,
  });
}

function expectedModuleForTest0(testFile) {
  const stem = testFile.replace(/\.test\.mjs$/, '');

  if (testFile === 'pcc-release-audit-final-certificate-surface0.test.mjs') {
    return 'pcc-release-audit0.mjs';
  }  

  const explicit = {
    'pcc-release-audit-concrete-final-certificate-surface0': 'pcc-release-audit0.mjs',
    'pcc-core': 'pcc-core.mjs',
    'pcc-core.negative': 'pcc-core.mjs',
    'pcc-core-negative': 'pcc-core.mjs',
    'pcc-verifier-frag0-current-suite': 'pcc-verifier-frag0.mjs',
    'pcc-boot0-batch0-coverage': 'pcc-boot0.mjs',
    'pcc-public-entry0': 'index.mjs',
    'pcc-public-api0': 'index.mjs',
    'pcc-integrated-pipeline-tamper0': 'pcc-integrated-pipeline0.mjs',
    'pcc-release-audit0-negative': 'pcc-release-audit0.mjs',
    'pcc-materialized-aggregate-cli0': 'bin/check-materialized-aggregate0.mjs',
    'pcc-materialized-acceptance-bridge-cli0': 'bin/check-materialized-acceptance-bridge0.mjs',
    'pcc-materialized-path-readme0': 'README.md',
    'pcc-materialized-accept-run-cli0': 'bin/check-materialized-accept-run0.mjs',
    'pcc-materialized-final-verdict-cli0': 'bin/check-materialized-final-verdict0.mjs',
    'pcc-materialized-public-status-cli0': 'bin/check-materialized-public-status0.mjs',
    'pcc-materialized-public-status-release-gate0': 'README.md',
    'pcc-release-audit-materialized-gate0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-materialized-gate-negative0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-cli-materialized-gate0': 'bin/release-audit0.mjs',
    'pcc-release-audit-full-mode-gate-summary0': 'bin/release-audit0.mjs',
    'pcc-release-audit-surface-freeze0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-public-surface-freeze0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-public-surface-summary0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-public-surface-summary-negative0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-phase-order-freeze0': 'pcc-release-audit0.mjs',
    'pcc-release-audit-cli-hard-gate0': 'bin/release-audit0.mjs',
    'pcc-release-audit-readme-negative0': 'pcc-release-audit0.mjs',                                              
  };

  if (Object.prototype.hasOwnProperty.call(explicit, stem)) {
    return explicit[stem];
  }

  return `${stem}.mjs`;
}

async function readJsonFile0(filePath) {
  try {
    const text = await fs.readFile(filePath, 'utf8');
    return {
      ok: true,
      value: JSON.parse(text),
    };
  } catch (error) {
    return {
      ok: false,
      witness: {
        filePath,
        error: error.message,
      },
    };
  }
}

async function walkFiles0(dir) {
  const out = [];
  const entries = await fs.readdir(dir, {
    withFileTypes: true,
  });

  for (const entry of entries) {
    const absolute = path.join(dir, entry.name);

    if (entry.isDirectory()) {
      out.push(...await walkFiles0(absolute));
    } else if (entry.isFile()) {
      out.push(absolute);
    }
  }

  return out;
}

async function pathExists0(filePath) {
  try {
    await fs.access(filePath);
    return true;
  } catch {
    return false;
  }
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

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}