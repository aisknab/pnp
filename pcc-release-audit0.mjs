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