#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { CheckActivatedPNPStatus0 } from './pcc-activated-pnp-status0.mjs';
import { CheckFormalReconstructionStatus0 } from './pcc-formal-reconstruction-status0.mjs';
import {
  CheckPublicTheoremActivation0,
  EvaluatePublicTheoremActivationExample0,
} from './pcc-public-theorem-activation0.mjs';
import {
  CheckUnrestrictedFinalSoundnessRelease0,
  EvaluateUnrestrictedFinalSoundnessReleaseExample0,
} from './pcc-unrestricted-final-soundness-release0.mjs';
import { CheckUniformFinalSoundnessTarget0 } from './pcc-uniform-final-soundness-target0.mjs';
import { CheckUniformInputFamily0 } from './pcc-uniform-input-family0.mjs';
import { CheckUniformLockedNANDConstruction0 } from './pcc-uniform-locked-nand-construction0.mjs';
import { CheckUniformLockedNANDThreshold0 } from './pcc-uniform-locked-nand-threshold0.mjs';
import { CheckUniformResidualBandMinimizer0 } from './pcc-uniform-residual-band-minimizer0.mjs';
import { CheckUniformZeroSlackClosure0 } from './pcc-uniform-zeroslack-closure0.mjs';
import {
  CheckNoHiddenOracleSemantic0,
  EvaluateNoHiddenOracleSemanticExample0,
} from './pcc-no-hidden-oracle-semantic0.mjs';
import {
  CheckUniformComplexityConclusion0,
  EvaluateComplexityConclusionExample0,
} from './pcc-uniform-complexity-conclusion0.mjs';
import * as publicEntry0 from './index.mjs';
import {
  CheckRunAll0 as PackageCheckRunAll0,
  RunAll0 as PackageRunAll0,
  makeSyntheticRunAllInput0,
} from './pcc-runall0.mjs';
import {
  CheckIntegratedPipeline0,
  RunIntegratedPCC0,
  makeSyntheticIntegratedPipeline0,
} from './pcc-integrated-pipeline0.mjs';
import {
  CheckAcceptRun0,
  EmitFinalVerdict0,
  ReplayAcceptRun0,
  makeSyntheticAcceptRun0,
  makeSyntheticRejectAcceptRun0,
} from './pcc-accept-run0.mjs';
import { CheckReleaseAudit0 as PackageReleaseAudit0 } from './pcc-release-audit0.mjs';
import {
  CheckMaterializedAcceptanceBridge0,
  CheckMaterializedAcceptanceBridgeFile0,
  makeAcceptedMaterializedAcceptanceBridge0,
  makeMaterializedAcceptanceBridge0,
} from './pcc-materialized-acceptance-bridge0.mjs';
import {
  CheckMaterializedAcceptRun0,
  CheckMaterializedAcceptRunFile0,
  makeMaterializedAcceptRun0 as makeLegacyMaterializedAcceptRun0,
} from './pcc-materialized-accept-run0.mjs';
import {
  CheckMaterializedFinalVerdict0,
  CheckMaterializedFinalVerdictFile0,
} from './pcc-materialized-final-verdict0.mjs';
import {
  CheckMaterializedPublicStatus0,
  CheckMaterializedPublicStatusFile0,
} from './pcc-materialized-public-status0.mjs';
import { WriteMaterializedFixtureSet0 } from './pcc-materialized-fixture-writer0.mjs';
import { WriteMaterializedAcceptRunFixtureSet0 } from './pcc-materialized-accept-run-fixtures0.mjs';
import { WriteMaterializedFinalRunFixtureSet0 } from './pcc-materialized-final-run-fixtures0.mjs';
import { CheckMaterializedFinalRunRoundtrip0 } from './pcc-materialized-final-run-roundtrip0.mjs';
import { CheckMaterializedPublicStatusRoundtrip0 } from './pcc-materialized-public-status-roundtrip0.mjs';
import {
  CheckMaterializedGeneratedAcceptRun0,
  makeMaterializedAcceptRun0 as makeGeneratedMaterializedAcceptRun0,
  makeMaterializedGeneratedAcceptRun0,
  writeMaterializedGeneratedAcceptRunFiles0,
} from './pcc-accept-run-materialized0.mjs';
import {
  CheckMaterializedFinalCertificate0,
  makeFinalCertificateRecord0,
  makeMaterializedFinalCertificate0,
  writeMaterializedFinalCertificateFiles0,
} from './pcc-final-certificate-materialized0.mjs';
import {
  CheckFinalCertificatePublicStatus0,
  emitFinalCertificatePublicStatus0,
  makeFinalCertificatePublicStatus0,
  writeFinalCertificatePublicStatusFiles0,
} from './pcc-final-certificate-public-status0.mjs';
import {
  CheckReleaseAuditFinalCertificateGate0,
  makeReleaseAuditFinalCertificateGate0,
  writeReleaseAuditFinalCertificateGateFiles0,
} from './pcc-release-audit-final-certificate-gate0.mjs';
import {
  CheckReleaseAuditConcreteFinalCertificateGate0,
  makeReleaseAuditConcreteFinalCertificateGate0,
  writeReleaseAuditConcreteFinalCertificateGateFiles0,
} from './pcc-release-audit-final-certificate-concrete-gate0.mjs';
import {
  CheckConcreteReleaseAppendix0,
  makeConcreteReleaseAppendix0,
  makeConcreteReleaseAppendixRecord0,
  writeConcreteReleaseAppendixFiles0,
} from './pcc-concrete-release-appendix0.mjs';
import {
  CheckConcreteFinalAcceptanceReplay0,
  makeConcreteFinalAcceptanceReplay0,
  writeConcreteFinalAcceptanceReplayFiles0,
} from './pcc-final-acceptance-replay0.mjs';
import {
  CheckFinalPNPCertificate0,
  makeFinalPNPCertificate0,
  makeFinalPNPCertificateRecord0,
  writeFinalPNPCertificateFiles0,
} from './pcc-final-pnp-certificate0.mjs';
import {
  CheckFinalPNPReleaseGate0,
  makeFinalPNPReleaseGate0,
  writeFinalPNPReleaseGateFiles0,
} from './pcc-final-pnp-release-gate0.mjs';
import {
  CheckFinalPNPProofReport0,
  makeFinalPNPProofReport0,
  makeFinalPNPProofReportRecord0,
  writeFinalPNPProofReportFiles0,
} from './pcc-final-proof-report0.mjs';
import {
  CheckConcreteMaterializedGeneratedAcceptRun0,
  makeConcreteMaterializedGeneratedAcceptRun0,
  writeConcreteMaterializedGeneratedAcceptRunFiles0,
} from './pcc-accept-run-concrete-materialized0.mjs';
import {
  CheckConcreteMaterializedFinalCertificate0,
  makeConcreteMaterializedFinalCertificate0,
  writeConcreteMaterializedFinalCertificateFiles0,
} from './pcc-final-certificate-concrete-materialized0.mjs';
import {
  CheckConcreteFinalCertificatePublicStatus0,
  makeConcreteFinalCertificatePublicStatus0,
  writeConcreteFinalCertificatePublicStatusFiles0,
} from './pcc-final-certificate-public-status-concrete0.mjs';
import {
  BuildCurrentRunBundle0,
  BuildPNPLabsRunRecord0,
  UploadPNPLabsIssue0,
  WritePNPLabsUploadFiles0,
} from './scripts/pnp-verify-and-upload.mjs';
import {
  CheckMaterializedFixtureRoundtrip0,
  CheckMaterializedFixtureRoundtripDirs0,
} from './pcc-materialized-fixture-roundtrip0.mjs';
import {
  IndexMaterializedFixtureDigests0,
  ResolveMaterializedDigest0,
} from './pcc-materialized-digest-resolver0.mjs';
import {
  CheckMaterializedScaffoldBurndown0,
  makeMaterializedScaffoldBurndown0,
  writeMaterializedScaffoldBurndownFiles0,
} from './pcc-materialized-scaffold-burndown0.mjs';
import {
  CheckMaterializedFinalIntegration0,
  makeMaterializedFinalIntegrationEnvelope0,
  makeMaterializedFinalTheorem0,
  makeMaterializedRowFamFinal0,
  writeMaterializedFinalIntegrationFiles0,
} from './pcc-final-integration-materialized0.mjs';
import {
  CheckConcreteMaterializedFinalIntegration0,
  makeConcreteMaterializedFinalIntegration0,
  writeConcreteMaterializedFinalIntegrationFiles0,
} from './pcc-final-integration-concrete-materialized0.mjs';
import {
  CheckMaterializedPCCPack0,
  makeMaterializedPCCPack0,
  writeMaterializedPCCPackFiles0,
} from './pcc-pack-materialized0.mjs';
import {
  CheckConcreteMaterializedPCCPack0,
  makeConcreteMaterializedPCCPack0,
  writeConcreteMaterializedPCCPackFiles0,
} from './pcc-pack-concrete-materialized0.mjs';
import {
  CheckGeneratedPCCPackexp0,
  GeneratePCCPack0,
  makeGeneratedPCCPackexp0,
  writeGeneratedPCCPackexpFiles0,
} from './pcc-generate-pcc-pack0.mjs';
import {
  CheckFinal0,
  CheckRowFamFinal0,
  makeSyntheticFinalTheorem0,
  makeSyntheticRowFamFinal0,
} from './pcc-final0.mjs';
import {
  CheckPackSufficiency0,
  makeSyntheticPCCPack0,
  makeSyntheticPackSufficiencyTheorem0,
} from './pcc-pack-sufficiency0.mjs';
import { CheckPCCPackexp0 } from './pcc-check-pcc-pack-exp0.mjs';
import { makePCCPack0 } from './pcc-pack-materialized0.mjs';
import {
  CheckMaterializedCheckPCCPack0,
  makeMaterializedCheckPCCPackShell0,
} from './pcc-materialized-checkpack0.mjs';

const CHECKER = 'CheckFormalPublicSurface0';
const VERSION = 0;
const COORDINATE = 'PUBLIC-SURFACE-BASELINE-2026-07-10-FORMAL-RECONSTRUCTION-01';
const OUTPUT_PATH = 'artifacts/formal-public-surface/latest-verdict.json';

export const FORMAL_GATED_ENTRYPOINTS0 = Object.freeze([
  'pcc-uniform-final-soundness-target0.mjs',
  'pcc-uniform-input-family0.mjs',
  'pcc-uniform-locked-nand-construction0.mjs',
  'pcc-uniform-locked-nand-threshold0.mjs',
  'pcc-uniform-residual-band-minimizer0.mjs',
  'pcc-uniform-zeroslack-closure0.mjs',
  'pcc-no-hidden-oracle-semantic0.mjs',
  'pcc-uniform-complexity-conclusion0.mjs',
  'bin/runall0.mjs',
  'bin/release-audit0.mjs',
  'bin/check-materialized-acceptance-bridge0.mjs',
  'bin/check-materialized-fixture-roundtrip0.mjs',
  'bin/resolve-materialized-digest0.mjs',
  'bin/write-materialized-scaffold-burndown0.mjs',
  'bin/write-materialized-final-integration0.mjs',
  'bin/write-concrete-materialized-final-integration0.mjs',
  'bin/write-materialized-pcc-pack0.mjs',
  'bin/write-concrete-materialized-pcc-pack0.mjs',
  'bin/check-materialized-aggregate0.mjs',
  'tools/reproducibility-smoke.mjs',
  'bin/write-materialized-fixtures0.mjs',
  'bin/check-materialized-accept-run0.mjs',
  'bin/write-materialized-accept-run-fixtures0.mjs',
  'bin/check-materialized-final-verdict0.mjs',
  'bin/write-materialized-final-run-fixtures0.mjs',
  'bin/check-materialized-final-run-roundtrip0.mjs',
  'bin/check-materialized-public-status0.mjs',
  'bin/check-materialized-public-status-roundtrip0.mjs',
  'bin/write-materialized-accept-run0.mjs',
  'bin/write-concrete-materialized-accept-run0.mjs',
  'bin/write-materialized-final-certificate0.mjs',
  'bin/write-concrete-materialized-final-certificate0.mjs',
  'bin/write-final-certificate-public-status0.mjs',
  'bin/write-concrete-final-certificate-public-status0.mjs',
  'bin/write-release-audit-final-certificate-gate0.mjs',
  'bin/write-release-audit-concrete-final-certificate-gate0.mjs',
  'bin/write-concrete-release-appendix0.mjs',
  'bin/write-concrete-final-acceptance-replay0.mjs',
  'bin/write-final-pnp-certificate0.mjs',
  'bin/write-final-pnp-release-gate0.mjs',
  'bin/write-final-pnp-proof-report0.mjs',
  'scripts/pnp-verify-and-upload.mjs',
]);

const DEFAULT_REJECT_CHECKERS = Object.freeze([
  ['uniform-final-soundness-target', () => CheckUniformFinalSoundnessTarget0({ writeOutput: false })],
  ['uniform-input-family', () => CheckUniformInputFamily0({ writeOutput: false })],
  ['uniform-locked-nand-construction', () => CheckUniformLockedNANDConstruction0({ writeOutput: false })],
  ['uniform-locked-nand-threshold', () => CheckUniformLockedNANDThreshold0({ writeOutput: false })],
  ['uniform-residual-band-minimizer', () => CheckUniformResidualBandMinimizer0({ writeOutput: false })],
  ['uniform-zeroslack-closure', () => CheckUniformZeroSlackClosure0({ writeOutput: false })],
  ['no-hidden-oracle-semantic', () => CheckNoHiddenOracleSemantic0({ writeOutput: false })],
  ['no-hidden-oracle-example', () => EvaluateNoHiddenOracleSemanticExample0()],
  ['uniform-complexity-conclusion', () => CheckUniformComplexityConclusion0({ writeOutput: false })],
  ['uniform-complexity-example', () => EvaluateComplexityConclusionExample0()],
  ['unrestricted-final-soundness-release', () => CheckUnrestrictedFinalSoundnessRelease0({ writeOutput: false })],
  ['unrestricted-final-soundness-example', () => EvaluateUnrestrictedFinalSoundnessReleaseExample0()],
  ['public-theorem-activation', () => CheckPublicTheoremActivation0({ writeOutput: false })],
  ['public-theorem-activation-example', () => EvaluatePublicTheoremActivationExample0()],
  ['activated-pnp-status', () => CheckActivatedPNPStatus0({ writeOutput: false })],
  ['synthetic-accept-run-constructor', () => makeSyntheticAcceptRun0()],
  ['synthetic-reject-run-constructor', () => makeSyntheticRejectAcceptRun0()],
  ['synthetic-integrated-pipeline-constructor', () => makeSyntheticIntegratedPipeline0()],
  ['synthetic-runall-input-constructor', () => makeSyntheticRunAllInput0()],
  ['public-index-runall', () => publicEntry0.RunAll0()],
  ['public-index-check-runall', () => publicEntry0.CheckRunAll0()],
  ['public-index-integrated-pipeline', () => publicEntry0.CheckIntegratedPipeline0()],
  ['public-index-run-integrated-pipeline', () => publicEntry0.RunIntegratedPCC0()],
  ['public-index-check-accept-run', () => publicEntry0.CheckAcceptRun0()],
  ['public-index-replay-accept-run', () => publicEntry0.ReplayAcceptRun0()],
  ['public-index-emit-final-verdict', () => publicEntry0.EmitFinalVerdict0()],
  ['public-index-release-audit', () => publicEntry0.CheckReleaseAudit0()],
  ['package-subpath-runall', () => PackageRunAll0()],
  ['package-subpath-check-runall', () => PackageCheckRunAll0()],
  ['package-subpath-integrated-pipeline', () => CheckIntegratedPipeline0()],
  ['package-subpath-run-integrated-pipeline', () => RunIntegratedPCC0()],
  ['package-subpath-check-accept-run', () => CheckAcceptRun0()],
  ['package-subpath-replay-accept-run', () => ReplayAcceptRun0()],
  ['package-subpath-emit-final-verdict', () => EmitFinalVerdict0()],
  ['package-subpath-release-audit', () => PackageReleaseAudit0()],
  ['materialized-bridge-pending', () => makeMaterializedAcceptanceBridge0()],
  ['materialized-bridge-accepted', () => makeAcceptedMaterializedAcceptanceBridge0()],
  ['materialized-bridge-check', () => CheckMaterializedAcceptanceBridge0()],
  ['materialized-bridge-file-check', () => CheckMaterializedAcceptanceBridgeFile0()],
  ['materialized-accept-run-make', () => makeLegacyMaterializedAcceptRun0()],
  ['materialized-accept-run-check', () => CheckMaterializedAcceptRun0()],
  ['materialized-accept-run-file-check', () => CheckMaterializedAcceptRunFile0()],
  ['materialized-final-verdict-check', () => CheckMaterializedFinalVerdict0()],
  ['materialized-final-verdict-file-check', () => CheckMaterializedFinalVerdictFile0()],
  ['materialized-public-status-check', () => CheckMaterializedPublicStatus0()],
  ['materialized-public-status-file-check', () => CheckMaterializedPublicStatusFile0()],
  ['materialized-fixture-writer', () => WriteMaterializedFixtureSet0()],
  ['materialized-fixture-roundtrip', () => CheckMaterializedFixtureRoundtrip0()],
  ['materialized-fixture-roundtrip-dirs', () => CheckMaterializedFixtureRoundtripDirs0()],
  ['materialized-digest-index', () => IndexMaterializedFixtureDigests0()],
  ['materialized-digest-resolve', () => ResolveMaterializedDigest0()],
  ['materialized-scaffold-burndown-make', () => makeMaterializedScaffoldBurndown0()],
  ['materialized-scaffold-burndown-check', () => CheckMaterializedScaffoldBurndown0()],
  ['materialized-scaffold-burndown-write', () => writeMaterializedScaffoldBurndownFiles0()],
  ['materialized-final-integration-make', () => makeMaterializedFinalIntegrationEnvelope0()],
  ['materialized-final-theorem-make', () => makeMaterializedFinalTheorem0()],
  ['materialized-final-row-family-make', () => makeMaterializedRowFamFinal0()],
  ['materialized-final-integration-check', () => CheckMaterializedFinalIntegration0()],
  ['materialized-final-integration-write', () => writeMaterializedFinalIntegrationFiles0()],
  ['concrete-final-integration-make', () => makeConcreteMaterializedFinalIntegration0()],
  ['concrete-final-integration-check', () => CheckConcreteMaterializedFinalIntegration0()],
  ['concrete-final-integration-write', () => writeConcreteMaterializedFinalIntegrationFiles0()],
  ['materialized-pcc-pack-make', () => makeMaterializedPCCPack0()],
  ['materialized-pcc-pack-check', () => CheckMaterializedPCCPack0()],
  ['materialized-pcc-pack-write', () => writeMaterializedPCCPackFiles0()],
  ['concrete-materialized-pcc-pack-make', () => makeConcreteMaterializedPCCPack0()],
  ['concrete-materialized-pcc-pack-check', () => CheckConcreteMaterializedPCCPack0()],
  ['concrete-materialized-pcc-pack-write', () => writeConcreteMaterializedPCCPackFiles0()],
  ['generated-pcc-pack-generate', () => GeneratePCCPack0()],
  ['generated-pcc-pack-make', () => makeGeneratedPCCPackexp0()],
  ['generated-pcc-pack-check', () => CheckGeneratedPCCPackexp0()],
  ['generated-pcc-pack-write', () => writeGeneratedPCCPackexpFiles0()],
  ['synthetic-final-theorem-make', () => makeSyntheticFinalTheorem0()],
  ['synthetic-final-row-family-make', () => makeSyntheticRowFamFinal0()],
  ['synthetic-final-theorem-check', () => CheckFinal0()],
  ['synthetic-final-row-family-check', () => CheckRowFamFinal0()],
  ['synthetic-pack-theorem-make', () => makeSyntheticPackSufficiencyTheorem0()],
  ['synthetic-pcc-pack-make', () => makeSyntheticPCCPack0()],
  ['synthetic-pcc-pack-check', () => CheckPackSufficiency0()],
  ['explicit-pcc-pack-check', () => CheckPCCPackexp0()],
  ['materialized-pcc-pack-core-make', () => makePCCPack0()],
  ['materialized-accept-run-fixture-writer', () => WriteMaterializedAcceptRunFixtureSet0()],
  ['materialized-final-run-fixture-writer', () => WriteMaterializedFinalRunFixtureSet0()],
  ['materialized-final-run-roundtrip', () => CheckMaterializedFinalRunRoundtrip0()],
  ['materialized-public-status-roundtrip', () => CheckMaterializedPublicStatusRoundtrip0()],
  ['generated-materialized-accept-run-make-record', () => makeGeneratedMaterializedAcceptRun0()],
  ['generated-materialized-accept-run-make', () => makeMaterializedGeneratedAcceptRun0()],
  ['generated-materialized-accept-run-check', () => CheckMaterializedGeneratedAcceptRun0()],
  ['generated-materialized-accept-run-write', () => writeMaterializedGeneratedAcceptRunFiles0()],
  ['materialized-final-certificate-make', () => makeMaterializedFinalCertificate0()],
  ['materialized-final-certificate-record', () => makeFinalCertificateRecord0()],
  ['materialized-final-certificate-check', () => CheckMaterializedFinalCertificate0()],
  ['materialized-final-certificate-write', () => writeMaterializedFinalCertificateFiles0()],
  ['final-certificate-public-status-make', () => makeFinalCertificatePublicStatus0()],
  ['final-certificate-public-status-emit', () => emitFinalCertificatePublicStatus0()],
  ['final-certificate-public-status-check', () => CheckFinalCertificatePublicStatus0()],
  ['final-certificate-public-status-write', () => writeFinalCertificatePublicStatusFiles0()],
  ['release-audit-final-certificate-gate-make', () => makeReleaseAuditFinalCertificateGate0()],
  ['release-audit-final-certificate-gate-check', () => CheckReleaseAuditFinalCertificateGate0()],
  ['release-audit-final-certificate-gate-write', () => writeReleaseAuditFinalCertificateGateFiles0()],
  ['release-audit-concrete-gate-make', () => makeReleaseAuditConcreteFinalCertificateGate0()],
  ['release-audit-concrete-gate-check', () => CheckReleaseAuditConcreteFinalCertificateGate0()],
  ['release-audit-concrete-gate-write', () => writeReleaseAuditConcreteFinalCertificateGateFiles0()],
  ['concrete-release-appendix-make', () => makeConcreteReleaseAppendix0()],
  ['concrete-release-appendix-record', () => makeConcreteReleaseAppendixRecord0()],
  ['concrete-release-appendix-check', () => CheckConcreteReleaseAppendix0()],
  ['concrete-release-appendix-write', () => writeConcreteReleaseAppendixFiles0()],
  ['concrete-final-replay-make', () => makeConcreteFinalAcceptanceReplay0()],
  ['concrete-final-replay-check', () => CheckConcreteFinalAcceptanceReplay0()],
  ['concrete-final-replay-write', () => writeConcreteFinalAcceptanceReplayFiles0()],
  ['final-pnp-certificate-make', () => makeFinalPNPCertificate0()],
  ['final-pnp-certificate-record', () => makeFinalPNPCertificateRecord0()],
  ['final-pnp-certificate-check', () => CheckFinalPNPCertificate0()],
  ['final-pnp-certificate-write', () => writeFinalPNPCertificateFiles0()],
  ['final-pnp-release-gate-make', () => makeFinalPNPReleaseGate0()],
  ['final-pnp-release-gate-check', () => CheckFinalPNPReleaseGate0()],
  ['final-pnp-release-gate-write', () => writeFinalPNPReleaseGateFiles0()],
  ['final-pnp-proof-report-make', () => makeFinalPNPProofReport0()],
  ['final-pnp-proof-report-record', () => makeFinalPNPProofReportRecord0()],
  ['final-pnp-proof-report-check', () => CheckFinalPNPProofReport0()],
  ['final-pnp-proof-report-write', () => writeFinalPNPProofReportFiles0()],
  ['concrete-materialized-accept-run-make', () => makeConcreteMaterializedGeneratedAcceptRun0()],
  ['concrete-materialized-accept-run-check', () => CheckConcreteMaterializedGeneratedAcceptRun0()],
  ['concrete-materialized-accept-run-write', () => writeConcreteMaterializedGeneratedAcceptRunFiles0()],
  ['concrete-final-certificate-make', () => makeConcreteMaterializedFinalCertificate0()],
  ['concrete-final-certificate-check', () => CheckConcreteMaterializedFinalCertificate0()],
  ['concrete-final-certificate-write', () => writeConcreteMaterializedFinalCertificateFiles0()],
  ['concrete-public-status-make', () => makeConcreteFinalCertificatePublicStatus0()],
  ['concrete-public-status-check', () => CheckConcreteFinalCertificatePublicStatus0()],
  ['concrete-public-status-write', () => writeConcreteFinalCertificatePublicStatusFiles0()],
  ['pnplabs-record-build', () => BuildPNPLabsRunRecord0()],
  ['pnplabs-current-bundle', () => BuildCurrentRunBundle0()],
  ['pnplabs-upload-files', () => WritePNPLabsUploadFiles0()],
  ['pnplabs-upload-issue', () => UploadPNPLabsIssue0()],
]);

const PACKAGE_GATED_COMMANDS = Object.freeze([
  'verify',
  'pnp:verify:upload',
  'proof:unrestricted-final-soundness-release',
  'proof:public-theorem-activation',
  'proof:activated-pnp-status',
  'proof:uniform-final-soundness-target',
  'proof:uniform-input-family',
  'proof:uniform-locked-nand-construction',
  'proof:uniform-locked-nand-threshold',
  'proof:uniform-residual-band-minimizer',
  'proof:uniform-zeroslack-closure',
  'proof:no-hidden-oracle-semantic',
  'proof:uniform-complexity-conclusion',
  'runall',
  'smoke',
  'smoke:full',
  'release:audit',
  'release:audit:full',
  'materialized:bridge',
  'materialized:bridge:full',
  'materialized:aggregate',
  'materialized:aggregate:full',
  'materialized:resolve-digest',
  'materialized:resolve-digest:full',
  'materialized:write-fixtures',
  'materialized:write-fixtures:full',
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
  'materialized:final-certificate-public-status',
  'materialized:final-certificate-public-status:full',
  'materialized:final-certificate',
  'materialized:final-certificate:full',
  'release:audit:final-certificate-gate',
  'release:audit:final-certificate-gate:full',
  'release:audit:concrete-final-certificate-gate',
  'release:audit:concrete-final-certificate-gate:full',
  'release:audit:concrete-release-appendix',
  'release:audit:concrete-release-appendix:full',
  'release:audit:concrete-final-acceptance-replay',
  'release:audit:concrete-final-acceptance-replay:full',
  'release:audit:final-pnp-certificate',
  'release:audit:final-pnp-certificate:full',
  'release:audit:final-pnp-release-gate',
  'release:audit:final-pnp-release-gate:full',
  'release:audit:final-pnp-proof-report',
  'release:audit:final-pnp-proof-report:full',
]);

export async function CheckFormalPublicSurface0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;
  try {
    const status = await CheckFormalReconstructionStatus0({ root, writeOutput: false });
    if (status.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.Status', ['status/FORMAL_RECONSTRUCTION_STATUS.json'], 'formal reconstruction status must accept', { dependency: status }));

    const packageJson = options.packageJsonOverride ?? await readJson0(root, 'package.json');
    if (packageJson.tag === 'reject') return write0(root, outputPath, writeOutput, packageJson);
    const pkg = packageJson.value ?? packageJson;
    if (pkg.private !== true) return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.PackagePrivate', ['package.json', 'private'], 'the legacy checker package must remain private'));
    if (pkg.scripts?.['pnp:verify'] !== 'node scripts/pnp-verify-all.mjs --json') return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.CurrentVerifyCommand', ['package.json', 'scripts', 'pnp:verify'], 'current verifier command mismatch'));
    for (const key of PACKAGE_GATED_COMMANDS) {
      const command = pkg.scripts?.[key];
      if (typeof command !== 'string') return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.LegacyCommandMissing', ['package.json', 'scripts', key], 'frozen legacy command is missing'));
      if (command.includes('--historical-replay')) return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.ImplicitHistoricalReplay', ['package.json', 'scripts', key], 'package commands must not silently opt into historical replay'));
    }

    const sourceDigests = [];
    for (const filePath of FORMAL_GATED_ENTRYPOINTS0) {
      const text = options.sourceOverrides?.[filePath] ?? await readFile(path.join(root, filePath), 'utf8');
      const executableText = stripComments0(text);
      if (!/\bEnforceHistoricalReplayCli0\s*\(\s*\{/u.test(executableText)) return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.MissingCliGate', [filePath], 'legacy CLI entrypoint must call the explicit historical replay gate'));
      sourceDigests.push({ path: filePath, sha256: sha2560(Buffer.from(text, 'utf8')) });
    }

    const defaultRejects = [];
    for (const [id, check] of DEFAULT_REJECT_CHECKERS) {
      const out = await check();
      if (
        out?.tag !== 'reject'
        || out.publicTheoremEmissionAllowed !== false
        || out.finalTheoremReady !== false
        || !String(out.coord ?? '').endsWith('.HistoricalReplayRequired')
      ) return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.DefaultCheckerRoute', [id], 'superseded checker must reject at the historical replay gate by default', { actual: out }));
      defaultRejects.push({ id, coord: out.coord });
    }

    const injectedPackageCheck = await CheckMaterializedCheckPCCPack0(
      makeMaterializedCheckPCCPackShell0(),
      {
        packageCheckRunner: async () => ({
          tag: 'accept',
          NF: {
            kind: 'PackSufficiency0NF',
            publicConclusion: {
              antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
              consequent: 'P = NP',
              conditional: true,
            },
          },
        }),
      },
    );
    if (
      injectedPackageCheck?.tag !== 'reject'
      || injectedPackageCheck.coord !== 'CheckMaterializedCheckPCCPack0.HistoricalReplayRequired'
    ) return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.InjectedPackageRunner', ['pcc-materialized-checkpack0.mjs'], 'injected accepting package runners must require historical replay', { actual: injectedPackageCheck }));

    let uploadFetchCalled = false;
    const frozenUpload = await UploadPNPLabsIssue0({
      historicalReplay: true,
      token: 'formal-surface-must-not-upload',
      fetchImpl: async () => {
        uploadFetchCalled = true;
        throw new Error('frozen upload route attempted network access');
      },
    });
    if (
      frozenUpload?.tag !== 'reject'
      || frozenUpload.coord !== 'PNPLabsUpload.FrozenDuringFormalReconstruction'
      || frozenUpload.publicTheoremEmissionAllowed !== false
      || frozenUpload.finalTheoremReady !== false
      || uploadFetchCalled
    ) return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.PNPLabsUploadFrozen', ['scripts/pnp-verify-and-upload.mjs'], 'PNP Labs upload must stay frozen even during historical replay', { actual: frozenUpload, uploadFetchCalled }));

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORDINATE,
      status: 'formal-reconstruction-public-surface',
      mathematicalTheoremEstablished: false,
      publicTheoremEmissionAllowed: false,
      publicTheoremStatement: null,
      publicTheoremConclusion: null,
      finalTheoremReady: false,
      legacyCliHistoricalReplayRequiresExplicitOptIn: true,
      legacyProgrammaticCheckerExportsAreCurrentAuthority: false,
      packagePrivate: true,
      gatedEntrypoints: [...FORMAL_GATED_ENTRYPOINTS0],
      gatedPackageCommands: [...PACKAGE_GATED_COMMANDS],
      defaultRejects,
      pnplabsUploadFrozen: true,
      sourceDigests,
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('FormalPublicSurface.UnhandledException', [], 'formal public surface checker threw', normalizeError0(error)));
  }
}

async function readJson0(root, filePath) {
  try {
    return { value: JSON.parse(await readFile(path.join(root, filePath), 'utf8')) };
  } catch (error) {
    return reject0('FormalPublicSurface.ReadOrParseFailed', [filePath], 'could not read or parse file', normalizeError0(error));
  }
}

async function write0(root, outputPath, enabled, verdict) {
  const rendered = { ...verdict, outputPath: enabled ? outputPath : null };
  if (enabled) {
    const absolute = path.join(root, outputPath);
    await mkdir(path.dirname(absolute), { recursive: true });
    await writeFile(absolute, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
}

function reject0(coord, pathArray, reason, witness = {}) {
  return {
    tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray,
    witness: { reason, ...witness }, mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false, publicTheoremStatement: null,
    publicTheoremConclusion: null, finalTheoremReady: false,
  };
}

function sha2560(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function stripComments0(source) { return source.replace(/\/\*[\s\S]*?\*\//gu, '').replace(/^\s*\/\/.*$/gmu, ''); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

async function main0() {
  const json = process.argv.includes('--json');
  const noWrite = process.argv.includes('--no-write');
  const unknown = process.argv.slice(2).filter((arg) => !['--json', '--no-write'].includes(arg));
  if (unknown.length !== 0) {
    console.error(JSON.stringify(reject0('FormalPublicSurface.CliBadArgument', [], 'unknown CLI argument', { unknown }), null, 2));
    process.exit(2);
  }
  const out = await CheckFormalPublicSurface0({ writeOutput: !noWrite });
  const rendered = JSON.stringify(out, null, 2);
  if (json || out.tag === 'accept') console.log(rendered); else console.error(rendered);
  process.exit(out.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
