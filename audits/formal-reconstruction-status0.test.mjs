import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckFormalReconstructionStatus0,
  FORMAL_RECONSTRUCTION_BLOCKERS0,
} from '../pcc-formal-reconstruction-status0.mjs';

async function currentStatus0() {
  return JSON.parse(await readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url), 'utf8'));
}

test('formal reconstruction status accepts the current source and public mirrors', async () => {
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-10-06');
  assert.equal(out.formalReconstructionStatusAccepted, true);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.internalFinalTheoremReady, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.satInPConclusionAccepted, false);
  assert.equal(out.pEqualsNPConclusionAccepted, false);
  assert.equal(out.leanToolchain, 'leanprover/lean4:v4.31.0');
  assert.equal(out.leanCompilerVersion, '4.31.0');
  assert.equal(out.leanCompilerCommit, '68218e876d2a38b1985b8590fff244a83c321783');
  assert.equal(out.lakeVersion, '5.0.0-src+68218e8');
  assert.equal(out.elanVersion, '4.2.3');
  assert.equal(out.elanReleaseCommit, 'b6cec7e10fe4965a605aaf60d1cb4a5837f0462b');
  assert.equal(out.elanArchiveSha256, 'df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2');
  assert.equal(out.leanBuildTarget, 'PNP');
  assert.equal(out.leanRootModule, 'PNP');
  assert.equal(out.leanRootStatusDeclaration, 'PNP.Main.rootTheoremStatus');
  assert.equal(out.leanBuildConfigurationPinned, true);
  assert.equal(out.explicitLeanRootTargetPresent, true);
  assert.equal(out.leanLibraryTargetBuilt, true);
  assert.equal(out.leanSourcePlaceholderAuditPassed, true);
  assert.equal(out.leanNANDDirectWireCoreFormalized, true);
  assert.equal(out.leanNANDDirectWireCoreAxiomAuditPassed, true);
  assert.equal(out.leanNANDEnumeratorFormalized, true);
  assert.equal(out.leanNANDEnumeratorAxiomAuditPassed, true);
  assert.equal(out.leanNANDExactWidthEnumerationComplete, true);
  assert.equal(out.leanNANDEnumeratorUsesOrderedGatePairs, true);
  assert.equal(out.leanNANDEnumeratorIncludesUniqueEmptyOutputTuple, true);
  assert.equal(out.leanNANDEnumeratorDeduplicated, false);
  assert.equal(out.leanNANDTruthTableFormalized, true);
  assert.equal(out.leanNANDTruthTableAxiomAuditPassed, true);
  assert.equal(out.leanNANDSemanticEquivalenceDecidable, true);
  assert.equal(out.leanNANDMinimumAndSlackFormalized, true);
  assert.equal(out.leanNANDReferenceMinimumFormalized, true);
  assert.equal(out.leanNANDReferenceMinimumAxiomAuditPassed, true);
  assert.equal(out.leanNANDReferenceMinimumExhaustive, true);
  assert.equal(out.leanNANDReferenceMinimumScope, 'finite-boolean-direct-wire-empty-profile');
  assert.equal(out.leanNANDReferenceMinimumPolynomialRuntimeProved, false);
  assert.equal(out.leanNANDResidualSlackZeroIffMinimumFormalized, true);
  assert.equal(out.leanNANDCompositionFormalized, true);
  assert.equal(out.leanNANDCompositionAxiomAuditPassed, true);
  assert.equal(out.leanNANDFramedReplacementFormalized, true);
  assert.equal(out.leanNANDFramedGlobalSlackLawFormalized, true);
  assert.equal(out.leanNANDFramedSlackAxiomAuditPassed, true);
  assert.equal(out.leanNANDReplacementScope, 'concrete-serial-framed-context');
  assert.equal(out.leanCompatibleReplacementFormalized, false);
  assert.equal(out.leanGlobalSlackLawFormalized, false);
  assert.equal(out.leanLockedNANDBuilderFormalized, false);
  assert.equal(out.leanLockedNANDThresholdFormalized, false);
  assert.equal(out.rootLeanTheoremPresent, false);
  assert.equal(out.rootLeanTheoremBuilt, false);
  assert.equal(out.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(out.projectSpecificAxiomsRemaining, true);
  assert.deepEqual(out.projectSpecificAxiomInventory, [
    'PNP.SAT',
    'PNP.LockedNANDThreshold',
    'PNP.ResidualBandExactMinimization',
    'PNP.GeneratePCCPack',
    'PNP.CheckPCCPackexp',
  ]);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.deepEqual(out.remainingBlockers, FORMAL_RECONSTRUCTION_BLOCKERS0);
  assert.equal(out.remainingBlockers.length, 7);
  assert.equal(out.remainingBlockers.includes('Formal.PinnedLeanBuildAndRootTarget'), false);
  assert.match(out.statusSha256, /^[0-9a-f]{64}$/u);
  assert.match(out.siteStatusSha256, /^[0-9a-f]{64}$/u);
});

test('formal status records the exhaustive direct-wire reference minimum conservatively', async () => {
  const status = await currentStatus0();

  assert.equal(status.publicSurfaceBaselineCoordinate, 'PUBLIC-SURFACE-BASELINE-2026-07-10-NAND-REFERENCE-MINIMUM-06');
  assert.equal(status.leanNANDDirectWireCoreFormalized, true);
  assert.equal(status.leanNANDDirectWireCoreAxiomAuditPassed, true);
  assert.equal(status.leanNANDEnumeratorFormalized, true);
  assert.equal(status.leanNANDEnumeratorAxiomAuditPassed, true);
  assert.equal(status.leanNANDExactWidthEnumerationComplete, true);
  assert.equal(status.leanNANDEnumeratorUsesOrderedGatePairs, true);
  assert.equal(status.leanNANDEnumeratorIncludesUniqueEmptyOutputTuple, true);
  assert.equal(status.leanNANDEnumeratorDeduplicated, false);
  assert.equal(status.leanNANDTruthTableFormalized, true);
  assert.equal(status.leanNANDTruthTableAxiomAuditPassed, true);
  assert.equal(status.leanNANDSemanticEquivalenceDecidable, true);
  assert.equal(status.leanNANDMinimumAndSlackFormalized, true);
  assert.equal(status.leanNANDReferenceMinimumFormalized, true);
  assert.equal(status.leanNANDReferenceMinimumAxiomAuditPassed, true);
  assert.equal(status.leanNANDReferenceMinimumExhaustive, true);
  assert.equal(status.leanNANDReferenceMinimumScope, 'finite-boolean-direct-wire-empty-profile');
  assert.equal(status.leanNANDReferenceMinimumPolynomialRuntimeProved, false);
  assert.equal(status.leanNANDResidualSlackZeroIffMinimumFormalized, true);
  assert.equal(status.leanNANDCompositionFormalized, true);
  assert.equal(status.leanNANDCompositionAxiomAuditPassed, true);
  assert.equal(status.leanNANDFramedReplacementFormalized, true);
  assert.equal(status.leanNANDFramedGlobalSlackLawFormalized, true);
  assert.equal(status.leanNANDFramedSlackAxiomAuditPassed, true);
  assert.equal(status.leanNANDReplacementScope, 'concrete-serial-framed-context');
  assert.equal(status.leanCompatibleReplacementFormalized, false);
  assert.equal(status.leanGlobalSlackLawFormalized, false);
  assert.equal(status.leanLockedNANDBuilderFormalized, false);
  assert.equal(status.leanLockedNANDThresholdFormalized, false);
  assert.equal(status.nonClaims.some((entry) => entry.includes('direct-wire NAND semantics layer does not by itself prove enumeration')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('reference-minimum computation has no polynomial-runtime claim')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('concrete serial framed-context construction')), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-semantics0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-enumerator0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-reference-minimum0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDTruthTableAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDCompositionAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean'), true);
  assert.equal(status.remainingBlockers.includes('Formal.LockedNANDThreshold'), true);
});

test('formal status records a pinned Lean library root without claiming a root theorem', async () => {
  const status = await currentStatus0();

  assert.equal(status.leanToolchain, 'leanprover/lean4:v4.31.0');
  assert.equal(status.leanBuildTarget, 'PNP');
  assert.equal(status.leanRootModule, 'PNP');
  assert.equal(status.leanRootStatusDeclaration, 'PNP.Main.rootTheoremStatus');
  assert.equal(status.leanBuildConfigurationPinned, true);
  assert.equal(status.explicitLeanRootTargetPresent, true);
  assert.equal(status.leanLibraryTargetBuilt, true);
  assert.equal(status.leanSourcePlaceholderAuditPassed, true);
  assert.equal(status.rootLeanTheorem, 'PNP.Main.p_eq_np');
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.rootLeanTheoremBuilt, false);
  assert.equal(status.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(status.projectSpecificAxiomsRemaining, true);
  assert.equal(status.sorryOrAdmitInRootDependencyClosure, null);
  assert.equal(status.nonClaims.some((entry) => entry.includes('root-status build is reconstruction data')), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-root-target0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake build PNP'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean'), true);
});

test('formal status separates current-authority and historical replay workflows', async () => {
  const status = await currentStatus0();
  const names = (await readdir(new URL('../.github/workflows/', import.meta.url)))
    .filter((name) => name.endsWith('.yml'))
    .sort()
    .map((name) => `.github/workflows/${name}`);

  assert.deepEqual([
    ...status.activeCoreWorkflows,
    ...status.historicalReplayWorkflows,
  ].sort(), names);
  assert.deepEqual(status.historicalReplayWorkflows, ['.github/workflows/legacy-v0-replay.yml']);
  assert.equal(status.activeCoreWorkflows.includes('.github/workflows/legacy-v0-replay.yml'), false);
});

test('formal status designates only the pinned legacy-v0 archive replay', async () => {
  const status = await currentStatus0();
  assert.equal(status.legacyCheckerArchiveManifest, 'archive/legacy-v0/ARCHIVE.json');
  assert.equal(status.legacyCheckerArchiveCheckCommand, 'npm run legacy:v0:check');
  assert.equal(status.legacyCheckerReplayCommand, 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d');
  assert.equal(status.nonClaims.some((entry) => entry.includes('neither current theorem authority nor a mathematical proof')), true);
});

test('formal reconstruction status rejects theorem emission activation', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowed = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'publicTheoremEmissionAllowed']);
});

test('formal reconstruction status rejects an unearned root theorem', async () => {
  const status = await currentStatus0();
  status.rootLeanTheoremPresent = true;
  status.rootLeanTheoremBuilt = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'rootLeanTheoremPresent']);
});

test('formal reconstruction status rejects a drifting Lean toolchain pin', async () => {
  const status = await currentStatus0();
  status.leanToolchain = 'leanprover/lean4:stable';
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'leanToolchain']);
});

test('formal reconstruction status rejects a disabled Lean placeholder audit', async () => {
  const status = await currentStatus0();
  status.leanSourcePlaceholderAuditPassed = false;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'leanSourcePlaceholderAuditPassed']);
});

test('formal reconstruction status rejects disabling the audited direct-wire NAND core', async () => {
  const status = await currentStatus0();
  status.leanNANDDirectWireCoreAxiomAuditPassed = false;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'leanNANDDirectWireCoreAxiomAuditPassed']);
});

test('formal reconstruction status rejects disabling an earned NAND enumerator property', async () => {
  const fields = [
    'leanNANDEnumeratorFormalized',
    'leanNANDEnumeratorAxiomAuditPassed',
    'leanNANDExactWidthEnumerationComplete',
    'leanNANDEnumeratorUsesOrderedGatePairs',
    'leanNANDEnumeratorIncludesUniqueEmptyOutputTuple',
    'leanNANDTruthTableFormalized',
    'leanNANDTruthTableAxiomAuditPassed',
    'leanNANDSemanticEquivalenceDecidable',
    'leanNANDMinimumAndSlackFormalized',
    'leanNANDReferenceMinimumFormalized',
    'leanNANDReferenceMinimumAxiomAuditPassed',
    'leanNANDReferenceMinimumExhaustive',
    'leanNANDResidualSlackZeroIffMinimumFormalized',
    'leanNANDCompositionFormalized',
    'leanNANDCompositionAxiomAuditPassed',
    'leanNANDFramedReplacementFormalized',
    'leanNANDFramedGlobalSlackLawFormalized',
    'leanNANDFramedSlackAxiomAuditPassed',
  ];

  for (const field of fields) {
    const status = await currentStatus0();
    status[field] = false;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.equal(out.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects unearned broad downstream NAND claims', async () => {
  const fields = [
    'leanNANDEnumeratorDeduplicated',
    'leanNANDReferenceMinimumPolynomialRuntimeProved',
    'leanCompatibleReplacementFormalized',
    'leanGlobalSlackLawFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
  ];

  for (const field of fields) {
    const status = await currentStatus0();
    status[field] = true;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.equal(out.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects removing the locked NAND threshold blocker', async () => {
  const status = await currentStatus0();
  status.remainingBlockers = status.remainingBlockers.filter((entry) => entry !== 'Formal.LockedNANDThreshold');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Blockers');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'remainingBlockers']);
});

test('formal reconstruction status rejects a hidden project-specific axiom', async () => {
  const status = await currentStatus0();
  status.projectSpecificAxiomInventory = status.projectSpecificAxiomInventory.slice(0, -1);
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.ProjectSpecificAxiomInventory');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'projectSpecificAxiomInventory']);
});

test('formal reconstruction status rejects external review as a theorem premise', async () => {
  const status = await currentStatus0();
  status.externalReviewIsMathematicalPremise = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'externalReviewIsMathematicalPremise']);
});

test('formal reconstruction status rejects hidden formal blockers', async () => {
  const status = await currentStatus0();
  status.remainingBlockers = [];
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Blockers');
});

test('formal reconstruction status rejects a drifting public mirror', async () => {
  const status = await currentStatus0();
  const site = { ...status, nonClaims: [...status.nonClaims, 'drift'] };
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: site });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.NonClaims');
  assert.deepEqual(out.path, ['public/pnp-status.json', 'nonClaims']);
});

test('formal reconstruction status rejects formatting-only public mirror drift', async () => {
  const status = await currentStatus0();
  const statusText = `${JSON.stringify(status, null, 2)}\n`;
  const siteText = JSON.stringify(status);
  const out = await CheckFormalReconstructionStatus0({
    writeOutput: false,
    statusBytesOverride: statusText,
    siteBytesOverride: siteText,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.SiteMirrorMismatch');
  assert.deepEqual(out.path, ['public/pnp-status.json']);
});

test('formal reconstruction status rejects unknown theorem authority fields', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowedByLegacyRoute = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Keys');
  assert.deepEqual(out.witness.extraKeys, ['publicTheoremEmissionAllowedByLegacyRoute']);
});

test('formal reconstruction status rejects reintroduced upload commands', async () => {
  const status = await currentStatus0();
  status.verificationCommands.push('npm run pnp:verify:upload');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Commands');
});

test('formal reconstruction status rejects contradictory non-claims', async () => {
  const status = await currentStatus0();
  status.nonClaims.push('P = NP is established by another route.');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.NonClaims');
});
