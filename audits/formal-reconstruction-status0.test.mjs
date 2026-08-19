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
  const [out, status] = await Promise.all([
    CheckFormalReconstructionStatus0({ writeOutput: false }),
    currentStatus0(),
  ]);
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, status.coordinate);
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
  assert.equal(out.leanConcreteCNFVerifierCorrectnessFormalized, true);
  assert.equal(out.leanConcreteCNFVerifierNoTimeoutFormalized, true);
  assert.equal(out.leanConcreteCNFVerifierAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCNFWorkAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCNFWorkAuditedDeclarationCount, 766);
  assert.equal(out.leanConcreteCNFSATMembershipFormalized, true);
  assert.equal(out.leanConcreteCNFSATMembershipTheorem,
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP');
  assert.equal(out.leanConcreteCNFProofScope,
    'direct-finite-machine-verifier-correctness-and-np-membership-only');
  assert.equal(out.leanConcreteCNFSATInPFormalized, false);
  assert.equal(out.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthAuditedDeclarationCount, 39);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthMalformedInternalInputTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputLengthConnectedToTotalInputFramerEndpointFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixAuditedDeclarationCount, 40);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixMalformedScanSymbolTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixLiteralFramerLaunchFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderAuditedDeclarationCount, 68);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderAllTokensExactFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderFirstFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderMalformedPhaseTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderTokenAppenderInputPrefixComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixAuditedDeclarationCount, 37);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstTokenPrefixMalformedPhaseTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderUnaryPolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderUnaryPolynomialAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderUnaryPolynomialAuditedDeclarationCount, 74);
  assert.equal(out.leanConcreteCookLevinBuilderUnaryPolynomialCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderUnaryPolynomialExactRuntimePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderAuditedDeclarationCount, 84);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderCompleteHeaderFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixAuditedDeclarationCount, 60);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixRetainedNextTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderBodyStartPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixAuditedDeclarationCount, 74);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixRetainedNextTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixAuditedDeclarationCount, 79);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixRetainedNextTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePrefixCompleteFirstClauseFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepAuditedDeclarationCount, 47);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepDirectPaddingOutcomeFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicTokenCursorStepSinglePaddingStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunAuditedDeclarationCount, 84);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunRemainingPaddingCountFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunDirectPaddingBlockFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunSecondClauseStartFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunNoEmissionSpecificationFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstClausePaddingRunFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepSecondClauseSeparatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSeparatorStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixAuditedDeclarationCount, 87);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixCompleteFirstNegativeLiteralFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAuditedDeclarationCount, 115);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixCompleteSecondNegativeLiteralFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixAuditedDeclarationCount, 57);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixCompleteSecondClauseFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixClauseTerminatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixRetainedFirstPaddingCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunAuditedDeclarationCount, 68);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunRemainingPaddingCountFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunDirectPaddingBlockFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunThirdClauseStartFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunNoEmissionSpecificationFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondClausePaddingRunFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepThirdClauseSeparatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSeparatorStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixAuditedDeclarationCount, 87);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixCompleteFirstNegativeLiteralFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixAuditedDeclarationCount, 145);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixCompleteSecondNegativeLiteralFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixRetainedClauseTerminatorCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixAuditedDeclarationCount, 57);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixCompleteThirdClauseFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixClauseTerminatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixRetainedFirstPaddingCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunAuditedDeclarationCount, 68);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunRemainingPaddingCountFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunDirectPaddingBlockFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunFourthClauseStartFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunNoEmissionSpecificationFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderThirdClausePaddingRunFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepFourthClauseSeparatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSeparatorStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixAuditedDeclarationCount, 115);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixCompleteFirstNegativeLiteralFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixAuditedDeclarationCount, 147);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixCompleteSecondNegativeLiteralFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixAuditedDeclarationCount, 57);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixCompleteFourthClauseFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePrefixFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunAuditedDeclarationCount, 68);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunRemainingPaddingCountFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunDirectPaddingBlockFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunFifthClauseSlotStartFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunNoEmissionSpecificationFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFourthClausePaddingRunFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunAuditedDeclarationCount, 68);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunPaddingCountFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunDirectPaddingBlockFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunSixthClauseSlotStartFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunNoEmissionSpecificationFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFifthClausePaddingRunFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunAuditedDeclarationCount, 68);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunPaddingCountFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunDirectPaddingBlockFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunSecondConstraintSeparatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunNoEmissionSpecificationFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderFirstConstraintPaddingRunFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepSecondConstraintSeparatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeparatorStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepSecondConstraintFirstLiteralSignFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepSecondConstraintFirstLiteralFirstUnaryUnitFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepSecondConstraintFirstLiteralSecondUnaryUnitFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepSecondConstraintFirstLiteralThirdUnaryUnitFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepAuditedDeclarationCount, 56);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepSecondConstraintFirstLiteralTerminatorFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepSecondConstraintFirstLiteralSuccessorTokenFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepPaddingOrUnaryOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepInputPrefixOptionalAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepSecondPaddingOrUnaryOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepInputPrefixOptionalAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepThirdPaddingOrUnaryOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepInputPrefixOptionalAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepFourthPaddingOrUnaryOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepInputPrefixOptionalAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepFifthPaddingOrTerminatorOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepInputPrefixOptionalTerminatorAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepSixthPaddingOrOpeningUnaryOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepInputPrefixOptionalAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepAxiomAuditPassed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepAuditedDeclarationCount, 82);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepCompiledRawMachineFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepExactFormulaBitsFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepSeventhPaddingOrUnaryOpportunityFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepRetainedAdvancedTokenCoordinateFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepInputPrefixOptionalAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepFailClosedBoundaryTimeoutFormalized, true);
  assert.equal(out.leanConcreteCookLevinBuilderInputPrefixAppenderComposed, true);
  assert.equal(out.leanConcreteCookLevinBuilderDynamicCursorFormalized, false);
  assert.equal(out.leanConcreteCookLevinFormulaBuilderFormalized, false);
  assert.equal(out.leanConcreteCookLevinBuilderRawRefinementFormalized, false);
  assert.equal(out.leanConcreteCookLevinBuilderPolynomialReductionFormalized, false);
  assert.equal(out.leanConcretePipelineStateNamespaceFormalized, true);
  assert.equal(out.leanConcretePipelineStateNamespaceAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineStateNamespaceAuditedDeclarationCount, 39);
  assert.equal(out.leanConcretePipelineSequentialNamespaceFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialNamespaceAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineSequentialNamespaceAuditedDeclarationCount, 26);
  assert.equal(out.leanConcretePipelineSequentialCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialCompilerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineSequentialCompilerAuditedDeclarationCount, 31);
  assert.equal(out.leanConcretePipelineSequentialVerdictAndOutputPreservationFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialExternalInputSizePolynomialFormalized, true);
  assert.equal(out.leanConcretePipelineSequentialStuckFirstTimeoutFormalized, true);
  assert.equal(out.leanConcretePipelineRuleTableCompositionFormalized, true);
  assert.equal(out.leanConcretePipelineStageBridgesFormalized, true);
  assert.equal(out.leanConcretePipelineStageBridgesAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineStageBridgesAuditedDeclarationCount, 56);
  assert.equal(out.leanConcretePipelineStageLaunchFormalized, true);
  assert.equal(out.leanConcretePipelineVerdictPreservationFormalized, true);
  assert.equal(out.leanConcretePipelineInternalOutputHandoffComposed, true);
  assert.equal(out.leanConcretePipelineTerminalOutputPackingFormalized, true);
  assert.equal(out.leanConcretePipelineTerminalOutputPackerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineTerminalOutputPackerAuditedDeclarationCount, 69);
  assert.equal(out.leanConcretePipelineTerminalOutputPackerConnectedToBridgeEndpointFormalized, true);
  assert.equal(out.leanConcretePipelineTerminalBridgeAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineTerminalBridgeAuditedDeclarationCount, 59);
  assert.equal(out.leanConcretePipelinePriorTraceTransportToTerminalBridgeFormalized, true);
  assert.equal(out.leanConcretePipelinePairedCompilerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelinePairedCompilerAuditedDeclarationCount, 28);
  assert.equal(out.leanConcretePipelineCanonicalPairCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineCompilerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineCompilerAuditedDeclarationCount, 29);
  assert.equal(out.leanConcretePipelineAllInputCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineInputFramerAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineInputFramerAuditedDeclarationCount, 70);
  assert.equal(out.leanConcretePipelineAllInputFramingFormalized, true);
  assert.equal(out.leanConcretePipelineMalformedInputBehaviorFormalized, true);
  assert.equal(out.leanConcretePipelineRawRefinementFormalized, true);
  assert.equal(out.leanConcretePipelineRefinementAxiomAuditPassed, true);
  assert.equal(out.leanConcretePipelineRefinementAuditedDeclarationCount, 16);
  assert.equal(out.leanConcreteFunctionProgramRecursiveCompilationFormalized, true);
  assert.equal(out.leanConcreteDecisionProgramRecursiveCompilationFormalized, true);
  assert.equal(out.leanConcretePolynomialTimeDeciderRawCompilationFormalized, true);
  assert.equal(out.leanConcretePipelineExternalInputSizePolynomialFormalized, true);
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
  assert.equal(out.leanLockedNANDDirectCandidatesFormalized, true);
  assert.equal(out.leanLockedNANDDirectAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDInternalMacroConstantsAbsent, true);
  assert.equal(out.leanDirectWireOutputLowerBoundFormalized, true);
  assert.equal(out.leanDirectWireBaselineAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDSourceDerivedCountsFormalized, true);
  assert.equal(out.leanLockedNANDBaselineAccountingFormalized, true);
  assert.equal(out.leanLockedNANDBaselineAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDConditionalSquareBaselineExactnessFormalized, true);
  assert.equal(out.leanLockedNANDLocalBaselineConditionsFormalized, true);
  assert.equal(out.leanLockedNANDLocalSquareBaselineExactnessFormalized, true);
  assert.equal(out.leanLockedNANDLocalBaselineAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDProofScope, 'typed-local-macros-source-derived-counts-and-five-local-square-baselines');
  assert.equal(out.leanLockedNANDConditionalThresholdBoundaryFormalized, true);
  assert.equal(out.leanLockedNANDConditionalResidualSlackAtMostFourFormalized, true);
  assert.equal(out.leanLockedNANDThresholdBoundaryAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDThresholdBoundaryScope, 'proof-bearing-typed-candidate-and-semantic-premises-only');
  assert.equal(out.leanLockedNANDThresholdBoundaryPremisesInstantiated, true);
  assert.equal(out.leanLockedNANDGlobalBaselineDistinctFormalized, true);
  assert.equal(out.leanLockedNANDGlobalBaselineDistinctAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDGlobalBaselineDistinctAuditedDeclarationCount, 5);
  assert.equal(out.leanLockedNANDGlobalBaselineDistinctScope,
    'arbitrary-finite-topological-nand-circuits-global-baseline-output-conditions-and-exact-reference-minimum');
  assert.equal(out.leanLockedNANDUnsatisfiableFinalZeroFormalized, true);
  assert.equal(out.leanLockedNANDUnsatisfiableFinalZeroAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDUnsatisfiableFinalZeroAuditedDeclarationCount, 2);
  assert.equal(out.leanLockedNANDUnsatisfiableFinalZeroScope,
    'arbitrary-finite-topological-nand-circuits-whole-carrier-unsatisfiable-final-zero-and-exact-reference-minimum');
  assert.equal(out.leanLockedNANDCarrierLayoutFormalized, true);
  assert.equal(out.leanLockedNANDTraceEquivalenceFormalized, true);
  assert.equal(out.leanLockedNANDCarrierTraceAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDCarrierTraceAuditedDeclarationCount, 71);
  assert.equal(out.leanLockedNANDCarrierTraceScope,
    'arbitrary-finite-topological-nand-circuits-carrier-separation-and-trace-equivalence');
  assert.equal(out.leanLockedNANDGlobalCandidateAssemblyFormalized, true);
  assert.equal(out.leanLockedNANDGlobalBaselineCandidateFormalized, true);
  assert.equal(out.leanLockedNANDFullCandidateFormalized, true);
  assert.equal(out.leanLockedNANDGlobalCandidateAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDGlobalCandidateAuditedDeclarationCount, 71);
  assert.equal(out.leanLockedNANDGlobalCandidateScope,
    'arbitrary-finite-topological-nand-circuits-exact-baseline-and-four-gate-extension');
  assert.equal(out.leanLockedNANDDerivedFinalOutputLawsFormalized, true);
  assert.equal(out.leanLockedNANDResidualSlackAtMostFourFormalized, true);
  assert.equal(out.leanLockedNANDSatisfiableFinalConditionsFormalized, true);
  assert.equal(out.leanLockedNANDGlobalSemanticThresholdFormalized, true);
  assert.equal(out.leanLockedNANDGlobalSemanticThresholdAxiomAuditPassed, true);
  assert.equal(out.leanLockedNANDGlobalSemanticThresholdAuditedDeclarationCount, 8);
  assert.equal(out.leanLockedNANDGlobalSemanticThresholdScope,
    'arbitrary-finite-topological-nand-circuits-complete-six-field-premises-and-typed-semantic-threshold');
  for (const field of [
    'leanConcreteLockedNANDCanonicalEncodingFormalized',
    'leanConcreteLockedNANDNormalizationSemanticsFormalized',
    'leanConcreteLockedNANDCompleteCandidateCodecFormalized',
    'leanConcreteLockedNANDEncodedSemanticReductionFormalized',
    'leanConcreteLockedNANDEncodedSemanticReductionAxiomAuditPassed',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanConcreteLockedNANDEncodedSemanticReductionAuditedDeclarationCount,
    48,
  );
  assert.equal(
    out.leanConcreteLockedNANDEncodedSemanticReductionScope,
    'strict-version-zero-codec-direct-normalization-semantics-complete-candidate-bytes-and-fail-closed-semantic-reduction',
  );
  for (const field of [
    'leanConcreteLockedNANDParserMachineFormalized',
    'leanConcreteLockedNANDParserAxiomAuditPassed',
    'leanConcreteLockedNANDParserAllInputExactFormalized',
    'leanConcreteLockedNANDParserExactOutputFormalized',
    'leanConcreteLockedNANDParserCompiledNonTimeoutFormalized',
    'leanConcreteLockedNANDParserPolynomialTimeMachineFormalized',
    'leanConcreteLockedNANDParserPolynomialTimeFunctionFormalized',
    'leanConcreteLockedNANDParserRawRefinementFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(out.leanConcreteLockedNANDParserAuditedDeclarationCount, 380);
  assert.equal(
    out.leanConcreteLockedNANDParserScope,
    'literal-228-state-2052-rule-strict-version-zero-all-input-parser-byte-preserving-or-empty-with-compiled-cubic-bound',
  );
  for (const field of [
    'leanConcreteLockedNANDEmitterMachineFormalized',
    'leanConcreteLockedNANDEmitterAxiomAuditPassed',
    'leanConcreteLockedNANDEmitterAllInputExactFormalized',
    'leanConcreteLockedNANDEmitterExactTargetBytesFormalized',
    'leanConcreteLockedNANDEmitterCompiledNonTimeoutFormalized',
    'leanConcreteLockedNANDEmitterPolynomialTimeMachineFormalized',
    'leanConcreteLockedNANDEmitterPolynomialTimeFunctionFormalized',
    'leanConcreteLockedNANDEmitterRawRefinementFormalized',
    'leanConcreteLockedNANDEmitterStrictParserCompositionFormalized',
    'leanConcreteLockedNANDEmitterOutputSizeBoundFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(out.leanConcreteLockedNANDEmitterAuditedDeclarationCount, 3295);
  assert.equal(
    out.leanConcreteLockedNANDEmitterScope,
    'literal-1387921-rule-grammar-only-all-input-target-emitter-with-strict-parser-composition-polynomial-bounds-and-recursive-raw-refinement',
  );
  for (const field of [
    'leanConcreteLockedNANDPolynomialReductionFormalized',
    'leanConcreteLockedNANDPolynomialReductionAxiomAuditPassed',
    'leanConcreteLockedNANDPolynomialReductionExactFunctionFormalized',
    'leanConcreteLockedNANDPolynomialReductionExactOutputFormalized',
    'leanConcreteLockedNANDPolynomialReductionLanguageEquivalenceFormalized',
    'leanConcreteLockedNANDPolynomialReductionWitnessFormalized',
    'leanConcreteLockedNANDPolynomialReductionRawRefinementFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanConcreteLockedNANDPolynomialReductionAuditedDeclarationCount,
    16,
  );
  assert.equal(
    out.leanConcreteLockedNANDPolynomialReductionScope,
    'strict-version-zero-parser-emitter-polynomial-reduction-with-exact-language-equivalence-and-recursive-raw-refinement',
  );
  for (const field of [
    'leanConcreteCNFToNANDSemanticCompilerFormalized',
    'leanConcreteCNFToNANDSemanticCompilerAxiomAuditPassed',
    'leanConcreteCNFToNANDExactCodecCanonicalityFormalized',
    'leanConcreteCNFToNANDTypedTopologicalCompilationFormalized',
    'leanConcreteCNFToNANDWellFormedOutputFormalized',
    'leanConcreteCNFToNANDExactSemanticsFormalized',
    'leanConcreteCNFToNANDEdgeSemanticsFormalized',
    'leanConcreteCNFToNANDExactGateCountFormalized',
    'leanConcreteCNFToNANDPolynomialOutputSizeBoundFormalized',
    'leanConcreteCNFToNANDAllBitstringFailClosedFormalized',
    'leanConcreteCNFToNANDLockedThresholdCompositionFormalized',
    'leanConcreteCNFToNANDFiniteMachineFormalized',
    'leanConcreteCNFToNANDPolynomialTimeFunctionFormalized',
    'leanConcreteCNFToNANDPolynomialReductionFormalized',
    'leanConcreteCNFToNANDPolynomialReductionAxiomAuditPassed',
    'leanConcreteCNFToNANDAllInputExactFormalized',
    'leanConcreteCNFToNANDExactMachineOutputFormalized',
    'leanConcreteCNFToNANDCompiledNonTimeoutFormalized',
    'leanConcreteCNFToNANDRawRefinementFormalized',
    'leanConcreteCNFToNANDDirectReductionFormalized',
    'leanConcreteCNFToNANDLockedReductionCompositionFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanConcreteCNFToNANDSemanticCompilerAuditedDeclarationCount,
    68,
  );
  assert.equal(
    out.leanConcreteCNFToNANDPolynomialReductionAuditedDeclarationCount,
    1316,
  );
  assert.equal(
    out.leanConcreteCNFToNANDSemanticCompilerScope,
    'strict-canonical-cnf-to-intrinsically-topological-nand-semantic-compiler-with-exact-gate-count-quadratic-output-bound-and-all-bitstring-fail-closed-equivalence',
  );
  assert.equal(
    out.leanConcreteCNFToNANDPolynomialReductionScope,
    'fixed-135070-rule-three-node-all-bitstring-cnf-to-nand-compiler-with-exact-output-polynomial-time-function-direct-reduction-locked-threshold-composition-and-recursive-raw-refinement',
  );
  assert.equal(out.leanLockedNANDPolynomialBuilderFormalized, true);
  assert.equal(out.leanCompatibleReplacementFormalized, false);
  assert.equal(out.leanGlobalSlackLawFormalized, false);
  assert.equal(out.leanLockedNANDBuilderFormalized, true);
  assert.equal(out.leanLockedNANDThresholdFormalized, true);
  for (const field of [
    'leanResidualRoutesListedGainScanFormalized',
    'leanResidualRoutesAxiomAuditPassed',
    'leanResidualRoutesGainSoundnessFormalized',
    'leanResidualRoutesStrictResidualDescentFormalized',
    'leanResidualRoutesExactResultProofBearing',
    'leanResidualRoutesZeroSlackResultProofBearing',
    'leanResidualRoutesUnresolvedFailClosed',
  ]) assert.equal(out[field], true, field);
  assert.equal(out.leanResidualRoutesScope, 'explicit-caller-supplied-finite-candidate-list');
  for (const field of [
    'leanResidualGainChainVerifierFormalized',
    'leanResidualGainChainAxiomAuditPassed',
    'leanResidualGainChainSemanticInvariantFormalized',
    'leanResidualGainChainSlackIterationBoundFormalized',
    'leanLockedNANDGainIterationsAtMostFourFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualGainChainScope,
    'all-finite-proof-bearing-or-executably-verified-strict-equivalent-gain-chains-with-locked-family-four-step-specialization',
  );
  for (const field of [
    'leanResidualGainStoppingSpecificationFormalized',
    'leanResidualGainStoppingAxiomAuditPassed',
    'leanResidualGainReferenceMinimumWitnessFormalized',
    'leanResidualGainPositiveIffGlobalStrictGainFormalized',
    'leanResidualGainZeroIffGlobalNoStrictGainFormalized',
    'leanResidualGainSemanticMinimumIffGlobalNoStrictGainFormalized',
    'leanResidualGainChainGlobalStoppingConsequenceFormalized',
    'leanResidualGainChainExactMinimumPackagingFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualGainStoppingScope,
    'all-finite-direct-wire-implementations-with-global-strict-equivalent-gain-quantification-and-proof-supplied-chain-endpoint-stopping',
  );
  for (const field of [
    'leanResidualTerminalFullBridgeFormalized',
    'leanResidualTerminalFullBridgeAxiomAuditPassed',
    'leanResidualTerminalizationExactFormalized',
    'leanResidualTerminalFullMinimumSpecificationFormalized',
    'leanResidualTerminalMuBridgeFormalized',
    'leanResidualWholeSpanPositiveWitnessIffFormalized',
    'leanResidualWholeSpanStrictDescentFormalized',
    'leanResidualWholeSpanZeroAbsenceIffFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualTerminalFullBridgeScope,
    'all-finite-direct-wire-implementations-with-complete-multi-output-semantics-and-exhaustive-reference-minimum-witnesses',
  );
  for (const field of [
    'leanResidualTerminalQuotientCarrierFormalized',
    'leanResidualTerminalModeFirewallFormalized',
    'leanResidualTerminalModeFirewallAxiomAuditPassed',
    'leanResidualTerminalProfileProjectionExactFormalized',
    'leanResidualTerminalCheckedFullLiftFormalized',
    'leanResidualTerminalQuotientEqualityNotConstructiveFormalized',
    'leanResidualTerminalObligationDischargePreservedFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualTerminalModeFirewallScope,
    'all-finite-direct-wire-implementations-with-computed-finite-profile-observers-and-explicit-forgetful-projections',
  );
  for (const field of [
    'leanResidualProjectionMinimumFormalized',
    'leanResidualProjectionMinimumAxiomAuditPassed',
    'leanResidualProjectionMinimumExecutableFullScanFormalized',
    'leanResidualProjectionMinimumExecutableQuotientScanFormalized',
    'leanResidualProjectionMinimumAttainmentFormalized',
    'leanResidualProjectionMinimumUniversalLowerBoundsFormalized',
    'leanResidualProjectionMinimumMonotonicityFormalized',
    'leanResidualProjectionDefectDecompositionFormalized',
    'leanResidualProjectionDefectZeroIffCheckedLiftAtMinimumFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualProjectionMinimumScope,
    'all-finite-direct-wire-implementations-with-computed-finite-profile-observers-explicit-projections-and-exhaustive-search-through-the-current-gate-count',
  );
  for (const field of [
    'leanResidualProjectionTransferFormalized',
    'leanResidualProjectionTransferAxiomAuditPassed',
    'leanResidualProjectionTransferSignedDeltasFormalized',
    'leanResidualProjectionTransferIdentityFormalized',
    'leanResidualProjectionTransferConstantCutFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualProjectionTransferScope,
    'all-finite-direct-wire-four-corner-terminal-profile-families-sharing-one-computed-observer-and-one-explicit-projection',
  );
  for (const field of [
    'leanResidualTerminalSaturationFormalized',
    'leanResidualTerminalSaturationAxiomAuditPassed',
    'leanResidualTerminalPrimitiveUniverseFormalized',
    'leanResidualTerminalSaturationExtensiveFormalized',
    'leanResidualTerminalSaturationLeastFormalized',
    'leanResidualTerminalSaturationMonotoneFormalized',
    'leanResidualTerminalSaturationIdempotentFormalized',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualTerminalSaturationScope,
    'all-finite-terminal-primitive-record-universes-with-explicit-boolean-rule-tagged-dependencies',
  );
  for (const field of [
    'leanResidualTerminalExecutableSaturationFormalized',
    'leanResidualTerminalPhysicalSupportCompletionFormalized',
    'leanResidualTerminalPhysicalBoundaryFormalized',
    'leanResidualTerminalPhysicalInterfaceFormalized',
    'leanResidualTerminalPhysicalCompatibilityFormalized',
    'leanResidualTerminalPhysicalSupportCompletionAxiomAuditPassed',
    'leanResidualTerminalSupportExtractionFormalized',
    'leanResidualTerminalOpenSemanticsFormalized',
    'leanResidualTerminalInducedRecoveryFormalized',
    'leanResidualTerminalSupportExtractionAxiomAuditPassed',
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
    'leanResidualTerminalSupportSquareClosureFormalized',
    'leanResidualTerminalSupportSquareMeetJoinExactFormalized',
    'leanResidualTerminalSupportSquarePhysicalCompatibilityFormalized',
    'leanResidualTerminalSupportSquareSemanticExtractionFormalized',
    'leanResidualTerminalSupportSquareClosureAxiomAuditPassed',
    'leanResidualTerminalSupportCompletionFormalized',
    'leanResidualTerminalGovernedSupportCompletionFormalized',
    'leanResidualTerminalGovernedProfilePartitionFormalized',
    'leanResidualTerminalGovernedSupportCompletionAxiomAuditPassed',
    'leanResidualTerminalFrontierPushoutFormalized',
    'leanResidualTerminalFrontierBoundaryGlueExactFormalized',
    'leanResidualTerminalFrontierInterfaceGlueExactFormalized',
    'leanResidualTerminalFrontierProfileGlueExactFormalized',
    'leanResidualTerminalFrontierInternalizationFormalized',
    'leanResidualTerminalFrontierPushoutAxiomAuditPassed',
    'leanResidualTerminalProjectionSquareFormalized',
    'leanResidualTerminalProjectionPhysicalInvariantFormalized',
    'leanResidualTerminalProjectionProfileExactFormalized',
    'leanResidualTerminalProjectionMeetJoinCommuteFormalized',
    'leanResidualTerminalProjectionPushoutCommuteFormalized',
    'leanResidualTerminalProjectionSquareAxiomAuditPassed',
    'leanResidualTerminalSideTightMinimumArithmeticFormalized',
    'leanResidualTerminalSideTightSignedSlackIdentityFormalized',
    'leanResidualTerminalSideTightFailClosedGateFormalized',
    'leanResidualTerminalSideTightCanonicalFullBasisFormalized',
    'leanResidualTerminalSideTightCanonicalQuotientBasisFormalized',
    'leanResidualTerminalSideTightMinimumAxiomAuditPassed',
    'leanResidualTerminalFourCornerCarrierTransportFormalized',
    'leanResidualTerminalFourCornerCarrierExactEndpointsFormalized',
    'leanResidualTerminalFourCornerCarrierInjectiveCoordinatesFormalized',
    'leanResidualTerminalFourCornerCarrierProfileTransportFormalized',
    'leanResidualTerminalFourCornerCarrierFailClosedPhysicalTransportFormalized',
    'leanResidualTerminalFourCornerCarrierAxiomAuditPassed',
    'leanResidualTerminalFourCornerOptimaCarrierCompatibleFormalized',
    'leanResidualTerminalFourCornerOptimaFaithfulAmbientizationFormalized',
    'leanResidualTerminalFourCornerOptimaReferenceMinimumPreservedFormalized',
    'leanResidualTerminalFourCornerOptimaLocalizedMinimaFormalized',
    'leanResidualTerminalFourCornerOptimaSharedObserverProjectionFormalized',
    'leanResidualTerminalFourCornerOptimaAxiomAuditPassed',
    'leanResidualTerminalFourCornerOptimumLocalRouteClassifierFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSoundnessFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumSideTightCompletionUnderRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumExactCompletionValuesFormalized',
    'leanResidualTerminalFourCornerOptimumPromotionFirewallRetained',
    'leanResidualTerminalFourCornerSideTightCompletionAxiomAuditPassed',
    'leanResidualTerminalFourCornerArbitraryFamilyCoherenceFormalized',
    'leanResidualTerminalFourCornerExactMinimumFamilyEnumerated',
    'leanResidualTerminalFourCornerTightBasisFamilyComplete',
    'leanResidualTerminalFourCornerSignedTightBasisMaximumFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumEqualsDeltaFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumAxiomAuditPassed',
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalSquareStructuralCompatibilityFormalized',
    'leanResidualTerminalSquareFrontierPushoutFormalized',
    'leanResidualTerminalSquareSharedQuantityCarrierFormalized',
    'leanResidualTerminalSquareLocalConclusionUnderRouteSilenceFormalized',
    'leanResidualTerminalSquareFailClosedRouteDichotomyFormalized',
    'leanResidualTerminalSquareLegitimacyAxiomAuditPassed',
    'leanResidualTerminalCoherentFourCornerBasisFormalized',
    'leanResidualTerminalComputedBCELAnchorNucleusFormalized',
    'leanResidualTerminalBCELMinimumPositiveNucleusFormalized',
    'leanResidualTerminalBCELAnchorAlgebraFormalized',
    'leanResidualTerminalBCELCutDefectFirewallFormalized',
    'leanResidualTerminalBCELCutRouteDichotomyFormalized',
    'leanResidualTerminalBCELConstantCutConclusionFormalized',
    'leanResidualTerminalBCELAnchorNucleusAxiomAuditPassed',
    'leanResidualTerminalSaturationPositivityFirewallFormalized',
    'leanResidualTerminalSaturationPositivityFirewallAxiomAuditPassed',
    'leanResidualTerminalCandidateSaturationFormalized',
    'leanResidualTerminalSaturationCostBalanceFormalized',
    'leanResidualTerminalFirstNontransparentStepFormalized',
    'leanResidualTerminalSaturationCostBalanceAxiomAuditPassed',
    'leanResidualTerminalInterfaceExposureRoutingFormalized',
    'leanResidualTerminalFiniteInterfaceExposureRoutesToEFormalized',
    'leanResidualTerminalInterfaceExposureZeroCostRetractFormalized',
    'leanResidualTerminalFirstInterfaceExposureRouteFormalized',
    'leanResidualTerminalInterfaceExposureRoutingAxiomAuditPassed',
    'leanResidualTerminalOriginKernelObligationRoutingFormalized',
    'leanResidualTerminalFiniteOriginKernelObligationClosureRoutedFormalized',
    'leanResidualTerminalFirstOriginKernelObligationRouteFormalized',
    'leanResidualTerminalOriginKernelObligationRoutingAxiomAuditPassed',
    'leanResidualTerminalFiniteSaturatePositiveCompositionFormalized',
    'leanResidualTerminalFiniteSaturatePositiveCompositionAxiomAuditPassed',
    'leanResidualTerminalRankWFFormalized',
    'leanResidualTerminalRankWFAxiomAuditPassed',
    'leanResidualTerminalBN3RequestEnvelopeFormalized',
    'leanResidualTerminalBN3RequestEnvelopeAxiomAuditPassed',
    'leanResidualTerminalBN4ActivationCancellationFormalized',
    'leanResidualTerminalBN4ActivationCancellationAxiomAuditPassed',
    'leanResidualTerminalBN5FullShadowLocalizationFormalized',
    'leanResidualTerminalBN5FullShadowLocalizationAxiomAuditPassed',
    'leanResidualTerminalPkgCSeparatingConsumersFormalized',
    'leanResidualTerminalPkgCSeparatingConsumersAxiomAuditPassed',
    'leanResidualTerminalPkgCTypedRestorationFormalized',
    'leanResidualTerminalPkgCTypedRestorationAxiomAuditPassed',
    'leanResidualTerminalPkgCSameKeyCancellationFormalized',
    'leanResidualTerminalPkgCSameKeyCancellationAxiomAuditPassed',
    'leanResidualTerminalPkgCAmbientBN4LedgerFormalized',
    'leanResidualTerminalPkgCAmbientBN4LedgerAxiomAuditPassed',
    'leanResidualTerminalPkgCAmbientBN4ResidualReductionFormalized',
    'leanResidualTerminalPkgCAmbientBN4ResidualReductionAxiomAuditPassed',
    'leanResidualTerminalConsumerAntichainNormalFormFormalized',
    'leanResidualTerminalConsumerAntichainNormalFormAxiomAuditPassed',
    'leanResidualTerminalConstantCutHypergraphRigidityFormalized',
    'leanResidualTerminalConstantCutHypergraphRigidityAxiomAuditPassed',
    'leanResidualTerminalBN6HypergraphPacketFormalized',
    'leanResidualTerminalBN6HypergraphPacketAxiomAuditPassed',
    'leanResidualTerminalPacketSelectorSeedsFormalized',
    'leanResidualTerminalPacketSelectorSeedsAxiomAuditPassed',
    'leanResidualTerminalPacketSelectorUniverseFormalized',
    'leanResidualTerminalPacketSelectorUniverseAxiomAuditPassed',
    'leanResidualTerminalPacketSelectorHandlesFormalized',
    'leanResidualTerminalPacketSelectorHandlesAxiomAuditPassed',
    'leanResidualTerminalPacketSelectorCodecFormalized',
    'leanResidualTerminalPacketSelectorCodecAxiomAuditPassed',
    'leanResidualTerminalPacketSelectorPayloadRealizationFormalized',
    'leanResidualTerminalPacketSelectorPayloadRealizationAxiomAuditPassed',
  ]) assert.equal(out[field], true, field);
  assert.equal(
    out.leanResidualTerminalPhysicalSupportCompletionScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-finite-seed-lists',
  );
  assert.equal(
    out.leanResidualTerminalSupportExtractionScope,
    'all-finite-direct-wire-candidates-terminal-record-lists-boundary-valuations-and-interface-coordinates',
  );
  assert.equal(
    out.leanResidualTerminalProperSupportScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-canonical-primitive-record-seeds-with-exhaustive-reference-minimum-local-gain',
  );
  assert.equal(
    out.leanResidualTerminalSupportSquareClosureScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-pairs-of-finite-terminal-seeds',
  );
  assert.equal(
    out.leanResidualTerminalGovernedSupportCompletionScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-finite-seed-lists-and-saturated-support-square-corners',
  );
  assert.equal(
    out.leanResidualTerminalFrontierPushoutScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-computed-saturated-support-squares',
  );
  assert.equal(
    out.leanResidualTerminalProjectionSquareScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-saturated-support-squares-and-forgetful-terminal-projections',
  );
  assert.equal(
    out.leanResidualTerminalSideTightMinimumScope,
    'all-finite-terminal-projection-four-corner-families-and-independently-attained-full-and-quotient-minimum-bases',
  );
  assert.equal(
    out.leanResidualTerminalFourCornerCarrierScope,
    'all-finite-computed-saturated-terminal-support-squares-and-canonical-physical-profile-transport-coordinates',
  );
  assert.equal(
    out.leanResidualTerminalFourCornerOptimaCarrierScope,
    'all-finite-computed-saturated-terminal-support-squares-one-reversible-ambient-carrier-and-shared-observer-projection',
  );
  assert.equal(
    out.leanResidualTerminalFourCornerSideTightCompletionScope,
    'all-finite-computed-terminal-support-squares-observers-and-full-or-quotient-modes-side-tight-coherent-completion-under-exact-local-route-silence',
  );
  assert.equal(
    out.leanResidualTerminalFourCornerTightBasisMaximumScope,
    'all-finite-computed-terminal-support-squares-observers-and-full-or-quotient-modes-complete-tight-basis-family-and-signed-maximum-under-exact-local-route-silence',
  );
  assert.equal(
    out.leanResidualTerminalCoherentFourCornerBasisScope,
    'conditional-on-exact-mode-appropriate-local-route-silence-not-universal-bn2-square-legitimacy',
  );
  assert.equal(
    out.leanResidualTerminalSquareLegitimacyScope,
    'all-finite-computed-terminal-support-squares-explicit-terminal-dependency-systems-direct-wire-candidates-observers-and-forgetful-projections-with-local-route-silence-or-proof-bearing-first-failure',
  );
  assert.equal(
    out.leanResidualTerminalBCELAnchorNucleusScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-governed-proper-positive-supports-forgetful-projections-executable-ambient-observers-and-positive-whole-support-projection-defect',
  );
  assert.equal(
    out.leanResidualTerminalSaturationPositivityFirewallScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-governed-proper-positive-supports-forgetful-projections-and-executable-ambient-observers-total-zero-or-positive-whole-support-projection-defect-classification',
  );
  assert.equal(
    out.leanResidualTerminalSaturationCostBalanceScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-candidate-derived-dependency-system-rule-labelled-exact-cost-balance-or-first-nontransparent-step',
  );
  assert.equal(
    out.leanResidualTerminalInterfaceExposureRoutingScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-candidate-derived-interface-consumer-transparent-or-local-e-route-with-exact-first-failure',
  );
  assert.equal(
    out.leanResidualTerminalOriginKernelObligationRoutingScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-candidate-derived-origin-kernel-obligation-closures-with-exact-safety-or-first-route',
  );
  assert.equal(
    out.leanResidualTerminalFiniteSaturatePositiveCompositionScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-proof-bearing-positive-full-slack-candidate-bcel-anchor-problems-total-finite-saturate-positive-composition',
  );
  assert.equal(
    out.leanResidualTerminalRankWFScope,
    'fixed-ten-coordinate-natural-lexicographic-order-executable-comparison-accessibility-induction-and-kernel-well-foundedness',
  );
  assert.equal(
    out.leanResidualTerminalBN3RequestEnvelopeScope,
    'successful-computed-finite-bcel-anchor-nuclei-canonical-stable-request-identities-exact-singleton-minimal-consumers-duplicate-free-incidence-and-jointly-side-tight-full-or-quotient-basis-family',
  );
  assert.equal(
    out.leanResidualTerminalBN4ActivationCancellationScope,
    'successful-computed-finite-bn3-envelope-explicit-typed-cell-ledgers-activation-exact-complete-key-same-key-cancellation-and-exact-integer-mass-residuals',
  );
  assert.equal(
    out.leanResidualTerminalBN5FullShadowLocalizationScope,
    'all-finite-exact-coordinate-negative-unit-refinements-computed-cut-silence-complete-multiplicity-coverage-or-strict-hall-deficit-with-local-x1-nonsilence',
  );
  assert.equal(
    out.leanResidualTerminalPkgCSeparatingConsumersScope,
    'all-finite-explicit-minimal-consumer-antichains-pkgc-separating-consumer-first-pair-canonical-atoms-exact-coordinate-restoration-or-strict-hall-local-q',
  );
  assert.equal(
    out.leanResidualTerminalPkgCTypedRestorationScope,
    'all-finite-explicit-minimal-consumer-antichains-typed-full-restoration-candidates-coordinate-preserving-exact-multiplicity-coverage-no-hall-or-singletonized',
  );
  assert.equal(
    out.leanResidualTerminalPkgCSameKeyCancellationScope,
    'all-finite-explicit-minimal-consumer-antichains-typed-exact-coordinate-restoration-canonical-opposite-sign-bn4-ledger-every-key-balanced-empty-residual-or-singletonized-under-cancellation-silence',
  );
  assert.equal(
    out.leanResidualTerminalPkgCAmbientBN4LedgerScope,
    'all-finite-explicit-ambient-bn4-ledgers-exact-multiset-embedding-balanced-generated-subledger-removal-preserves-remainder-signed-mass-and-candidate-derived-canonical-atom-linkage',
  );
  assert.equal(
    out.leanResidualTerminalPkgCAmbientBN4ResidualReductionScope,
    'all-finite-explicit-ambient-bn4-ledgers-exact-balanced-subledger-removal-preserves-per-key-and-complete-canonical-executable-residual-ledgers-with-empty-remainder-corollary',
  );
  assert.equal(
    out.leanResidualTerminalConsumerAntichainNormalFormScope,
    'all-finite-minimal-consumer-antichains-monotone-empty-false-nonzero-iff-disjoint-and-pkgc-singletonized-exact-v54-consumer-antichain-cut-indicator',
  );
  assert.equal(
    out.leanResidualTerminalConstantCutHypergraphRigidityScope,
    'all-finite-nonnegative-weighted-hypergraphs-constant-cut-hypergraph-rigidity-v53-q2-q3-q4-classification',
  );
  assert.equal(
    out.leanResidualTerminalBN6HypergraphPacketScope,
    'all-finite-explicit-grouped-v54-activation-to-v53-grouped-hypergraph-packet-bn6-pair-mixed-triple-fullspan-with-payload-witnesses',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorSeedsScope,
    'all-finite-explicit-bn6-packet-conclusions-payload-backed-pair-balanced-triple-or-fullspan-selector-seed-input-extraction',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorUniverseScope,
    'all-finite-explicit-bn6-grouped-families-exact-grouped-footprint-payload-selector-universe-membership',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorHandlesScope,
    'all-finite-explicit-bn6-grouped-families-canonical-indexed-grouped-footprint-handles-unique-decoding-payload-carrier-and-size-compatibility',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorCodecScope,
    'all-finite-explicit-bn6-grouped-families-canonical-unary-fail-closed-handle-codec-round-trip-unique-decoding-payload-carrier-size-and-explicit-universe-length-bound',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorPayloadRealizationScope,
    'all-finite-explicit-bn6-grouped-families-total-fail-closed-source-payload-realization-exact-original-cell-footprint-positive-atom-and-packet-branch-preservation',
  );
  assert.equal(out.leanResidualTerminalPacketSelectorGainScanFormalized, true);
  assert.equal(
    out.leanResidualTerminalPacketSelectorGainScanAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorGainScanScope,
    'all-finite-explicit-bn6-grouped-families-direct-wire-implementation-payloads-total-fail-closed-exact-source-cell-checked-strict-gain-or-cell-local-no-gain-packet-branch-preservation',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorUniverseGainScanFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorUniverseGainScanAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorUniverseGainScanScope,
    'all-finite-explicit-bn6-grouped-families-exhaustive-canonical-selector-scan-with-checked-strict-gain-or-family-local-no-gain-and-packet-branch-preservation',
  );
  assert.equal(
    out.leanResidualTerminalHBActiveDependencyClosureFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalHBActiveDependencyClosureAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalHBActiveDependencyClosureScope,
    'all-arbitrary-finite-hn-budget-total-tables-exhaustive-active-dependency-local-closure-exact-rank-induction-all-node-blocker-silence-and-gain-or-lower-seed-composition',
  );
  assert.equal(
    out.leanResidualTerminalHBSelectorSilenceClosureFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalHBSelectorSilenceClosureAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalHBSelectorSilenceClosureScope,
    'all-arbitrary-finite-canonical-selector-tables-explicit-global-semantic-gain-exclusion-checked-hn-budget-inactivity-strong-rank-induction-and-rank-complete-selector-silence',
  );
  assert.equal(
    out.leanResidualTerminalHBExecutableSelectorSilenceInductionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalHBExecutableSelectorSilenceInductionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalHBExecutableSelectorSilenceInductionScope,
    'all-arbitrary-finite-canonical-selector-tables-executable-all-row-selector-silence-checked-hn-budget-inactivity-strong-rank-induction-without-global-semantic-no-gain',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFaithfulnessRoutingFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFaithfulnessRoutingAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFaithfulnessRoutingScope,
    'all-arbitrary-finite-positive-bn6-packets-executable-canonical-payload-route-clearance-exact-hb-faithfulness-binding-and-selector-silence-contradiction',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFaithfulnessTableFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFaithfulnessTableAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFaithfulnessTableScope,
    'all-arbitrary-finite-canonical-packet-payload-faithfulness-table-construction-preserved-rank-claims-blocker-activity-binding-free-selector-silence-contradiction',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFirstRouteOutcomeFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFirstRouteOutcomeAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFirstRouteOutcomeScope,
    'all-arbitrary-finite-total-packet-first-route-classification-canonical-hb-selector-silence-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFirstRouteSemanticsFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFirstRouteSemanticsAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSelectorFirstRouteSemanticsScope,
    'all-arbitrary-finite-exact-earliest-field-semantics-for-ten-packet-first-routes-canonical-hb-first-route-failure-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketDescentRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketDescentRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketDescentRouteReflectionScope,
    'all-arbitrary-finite-rank-reflected-packet-descent-route-exact-rankwf-nondecrease-or-earlier-first-route-without-route-clear-or-descent-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketRankRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketRankRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketRankRouteReflectionScope,
    'all-arbitrary-finite-canonical-rank-tag-reflection-rank-route-excluded-exact-rankwf-nondecrease-or-earlier-route-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketExactRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketExactRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketExactRouteReflectionScope,
    'all-arbitrary-finite-canonical-source-route-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-seven-earlier-semantic-routes-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketChargeRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketChargeRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketChargeRouteReflectionScope,
    'all-arbitrary-finite-positive-source-charge-charge-route-excluded-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-six-earlier-semantic-routes-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketColourRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketColourRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketColourRouteReflectionScope,
    'all-arbitrary-finite-grouped-footprint-colour-colour-route-excluded-charge-route-excluded-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-five-earlier-semantic-routes-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketFrontierRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketFrontierRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketFrontierRouteReflectionScope,
    'all-arbitrary-finite-typed-frontier-equality-frontier-route-reflected-colour-route-excluded-charge-route-excluded-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-four-earlier-semantic-routes-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketBN5ObligationRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBN5ObligationRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBN5ObligationRouteReflectionScope,
    'all-arbitrary-finite-BN5-coordinate-frontier-obligation-routes-reflected-colour-route-excluded-charge-route-excluded-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-three-earlier-semantic-routes-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketBN4ActivationRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBN4ActivationRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBN4ActivationRouteReflectionScope,
    'all-arbitrary-finite-BN4-activation-predicate-route-reflected-BN5-frontier-obligation-routes-reflected-colour-route-excluded-charge-route-excluded-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-two-earlier-semantic-routes-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketDirectionRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketDirectionRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketDirectionRouteReflectionScope,
    'all-arbitrary-finite-typed-direction-equality-route-reflected-BN5-frontier-obligation-activation-routes-reflected-colour-route-excluded-charge-route-excluded-exact-route-excluded-rank-route-excluded-exact-rankwf-nondecrease-or-sole-remaining-budget-route-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketBudgetRouteReflectionFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBudgetRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBudgetRouteReflectionScope,
    'all-arbitrary-finite-typed-budget-equality-all-packet-route-fields-reflected-colour-charge-exact-route-rank-excluded-exact-rankwf-nondecrease-without-route-clear-or-binding-premises',
  );
  assert.equal(
    out.leanResidualTerminalPacketBudgetHBActivityBindingFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBudgetHBActivityBindingAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketBudgetHBActivityBindingScope,
    'all-arbitrary-finite-typed-budget-mismatch-to-HB-activity-checked-budget-route-excluded-under-checked-well-founded-HB-closure',
  );
  assert.equal(
    out.leanResidualTerminalPacketSemanticHNActivityBindingFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSemanticHNActivityBindingAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketSemanticHNActivityBindingScope,
    'all-arbitrary-finite-frontier-obligation-activation-direction-mismatch-to-HN-activity-checked-sole-descent-route-under-checked-semantic-HN-budget-HB-and-well-founded-HB-closure',
  );
  assert.equal(
    out.leanResidualTerminalPacketDescentNoLowerBindingFormalized,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketDescentNoLowerBindingAxiomAuditPassed,
    true,
  );
  assert.equal(
    out.leanResidualTerminalPacketDescentNoLowerBindingScope,
    'all-arbitrary-finite-canonical-packet-handles-exhaustive-local-descent-no-lower-row-rejected-under-checked-positive-packet-semantic-HN-budget-HB-selector-silence-and-HB-closure',
  );
  for (const field of [
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
  ]) assert.equal(out[field], false, field);
  for (const field of [
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanResidualGainChainPolynomialRuntimeFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
  ]) assert.equal(out[field], false, field);
  assert.equal(out.rootLeanTheoremPresent, false);
  assert.equal(out.rootLeanTheoremBuilt, false);
  assert.equal(out.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(out.projectSpecificAxiomsRemaining, true);
  assert.deepEqual(out.projectSpecificAxiomInventory, [
    'PNP.CheckPCCPackexp',
    'PNP.GeneratePCCPack',
    'PNP.LockedNANDThreshold',
    'PNP.ResidualBandExactMinimization',
  ]);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.deepEqual(out.remainingBlockers, FORMAL_RECONSTRUCTION_BLOCKERS0);
  assert.equal(out.remainingBlockers.length, 5);
  assert.equal(out.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), false);
  assert.equal(out.remainingBlockers.includes('Formal.PinnedLeanBuildAndRootTarget'), false);
  assert.match(out.statusSha256, /^[0-9a-f]{64}$/u);
  assert.match(out.siteStatusSha256, /^[0-9a-f]{64}$/u);
});

test('formal reconstruction status pins the locked-NAND carrier inventory and source closure', async () => {
  const [status, inventory] = await Promise.all([
    currentStatus0(),
    readFile(new URL('../status/LEAN_THEOREM_INVENTORY.json', import.meta.url),
      'utf8').then(JSON.parse),
  ]);
  assert.equal(status.leanTheoremInventoryDeclarationCount,
    inventory.declarationCount);
  assert.equal(status.leanTheoremInventoryTheoremCount, inventory.theoremCount);
  assert.equal(status.leanTheoremInventoryAssumptionFreeTheoremCount,
    inventory.assumptionFreeTheoremCount);
  assert.equal(status.leanTheoremInventoryExcludedPrivateDeclarationCount,
    inventory.excludedPrivateDeclarationCount);
  assert.equal(status.leanTheoremInventorySourceClosureModuleCount,
    inventory.sourceClosureModuleCount);
  assert.match(status.leanSourceClosureSha256, /^[0-9a-f]{64}$/u);
  const machine = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  assert.equal(machine.status, 'formalized-foundation-only');
  assert.equal(machine.earned, true);
  for (const name of [
    'PNP.Concrete.PipelineCompiler.pipeline_correct',
    'PNP.Concrete.PipelineCompiler.pipeline_boundedDecide_eq',
    'PNP.Concrete.PipelineCompiler.pipeline_machineOutput_eq',
    'PNP.Concrete.PipelineCompiler.pipeline_ne_timeout',
    'PNP.Concrete.PipelineCompiler.pipeline_accepts_iff',
    'PNP.Concrete.PipelineCompiler.pipeline_timeout_of_stuck_rawRunExact',
    'PNP.Concrete.PipelineCompiler.pipelineOutputSizeBound_eval',
    'PNP.Concrete.PipelineCompiler.suppliedTraceRawSteps_le_pipelineRawTimeBound',
    'PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_first_of_some',
    'PNP.Concrete.PipelineSequentialStateNamespace.findWorkRule_sequential_second_of_some',
    'PNP.Concrete.PipelineSequentialStateNamespace.firstAcceptLaunch_workStep',
    'PNP.Concrete.PipelineSequentialStateNamespace.firstPipelineState_ne_secondPipelineState',
    'PNP.Concrete.PipelineSequentialStateNamespace.firstRejectLaunch_workStep',
    'PNP.Concrete.PipelineSequentialStateNamespace.sequentialWorkMachine_acceptState_ne_rejectState',
    'PNP.Concrete.PipelineSequentialCompiler.acceptingSequentialTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.firstOutputSizeBound_eval',
    'PNP.Concrete.PipelineSequentialCompiler.firstTraceAndLaunch_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.rejectingSequentialTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.run_sequential_accept_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.run_sequential_reject_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.sequentialOutputSizeBound_eval',
    'PNP.Concrete.PipelineSequentialCompiler.sequentialRawSteps_le_of_rawRunExact',
    'PNP.Concrete.PipelineSequentialCompiler.sequentialRawSteps_le_sequentialRawTimeBound',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_accepts_iff',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_boundedDecide_eq',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_correct',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_machineOutput_eq',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_ne_timeout',
    'PNP.Concrete.PipelineSequentialCompiler.sequential_timeout_of_stuck_first_rawRunExact',
    'PNP.Concrete.FunctionProgram.RawRefinement.compile_haltsWithin',
    'PNP.Concrete.FunctionProgram.RawRefinement.compile_output_eq',
    'PNP.Concrete.DecisionProgram.RawRefinement.compile_haltsWithin',
    'PNP.Concrete.DecisionProgram.RawRefinement.compile_verdict_eq',
    'PNP.Concrete.PolynomialTimeDecider.compileToMachine_accepts_iff',
  ]) assert.equal(machine.requiredTheorems.includes(name), true, name);
  for (const name of [
    'PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_accept',
    'PNP.Concrete.PipelineInputFramer.boundedDecide_compileTotalInputFramer_ne_timeout',
    'PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_encoded_rawTimeBound',
    'PNP.Concrete.PipelineInputFramer.run_compileTotalInputFramer_rawTimeBound_blankEquivalent',
    'PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_isHalted',
    'PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_represents',
    'PNP.Concrete.PipelineInputFramer.totalInputFramerRawTimeBound_le',
    'PNP.Concrete.PipelineInputFramer.totalInputFramer_workRunExact',
  ]) assert.equal(machine.requiredTheorems.includes(name), true, name);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_step'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_of_step'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_rawRunExact'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.liftMachine_isHalted_eq_of_representsConfiguration'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.rawRunExact?_exists_le_run'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.workRun_three_mul_of_run_halted'), true);
  assert.equal(machine.requiredTheorems.includes(
    'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_run_halted'), true);
  for (const name of [
    'PNP.Concrete.PipelineStageBridges.inputLaunch_workStep',
    'PNP.Concrete.PipelineStageBridges.acceptingLaunch_workStep',
    'PNP.Concrete.PipelineStageBridges.rejectingLaunch_workStep',
    'PNP.Concrete.PipelineStageBridges.bridgedWorkSteps_eq',
    'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_accept_of_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_reject_of_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.workBoundedDecide_bridged_timeout_of_stuck_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_accept_of_rawRunExact',
    'PNP.Concrete.PipelineStageBridges.run_compileBridgedMachine_reject_of_rawRunExact',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_workRunExact',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPackerFinal_isHalted',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_output_eq',
    'PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker_exact',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_runtime_le',
    'PNP.Concrete.TerminalOutputPacker.run_compileTerminalOutputPacker',
    'PNP.Concrete.TerminalOutputPacker.machineOutput_compileTerminalOutputPacker_eq',
    'PNP.Concrete.TerminalOutputPacker.terminalOutputPacker_one_step_short_timeout',
    'PNP.Concrete.PipelineTerminalBridge.acceptingPackerLaunch_workStep',
    'PNP.Concrete.PipelineTerminalBridge.acceptingSuppliedTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.acceptingTerminalFinal_isHalted',
    'PNP.Concrete.PipelineTerminalBridge.acceptingTerminal_workRunExact_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.bridged_workRunExact_of_exact',
    'PNP.Concrete.PipelineTerminalBridge.bridged_workStep?_of_some',
    'PNP.Concrete.PipelineTerminalBridge.findWorkRule_terminalBridge_acceptingPacker_of_some',
    'PNP.Concrete.PipelineTerminalBridge.findWorkRule_terminalBridge_rejectingPacker_of_some',
    'PNP.Concrete.PipelineTerminalBridge.machineOutput_compileTerminalBridge_accept_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.machineOutput_compileTerminalBridge_reject_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.outputBits_compileTerminalBridge_accepting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.outputBits_compileTerminalBridge_rejecting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.rejectingPackerLaunch_workStep',
    'PNP.Concrete.PipelineTerminalBridge.rejectingSuppliedTrace_workRunExact_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.rejectingTerminalFinal_isHalted',
    'PNP.Concrete.PipelineTerminalBridge.rejectingTerminal_workRunExact_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accept_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accepting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_accepting_of_represents_at_bound',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_reject_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_rejecting_of_represents',
    'PNP.Concrete.PipelineTerminalBridge.run_compileTerminalBridge_rejecting_of_represents_at_bound',
    'PNP.Concrete.PipelineTerminalBridge.simulationPrefix_terminalBridge_workBoundedDecide_timeout',
    'PNP.Concrete.PipelineTerminalBridge.suppliedTraceTerminalWorkSteps_eq',
    'PNP.Concrete.PipelineTerminalBridge.terminalBridgeMachine_acceptState_ne_rejectState',
    'PNP.Concrete.PipelineTerminalBridge.terminalBridge_runtime_le',
    'PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_accept_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_reject_of_rawRunExact',
    'PNP.Concrete.PipelineTerminalBridge.workBoundedDecide_terminalBridge_timeout_of_stuck_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.machineOutput_length_le_input_add_fuel',
    'PNP.Concrete.PipelinePairedCompiler.outputBits_length_le_pairedPipelineOutputSizeBound_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipelineOutputSizeBound_eval',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_accepts_iff',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_boundedDecide_eq',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_correct_on_pair',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_machineOutput_eq',
    'PNP.Concrete.PipelinePairedCompiler.pairedPipeline_ne_timeout',
    'PNP.Concrete.PipelinePairedCompiler.run_pairedPipeline_accept_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.run_pairedPipeline_reject_at_bound_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.suppliedTraceTerminalRawSteps_le_of_rawRunExact',
    'PNP.Concrete.PipelinePairedCompiler.suppliedTraceTerminalRawSteps_le_pairedPipelineRawTimeBound',
  ]) assert.equal(machine.requiredTheorems.includes(name), true, name);
  assert.match(machine.scope, /One literal finite four-stage pipeline handles every raw bitstring/u);
  assert.match(machine.scope, /exactly 4 work steps on empty input/u);
  assert.match(machine.scope, /6 \* m \* m \+ 39 \* m \+ 75/u);
  assert.match(machine.scope, /PipelineCompiler preserves one raw target's verdict and ordinary output/u);
  assert.match(machine.scope, /PipelineSequentialCompiler composes two raw targets/u);
  assert.match(machine.scope, /R\(m\) = PipelineRaw\(p\)\(m\) \+ 6 \+ PipelineRaw\(q\)\(m \+ p\(m\) \+ 1\)/u);
  assert.match(machine.scope, /PipelineRefinement recursively applies that compiler/u);
  assert.match(machine.scope, /16 audited declarations have empty axiom closure/u);
  assert.match(machine.nonClaim, /closes the concrete complexity machine-link blocker only/u);
  assert.match(machine.nonClaim, /P = NP/u);
  const cnf = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-cnf-universal-verifier',
  );
  assert.equal(cnf.status, 'formalized-np-membership-only');
  assert.equal(cnf.earned, true);
  assert.equal(cnf.requiredTheorems.includes(
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP'), true);
  for (const command of [
    'node --test audits/lean-concrete-pipeline-input-framer0.test.mjs',
    'node --test audits/lean-concrete-pipeline-output-handoff0.test.mjs',
    'node --test audits/lean-concrete-pipeline-state-namespace0.test.mjs',
    'node --test audits/lean-concrete-pipeline-sequential-state-namespace0.test.mjs',
    'node --test audits/lean-concrete-pipeline-stage-bridges0.test.mjs',
    'node --test audits/lean-concrete-terminal-output-packer0.test.mjs',
    'node --test audits/lean-concrete-pipeline-terminal-bridge0.test.mjs',
    'node --test audits/lean-concrete-pipeline-paired-compiler0.test.mjs',
    'node --test audits/lean-concrete-pipeline-compiler0.test.mjs',
    'node --test audits/lean-concrete-pipeline-sequential-compiler0.test.mjs',
    'node --test audits/lean-concrete-pipeline-machine-simulation0.test.mjs',
    'node --test audits/lean-concrete-pipeline-tape-geometry0.test.mjs',
    'node --test audits/lean-concrete-tape-handoff0.test.mjs',
    'node --test audits/lean-concrete-pipeline-refinement0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelinePairedCompilerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelinePairedCompiler.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineCompiler.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineSequentialCompilerAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineSequentialCompiler.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcretePipelineRefinementRecursive.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFWorkAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFWorkCanonical.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteWorkCompilerEdges.lean',
    'lake env lean -DwarningAsError=true --run lean-regression/PNPConcreteCNFWorkCanonicalExtended.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFWorkExhaustive.lean',
    'node --test audits/lean-concrete-cook-levin-builder-token-appender0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderTokenAppenderAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderTokenAppender.lean',
    'node --test audits/lean-concrete-cook-levin-builder-first-token-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFirstTokenPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFirstTokenPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-complete-header0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderUnaryPolynomialAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderCompleteHeaderAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderCompleteHeader.lean',
    'node --test audits/lean-concrete-cook-levin-builder-body-start-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderBodyStartPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderBodyStartPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-first-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFirstLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFirstLiteralPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-first-clause-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFirstClausePrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFirstClausePrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-dynamic-token-cursor-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderDynamicTokenCursorStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderDynamicTokenCursorStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-first-clause-padding-run0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFirstClausePaddingRunAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFirstClausePaddingRun.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-clause-separator-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondClauseSeparatorStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondClauseSeparatorStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-clause-first-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondClauseFirstLiteralPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-clause-second-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-clause-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondClausePrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondClausePrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-clause-padding-run0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondClausePaddingRunAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondClausePaddingRun.lean',
    'node --test audits/lean-concrete-cook-levin-builder-third-clause-separator-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderThirdClauseSeparatorStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderThirdClauseSeparatorStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-third-clause-first-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-third-clause-second-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefix.lean',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderThirdClausePrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderThirdClausePrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-third-clause-padding-run0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderThirdClausePaddingRunAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderThirdClausePaddingRun.lean',
    'node --test audits/lean-concrete-cook-levin-builder-fourth-clause-separator-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFourthClauseSeparatorStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFourthClauseSeparatorStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-fourth-clause-first-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-fourth-clause-second-literal-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-fourth-clause-prefix0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFourthClausePrefixAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFourthClausePrefix.lean',
    'node --test audits/lean-concrete-cook-levin-builder-fourth-clause-padding-run0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFourthClausePaddingRunAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFourthClausePaddingRun.lean',
    'node --test audits/lean-concrete-cook-levin-builder-fifth-clause-padding-run0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFifthClausePaddingRunAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFifthClausePaddingRun.lean',
    'node --test audits/lean-concrete-cook-levin-builder-first-constraint-padding-run0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderFirstConstraintPaddingRunAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderFirstConstraintPaddingRun.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-separator-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSeparatorStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSeparatorStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-sign-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-terminator-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.lean',
    'node --test audits/lean-concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step0.test.mjs',
    'lake env lean -DwarningAsError=true lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepAxiomAudit.lean',
    'lake env lean -DwarningAsError=true lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.lean',
  ]) assert.equal(status.verificationCommands.includes(command), true, command);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'exact successful prefix of length k at most F')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineInputFramer is one literal finite machine for every raw bitstring')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineOutputHandoff is one literal finite machine for an already represented internal tape')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineTerminalBridge preserves the earlier ordinary-input trace')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'stuck-endpoint timeout')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineStateNamespace remains the injective renaming and lookup-isolation prerequisite')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineSequentialStateNamespace nests two complete component machines')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineSequentialCompiler composes both exact executions')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineStageBridges proves exact framer-to-simulator and accept/reject-to-handoff launches')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'TerminalOutputPacker is a literal finite work machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineTerminalBridge is one literal extended finite work machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelinePairedCompiler remains the sharper canonical-pair theorem')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineCompiler extracts that prefix internally on every raw bitstring')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevinRawTapeBridge proves that the finite tableau semantics exactly represent ordinary two-sided raw Tape execution')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevinFormulaSize bounds the actual canonical unary-indexed CNF bitstring')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevinFormulaSchedule allocates exact rectangular constraint')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevinFormulaCursor decodes constraint')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderInputLength is a fixed 19-rule work machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderTokenAppender remains the independently audited fixed 59-rule')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFirstTokenPrefix is one literal 184-rule finite work machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderCompleteHeader compiles the verifier-fixed formula-width NatPolynomial')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderBodyStartPrefix composes the complete width-header machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFirstLiteralPrefix composes the complete body-start machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFirstClausePrefix composes the complete first-literal machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderDynamicTokenCursorStep composes that complete first-clause machine')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFirstClausePaddingRun composes the preceding one-slot cursor step')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondClauseSeparatorStep composes the complete first-clause padding run')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondClauseFirstLiteralPrefix composes the complete second-clause separator prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondClauseSecondLiteralPrefix composes the complete clause-two first-literal prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondClausePrefix composes the complete clause-two second-literal prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondClausePaddingRun composes the complete second-clause prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderThirdClauseSeparatorStep composes the complete second-clause padding run')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderThirdClauseFirstLiteralPrefix composes the complete third-clause separator prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderThirdClauseSecondLiteralPrefix composes the complete third-clause first-literal prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderThirdClausePrefix composes the complete third-clause second-literal prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderThirdClausePaddingRun composes the complete third-clause prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFourthClauseSeparatorStep composes the complete third-clause padding run')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFourthClauseFirstLiteralPrefix composes the complete fourth-clause separator prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFourthClauseSecondLiteralPrefix composes the complete fourth-clause first-literal prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFourthClausePrefix composes the fourth-clause second-literal prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFourthClausePaddingRun composes the complete fourth-clause prefix')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFifthClausePaddingRun composes the complete fourth-clause padding run')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderFirstConstraintPaddingRun composes the complete fifth-clause padding run')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintSeparatorStep composes the complete first-constraint padding run')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFirstLiteralSignStep composes the complete second-constraint separator step')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep composes the complete second-constraint first-literal sign step')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep composes the complete second-constraint first-literal first-unary-unit step')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep composes the complete second-constraint first-literal second-unary-unit step')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep composes the complete second-constraint first-literal third-unary-unit step')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep composes the complete first-literal terminator')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep composes the complete width-selected successor-token predecessor')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep composes the complete first padding-or-unary-opportunity predecessor')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep composes the complete second padding-or-unary-opportunity predecessor')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep composes the complete third padding-or-unary-opportunity predecessor')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep composes the complete fourth padding-or-unary-opportunity predecessor')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep composes the complete fifth padding-or-terminator-opportunity predecessor')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep composes the complete sixth padding-or-opening-unary-opportunity predecessor')), true);
});

test('formal status records the exhaustive direct-wire reference minimum conservatively', async () => {
  const status = await currentStatus0();

  assert.equal(status.publicSurfaceBaselineCoordinate, 'PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121');
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
  assert.equal(status.leanLockedNANDDirectCandidatesFormalized, true);
  assert.equal(status.leanLockedNANDDirectAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDInternalMacroConstantsAbsent, true);
  assert.equal(status.leanDirectWireOutputLowerBoundFormalized, true);
  assert.equal(status.leanDirectWireBaselineAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDSourceDerivedCountsFormalized, true);
  assert.equal(status.leanLockedNANDBaselineAccountingFormalized, true);
  assert.equal(status.leanLockedNANDBaselineAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDConditionalSquareBaselineExactnessFormalized, true);
  assert.equal(status.leanLockedNANDLocalBaselineConditionsFormalized, true);
  assert.equal(status.leanLockedNANDLocalSquareBaselineExactnessFormalized, true);
  assert.equal(status.leanLockedNANDLocalBaselineAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDConditionalThresholdBoundaryFormalized, true);
  assert.equal(status.leanLockedNANDConditionalResidualSlackAtMostFourFormalized, true);
  assert.equal(status.leanLockedNANDThresholdBoundaryAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDThresholdBoundaryScope, 'proof-bearing-typed-candidate-and-semantic-premises-only');
  assert.equal(status.leanLockedNANDThresholdBoundaryPremisesInstantiated, true);
  assert.equal(status.leanLockedNANDGlobalBaselineDistinctFormalized, true);
  assert.equal(status.leanLockedNANDGlobalBaselineDistinctAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDGlobalBaselineDistinctAuditedDeclarationCount, 5);
  assert.equal(status.leanLockedNANDGlobalBaselineDistinctScope,
    'arbitrary-finite-topological-nand-circuits-global-baseline-output-conditions-and-exact-reference-minimum');
  assert.equal(status.leanLockedNANDUnsatisfiableFinalZeroFormalized, true);
  assert.equal(status.leanLockedNANDUnsatisfiableFinalZeroAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDUnsatisfiableFinalZeroAuditedDeclarationCount, 2);
  assert.equal(status.leanLockedNANDUnsatisfiableFinalZeroScope,
    'arbitrary-finite-topological-nand-circuits-whole-carrier-unsatisfiable-final-zero-and-exact-reference-minimum');
  assert.equal(status.leanLockedNANDCarrierLayoutFormalized, true);
  assert.equal(status.leanLockedNANDTraceEquivalenceFormalized, true);
  assert.equal(status.leanLockedNANDCarrierTraceAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDCarrierTraceAuditedDeclarationCount, 71);
  assert.equal(status.leanLockedNANDCarrierTraceScope,
    'arbitrary-finite-topological-nand-circuits-carrier-separation-and-trace-equivalence');
  assert.equal(status.leanLockedNANDGlobalCandidateAssemblyFormalized, true);
  assert.equal(status.leanLockedNANDGlobalBaselineCandidateFormalized, true);
  assert.equal(status.leanLockedNANDFullCandidateFormalized, true);
  assert.equal(status.leanLockedNANDGlobalCandidateAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDGlobalCandidateAuditedDeclarationCount, 71);
  assert.equal(status.leanLockedNANDGlobalCandidateScope,
    'arbitrary-finite-topological-nand-circuits-exact-baseline-and-four-gate-extension');
  assert.equal(status.leanLockedNANDDerivedFinalOutputLawsFormalized, true);
  assert.equal(status.leanLockedNANDResidualSlackAtMostFourFormalized, true);
  assert.equal(status.leanLockedNANDSatisfiableFinalConditionsFormalized, true);
  assert.equal(status.leanLockedNANDGlobalSemanticThresholdFormalized, true);
  assert.equal(status.leanLockedNANDGlobalSemanticThresholdAxiomAuditPassed, true);
  assert.equal(status.leanLockedNANDGlobalSemanticThresholdAuditedDeclarationCount, 8);
  assert.equal(status.leanLockedNANDGlobalSemanticThresholdScope,
    'arbitrary-finite-topological-nand-circuits-complete-six-field-premises-and-typed-semantic-threshold');
  for (const field of [
    'leanConcreteLockedNANDCanonicalEncodingFormalized',
    'leanConcreteLockedNANDNormalizationSemanticsFormalized',
    'leanConcreteLockedNANDCompleteCandidateCodecFormalized',
    'leanConcreteLockedNANDEncodedSemanticReductionFormalized',
    'leanConcreteLockedNANDEncodedSemanticReductionAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanConcreteLockedNANDEncodedSemanticReductionAuditedDeclarationCount,
    48,
  );
  assert.equal(
    status.leanConcreteLockedNANDEncodedSemanticReductionScope,
    'strict-version-zero-codec-direct-normalization-semantics-complete-candidate-bytes-and-fail-closed-semantic-reduction',
  );
  for (const field of [
    'leanConcreteLockedNANDParserMachineFormalized',
    'leanConcreteLockedNANDParserAxiomAuditPassed',
    'leanConcreteLockedNANDParserAllInputExactFormalized',
    'leanConcreteLockedNANDParserExactOutputFormalized',
    'leanConcreteLockedNANDParserCompiledNonTimeoutFormalized',
    'leanConcreteLockedNANDParserPolynomialTimeMachineFormalized',
    'leanConcreteLockedNANDParserPolynomialTimeFunctionFormalized',
    'leanConcreteLockedNANDParserRawRefinementFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanConcreteLockedNANDParserAuditedDeclarationCount, 380);
  assert.equal(
    status.leanConcreteLockedNANDParserScope,
    'literal-228-state-2052-rule-strict-version-zero-all-input-parser-byte-preserving-or-empty-with-compiled-cubic-bound',
  );
  for (const field of [
    'leanConcreteLockedNANDEmitterMachineFormalized',
    'leanConcreteLockedNANDEmitterAxiomAuditPassed',
    'leanConcreteLockedNANDEmitterAllInputExactFormalized',
    'leanConcreteLockedNANDEmitterExactTargetBytesFormalized',
    'leanConcreteLockedNANDEmitterCompiledNonTimeoutFormalized',
    'leanConcreteLockedNANDEmitterPolynomialTimeMachineFormalized',
    'leanConcreteLockedNANDEmitterPolynomialTimeFunctionFormalized',
    'leanConcreteLockedNANDEmitterRawRefinementFormalized',
    'leanConcreteLockedNANDEmitterStrictParserCompositionFormalized',
    'leanConcreteLockedNANDEmitterOutputSizeBoundFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanConcreteLockedNANDEmitterAuditedDeclarationCount,
    3295,
  );
  assert.equal(
    status.leanConcreteLockedNANDEmitterScope,
    'literal-1387921-rule-grammar-only-all-input-target-emitter-with-strict-parser-composition-polynomial-bounds-and-recursive-raw-refinement',
  );
  for (const field of [
    'leanConcreteLockedNANDPolynomialReductionFormalized',
    'leanConcreteLockedNANDPolynomialReductionAxiomAuditPassed',
    'leanConcreteLockedNANDPolynomialReductionExactFunctionFormalized',
    'leanConcreteLockedNANDPolynomialReductionExactOutputFormalized',
    'leanConcreteLockedNANDPolynomialReductionLanguageEquivalenceFormalized',
    'leanConcreteLockedNANDPolynomialReductionWitnessFormalized',
    'leanConcreteLockedNANDPolynomialReductionRawRefinementFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanConcreteLockedNANDPolynomialReductionAuditedDeclarationCount,
    16,
  );
  assert.equal(
    status.leanConcreteLockedNANDPolynomialReductionScope,
    'strict-version-zero-parser-emitter-polynomial-reduction-with-exact-language-equivalence-and-recursive-raw-refinement',
  );
  for (const field of [
    'leanConcreteCNFToNANDSemanticCompilerFormalized',
    'leanConcreteCNFToNANDSemanticCompilerAxiomAuditPassed',
    'leanConcreteCNFToNANDExactCodecCanonicalityFormalized',
    'leanConcreteCNFToNANDTypedTopologicalCompilationFormalized',
    'leanConcreteCNFToNANDWellFormedOutputFormalized',
    'leanConcreteCNFToNANDExactSemanticsFormalized',
    'leanConcreteCNFToNANDEdgeSemanticsFormalized',
    'leanConcreteCNFToNANDExactGateCountFormalized',
    'leanConcreteCNFToNANDPolynomialOutputSizeBoundFormalized',
    'leanConcreteCNFToNANDAllBitstringFailClosedFormalized',
    'leanConcreteCNFToNANDLockedThresholdCompositionFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanConcreteCNFToNANDSemanticCompilerAuditedDeclarationCount,
    68,
  );
  assert.equal(
    status.leanConcreteCNFToNANDSemanticCompilerScope,
    'strict-canonical-cnf-to-intrinsically-topological-nand-semantic-compiler-with-exact-gate-count-quadratic-output-bound-and-all-bitstring-fail-closed-equivalence',
  );
  for (const field of [
    'leanConcreteCNFToNANDFiniteMachineFormalized',
    'leanConcreteCNFToNANDPolynomialTimeFunctionFormalized',
    'leanConcreteCNFToNANDPolynomialReductionFormalized',
    'leanConcreteCNFToNANDPolynomialReductionAxiomAuditPassed',
    'leanConcreteCNFToNANDAllInputExactFormalized',
    'leanConcreteCNFToNANDExactMachineOutputFormalized',
    'leanConcreteCNFToNANDCompiledNonTimeoutFormalized',
    'leanConcreteCNFToNANDRawRefinementFormalized',
    'leanConcreteCNFToNANDDirectReductionFormalized',
    'leanConcreteCNFToNANDLockedReductionCompositionFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanConcreteCNFToNANDPolynomialReductionAuditedDeclarationCount,
    1316,
  );
  assert.equal(
    status.leanConcreteCNFToNANDPolynomialReductionScope,
    'fixed-135070-rule-three-node-all-bitstring-cnf-to-nand-compiler-with-exact-output-polynomial-time-function-direct-reduction-locked-threshold-composition-and-recursive-raw-refinement',
  );
  assert.equal(status.leanLockedNANDPolynomialBuilderFormalized, true);
  assert.equal(status.leanCompatibleReplacementFormalized, false);
  assert.equal(status.leanGlobalSlackLawFormalized, false);
  assert.equal(status.leanLockedNANDBuilderFormalized, true);
  assert.equal(status.leanLockedNANDThresholdFormalized, true);
  assert.equal(status.leanResidualRoutesListedGainScanFormalized, true);
  assert.equal(status.leanResidualRoutesAxiomAuditPassed, true);
  assert.equal(status.leanResidualRoutesGainSoundnessFormalized, true);
  assert.equal(status.leanResidualRoutesStrictResidualDescentFormalized, true);
  assert.equal(status.leanResidualRoutesExactResultProofBearing, true);
  assert.equal(status.leanResidualRoutesZeroSlackResultProofBearing, true);
  assert.equal(status.leanResidualRoutesUnresolvedFailClosed, true);
  assert.equal(status.leanResidualRoutesScope, 'explicit-caller-supplied-finite-candidate-list');
  assert.equal(status.leanResidualRoutesCandidateListCompletenessFormalized, false);
  assert.equal(status.leanResidualRoutesGlobalGainCompletenessFormalized, false);
  assert.equal(status.leanResidualGainChainVerifierFormalized, true);
  assert.equal(status.leanResidualGainChainAxiomAuditPassed, true);
  assert.equal(status.leanResidualGainChainSemanticInvariantFormalized, true);
  assert.equal(status.leanResidualGainChainSlackIterationBoundFormalized, true);
  assert.equal(status.leanLockedNANDGainIterationsAtMostFourFormalized, true);
  assert.equal(
    status.leanResidualGainChainScope,
    'all-finite-proof-bearing-or-executably-verified-strict-equivalent-gain-chains-with-locked-family-four-step-specialization',
  );
  assert.equal(status.leanResidualGainChainPolynomialRuntimeFormalized, false);
  assert.equal(status.leanResidualGainStoppingSpecificationFormalized, true);
  assert.equal(status.leanResidualGainStoppingAxiomAuditPassed, true);
  assert.equal(status.leanResidualGainReferenceMinimumWitnessFormalized, true);
  assert.equal(status.leanResidualGainPositiveIffGlobalStrictGainFormalized, true);
  assert.equal(status.leanResidualGainZeroIffGlobalNoStrictGainFormalized, true);
  assert.equal(status.leanResidualGainSemanticMinimumIffGlobalNoStrictGainFormalized, true);
  assert.equal(status.leanResidualGainChainGlobalStoppingConsequenceFormalized, true);
  assert.equal(status.leanResidualGainChainExactMinimumPackagingFormalized, true);
  assert.equal(
    status.leanResidualGainStoppingScope,
    'all-finite-direct-wire-implementations-with-global-strict-equivalent-gain-quantification-and-proof-supplied-chain-endpoint-stopping',
  );
  assert.equal(status.leanResidualTerminalFullBridgeFormalized, true);
  assert.equal(status.leanResidualTerminalFullBridgeAxiomAuditPassed, true);
  assert.equal(status.leanResidualTerminalizationExactFormalized, true);
  assert.equal(status.leanResidualTerminalFullMinimumSpecificationFormalized, true);
  assert.equal(status.leanResidualTerminalMuBridgeFormalized, true);
  assert.equal(status.leanResidualWholeSpanPositiveWitnessIffFormalized, true);
  assert.equal(status.leanResidualWholeSpanStrictDescentFormalized, true);
  assert.equal(status.leanResidualWholeSpanZeroAbsenceIffFormalized, true);
  assert.equal(
    status.leanResidualTerminalFullBridgeScope,
    'all-finite-direct-wire-implementations-with-complete-multi-output-semantics-and-exhaustive-reference-minimum-witnesses',
  );
  assert.equal(status.leanResidualTerminalQuotientCarrierFormalized, true);
  assert.equal(status.leanResidualTerminalModeFirewallFormalized, true);
  assert.equal(status.leanResidualTerminalModeFirewallAxiomAuditPassed, true);
  assert.equal(status.leanResidualTerminalProfileProjectionExactFormalized, true);
  assert.equal(status.leanResidualTerminalCheckedFullLiftFormalized, true);
  assert.equal(status.leanResidualTerminalQuotientEqualityNotConstructiveFormalized, true);
  assert.equal(status.leanResidualTerminalObligationDischargePreservedFormalized, true);
  assert.equal(
    status.leanResidualTerminalModeFirewallScope,
    'all-finite-direct-wire-implementations-with-computed-finite-profile-observers-and-explicit-forgetful-projections',
  );
  for (const field of [
    'leanResidualProjectionMinimumFormalized',
    'leanResidualProjectionMinimumAxiomAuditPassed',
    'leanResidualProjectionMinimumExecutableFullScanFormalized',
    'leanResidualProjectionMinimumExecutableQuotientScanFormalized',
    'leanResidualProjectionMinimumAttainmentFormalized',
    'leanResidualProjectionMinimumUniversalLowerBoundsFormalized',
    'leanResidualProjectionMinimumMonotonicityFormalized',
    'leanResidualProjectionDefectDecompositionFormalized',
    'leanResidualProjectionDefectZeroIffCheckedLiftAtMinimumFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualProjectionMinimumScope,
    'all-finite-direct-wire-implementations-with-computed-finite-profile-observers-explicit-projections-and-exhaustive-search-through-the-current-gate-count',
  );
  for (const field of [
    'leanResidualProjectionTransferFormalized',
    'leanResidualProjectionTransferAxiomAuditPassed',
    'leanResidualProjectionTransferSignedDeltasFormalized',
    'leanResidualProjectionTransferIdentityFormalized',
    'leanResidualProjectionTransferConstantCutFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualProjectionTransferScope,
    'all-finite-direct-wire-four-corner-terminal-profile-families-sharing-one-computed-observer-and-one-explicit-projection',
  );
  for (const field of [
    'leanResidualTerminalSaturationFormalized',
    'leanResidualTerminalSaturationAxiomAuditPassed',
    'leanResidualTerminalPrimitiveUniverseFormalized',
    'leanResidualTerminalSaturationExtensiveFormalized',
    'leanResidualTerminalSaturationLeastFormalized',
    'leanResidualTerminalSaturationMonotoneFormalized',
    'leanResidualTerminalSaturationIdempotentFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalSaturationScope,
    'all-finite-terminal-primitive-record-universes-with-explicit-boolean-rule-tagged-dependencies',
  );
  for (const field of [
    'leanResidualTerminalExecutableSaturationFormalized',
    'leanResidualTerminalPhysicalSupportCompletionFormalized',
    'leanResidualTerminalPhysicalBoundaryFormalized',
    'leanResidualTerminalPhysicalInterfaceFormalized',
    'leanResidualTerminalPhysicalCompatibilityFormalized',
    'leanResidualTerminalPhysicalSupportCompletionAxiomAuditPassed',
    'leanResidualTerminalSupportExtractionFormalized',
    'leanResidualTerminalOpenSemanticsFormalized',
    'leanResidualTerminalInducedRecoveryFormalized',
    'leanResidualTerminalSupportExtractionAxiomAuditPassed',
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
    'leanResidualTerminalSupportSquareClosureFormalized',
    'leanResidualTerminalSupportSquareMeetJoinExactFormalized',
    'leanResidualTerminalSupportSquarePhysicalCompatibilityFormalized',
    'leanResidualTerminalSupportSquareSemanticExtractionFormalized',
    'leanResidualTerminalSupportSquareClosureAxiomAuditPassed',
    'leanResidualTerminalSupportCompletionFormalized',
    'leanResidualTerminalGovernedSupportCompletionFormalized',
    'leanResidualTerminalGovernedProfilePartitionFormalized',
    'leanResidualTerminalGovernedSupportCompletionAxiomAuditPassed',
    'leanResidualTerminalFrontierPushoutFormalized',
    'leanResidualTerminalFrontierBoundaryGlueExactFormalized',
    'leanResidualTerminalFrontierInterfaceGlueExactFormalized',
    'leanResidualTerminalFrontierProfileGlueExactFormalized',
    'leanResidualTerminalFrontierInternalizationFormalized',
    'leanResidualTerminalFrontierPushoutAxiomAuditPassed',
    'leanResidualTerminalProjectionSquareFormalized',
    'leanResidualTerminalProjectionPhysicalInvariantFormalized',
    'leanResidualTerminalProjectionProfileExactFormalized',
    'leanResidualTerminalProjectionMeetJoinCommuteFormalized',
    'leanResidualTerminalProjectionPushoutCommuteFormalized',
    'leanResidualTerminalProjectionSquareAxiomAuditPassed',
    'leanResidualTerminalSideTightMinimumArithmeticFormalized',
    'leanResidualTerminalSideTightSignedSlackIdentityFormalized',
    'leanResidualTerminalSideTightFailClosedGateFormalized',
    'leanResidualTerminalSideTightCanonicalFullBasisFormalized',
    'leanResidualTerminalSideTightCanonicalQuotientBasisFormalized',
    'leanResidualTerminalSideTightMinimumAxiomAuditPassed',
    'leanResidualTerminalFourCornerCarrierTransportFormalized',
    'leanResidualTerminalFourCornerCarrierExactEndpointsFormalized',
    'leanResidualTerminalFourCornerCarrierInjectiveCoordinatesFormalized',
    'leanResidualTerminalFourCornerCarrierProfileTransportFormalized',
    'leanResidualTerminalFourCornerCarrierFailClosedPhysicalTransportFormalized',
    'leanResidualTerminalFourCornerCarrierAxiomAuditPassed',
    'leanResidualTerminalFourCornerOptimaCarrierCompatibleFormalized',
    'leanResidualTerminalFourCornerOptimaFaithfulAmbientizationFormalized',
    'leanResidualTerminalFourCornerOptimaReferenceMinimumPreservedFormalized',
    'leanResidualTerminalFourCornerOptimaLocalizedMinimaFormalized',
    'leanResidualTerminalFourCornerOptimaSharedObserverProjectionFormalized',
    'leanResidualTerminalFourCornerOptimaAxiomAuditPassed',
    'leanResidualTerminalFourCornerOptimumLocalRouteClassifierFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSoundnessFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumSideTightCompletionUnderRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumExactCompletionValuesFormalized',
    'leanResidualTerminalFourCornerOptimumPromotionFirewallRetained',
    'leanResidualTerminalFourCornerSideTightCompletionAxiomAuditPassed',
    'leanResidualTerminalFourCornerArbitraryFamilyCoherenceFormalized',
    'leanResidualTerminalFourCornerExactMinimumFamilyEnumerated',
    'leanResidualTerminalFourCornerTightBasisFamilyComplete',
    'leanResidualTerminalFourCornerSignedTightBasisMaximumFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumEqualsDeltaFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumAxiomAuditPassed',
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalSquareStructuralCompatibilityFormalized',
    'leanResidualTerminalSquareFrontierPushoutFormalized',
    'leanResidualTerminalSquareSharedQuantityCarrierFormalized',
    'leanResidualTerminalSquareLocalConclusionUnderRouteSilenceFormalized',
    'leanResidualTerminalSquareFailClosedRouteDichotomyFormalized',
    'leanResidualTerminalSquareLegitimacyAxiomAuditPassed',
    'leanResidualTerminalCoherentFourCornerBasisFormalized',
    'leanResidualTerminalComputedBCELAnchorNucleusFormalized',
    'leanResidualTerminalBCELMinimumPositiveNucleusFormalized',
    'leanResidualTerminalBCELAnchorAlgebraFormalized',
    'leanResidualTerminalBCELCutDefectFirewallFormalized',
    'leanResidualTerminalBCELCutRouteDichotomyFormalized',
    'leanResidualTerminalBCELConstantCutConclusionFormalized',
    'leanResidualTerminalBCELAnchorNucleusAxiomAuditPassed',
    'leanResidualTerminalSaturationPositivityFirewallFormalized',
    'leanResidualTerminalSaturationPositivityFirewallAxiomAuditPassed',
    'leanResidualTerminalCandidateSaturationFormalized',
    'leanResidualTerminalSaturationCostBalanceFormalized',
    'leanResidualTerminalFirstNontransparentStepFormalized',
    'leanResidualTerminalSaturationCostBalanceAxiomAuditPassed',
    'leanResidualTerminalInterfaceExposureRoutingFormalized',
    'leanResidualTerminalFiniteInterfaceExposureRoutesToEFormalized',
    'leanResidualTerminalInterfaceExposureZeroCostRetractFormalized',
    'leanResidualTerminalFirstInterfaceExposureRouteFormalized',
    'leanResidualTerminalInterfaceExposureRoutingAxiomAuditPassed',
    'leanResidualTerminalOriginKernelObligationRoutingFormalized',
    'leanResidualTerminalFiniteOriginKernelObligationClosureRoutedFormalized',
    'leanResidualTerminalFirstOriginKernelObligationRouteFormalized',
    'leanResidualTerminalOriginKernelObligationRoutingAxiomAuditPassed',
    'leanResidualTerminalFiniteSaturatePositiveCompositionFormalized',
    'leanResidualTerminalFiniteSaturatePositiveCompositionAxiomAuditPassed',
    'leanResidualTerminalRankWFFormalized',
    'leanResidualTerminalRankWFAxiomAuditPassed',
    'leanResidualTerminalBN3RequestEnvelopeFormalized',
    'leanResidualTerminalBN3RequestEnvelopeAxiomAuditPassed',
    'leanResidualTerminalBN4ActivationCancellationFormalized',
    'leanResidualTerminalBN4ActivationCancellationAxiomAuditPassed',
    'leanResidualTerminalBN5FullShadowLocalizationFormalized',
    'leanResidualTerminalBN5FullShadowLocalizationAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalPhysicalSupportCompletionScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-finite-seed-lists',
  );
  assert.equal(
    status.leanResidualTerminalSupportExtractionScope,
    'all-finite-direct-wire-candidates-terminal-record-lists-boundary-valuations-and-interface-coordinates',
  );
  assert.equal(
    status.leanResidualTerminalProperSupportScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-canonical-primitive-record-seeds-with-exhaustive-reference-minimum-local-gain',
  );
  assert.equal(
    status.leanResidualTerminalSupportSquareClosureScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-pairs-of-finite-terminal-seeds',
  );
  assert.equal(
    status.leanResidualTerminalGovernedSupportCompletionScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-finite-seed-lists-and-saturated-support-square-corners',
  );
  assert.equal(
    status.leanResidualTerminalFrontierPushoutScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-computed-saturated-support-squares',
  );
  assert.equal(
    status.leanResidualTerminalProjectionSquareScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-saturated-support-squares-and-forgetful-terminal-projections',
  );
  assert.equal(
    status.leanResidualTerminalSideTightMinimumScope,
    'all-finite-terminal-projection-four-corner-families-and-independently-attained-full-and-quotient-minimum-bases',
  );
  assert.equal(
    status.leanResidualTerminalFourCornerCarrierScope,
    'all-finite-computed-saturated-terminal-support-squares-and-canonical-physical-profile-transport-coordinates',
  );
  assert.equal(
    status.leanResidualTerminalFourCornerOptimaCarrierScope,
    'all-finite-computed-saturated-terminal-support-squares-one-reversible-ambient-carrier-and-shared-observer-projection',
  );
  assert.equal(
    status.leanResidualTerminalFourCornerSideTightCompletionScope,
    'all-finite-computed-terminal-support-squares-observers-and-full-or-quotient-modes-side-tight-coherent-completion-under-exact-local-route-silence',
  );
  assert.equal(
    status.leanResidualTerminalFourCornerTightBasisMaximumScope,
    'all-finite-computed-terminal-support-squares-observers-and-full-or-quotient-modes-complete-tight-basis-family-and-signed-maximum-under-exact-local-route-silence',
  );
  assert.equal(
    status.leanResidualTerminalCoherentFourCornerBasisScope,
    'conditional-on-exact-mode-appropriate-local-route-silence-not-universal-bn2-square-legitimacy',
  );
  assert.equal(
    status.leanResidualTerminalSquareLegitimacyScope,
    'all-finite-computed-terminal-support-squares-explicit-terminal-dependency-systems-direct-wire-candidates-observers-and-forgetful-projections-with-local-route-silence-or-proof-bearing-first-failure',
  );
  assert.equal(
    status.leanResidualTerminalBCELAnchorNucleusScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-governed-proper-positive-supports-forgetful-projections-executable-ambient-observers-and-positive-whole-support-projection-defect',
  );
  assert.equal(
    status.leanResidualTerminalSaturationPositivityFirewallScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-governed-proper-positive-supports-forgetful-projections-and-executable-ambient-observers-total-zero-or-positive-whole-support-projection-defect-classification',
  );
  assert.equal(
    status.leanResidualTerminalSaturationCostBalanceScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-candidate-derived-dependency-system-rule-labelled-exact-cost-balance-or-first-nontransparent-step',
  );
  assert.equal(
    status.leanResidualTerminalInterfaceExposureRoutingScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-candidate-derived-interface-consumer-transparent-or-local-e-route-with-exact-first-failure',
  );
  assert.equal(
    status.leanResidualTerminalOriginKernelObligationRoutingScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-candidate-derived-origin-kernel-obligation-closures-with-exact-safety-or-first-route',
  );
  assert.equal(
    status.leanResidualTerminalFiniteSaturatePositiveCompositionScope,
    'all-finite-direct-wire-candidates-executable-observers-forgetful-projections-proof-bearing-positive-full-slack-candidate-bcel-anchor-problems-total-finite-saturate-positive-composition',
  );
  assert.equal(
    status.leanResidualTerminalRankWFScope,
    'fixed-ten-coordinate-natural-lexicographic-order-executable-comparison-accessibility-induction-and-kernel-well-foundedness',
  );
  assert.equal(
    status.leanResidualTerminalBN3RequestEnvelopeScope,
    'successful-computed-finite-bcel-anchor-nuclei-canonical-stable-request-identities-exact-singleton-minimal-consumers-duplicate-free-incidence-and-jointly-side-tight-full-or-quotient-basis-family',
  );
  assert.equal(
    status.leanResidualTerminalBN4ActivationCancellationScope,
    'successful-computed-finite-bn3-envelope-explicit-typed-cell-ledgers-activation-exact-complete-key-same-key-cancellation-and-exact-integer-mass-residuals',
  );
  assert.equal(
    status.leanResidualTerminalBN5FullShadowLocalizationScope,
    'all-finite-exact-coordinate-negative-unit-refinements-computed-cut-silence-complete-multiplicity-coverage-or-strict-hall-deficit-with-local-x1-nonsilence',
  );
  for (const field of [
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinLoopExactnessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.leanResidualBandMinimizerFormalized, false);
  assert.equal(status.nonClaims.some((entry) => entry.includes('direct-wire NAND semantics layer does not by itself prove enumeration')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('reference-minimum computation has no polynomial-runtime claim')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('concrete serial framed-context construction')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('do not by themselves prove the later global semantic threshold')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('baseline coordinates remain present alongside one final coordinate')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('honest source-derived baseline/displayed counts are 86/90')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('is not the report threshold theorem')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('now has residual slack at most four')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('arbitrary satisfiable proposition and baseline natural number')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('complete only for the explicit finite implementation list')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('empty-list scan is formally shown')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('never manufactured by the executable gain scanner')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('number of accepted gains is at most the starting residual slack')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('iteration-count bound only')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('positive residual slack is equivalent to the existence of a strict equivalent gain')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('requires a proof of global no-gain')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('terminal full-carrier bridge preserves every input/output coordinate')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('quotient carrier or mode firewall')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('mismatch at any forgotten coordinate')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('terminal and forgetful-projection only')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('exhaustively scans every direct-wire candidate size')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('terminal minima are finite reference computations')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('signed four-corner balance law')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('arithmetic over supplied corners')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('reflexive transitive closure is extensive')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('does not extract dependencies from an arbitrary circuit')), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-semantics0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-enumerator0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-nand-reference-minimum0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-baseline0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-threshold-boundary0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-routes0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-gain-chain0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-gain-stopping0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-full-bridge0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-mode-firewall0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-projection-minimum0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-projection-transfer0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-saturation0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDTruthTableAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDCompositionAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDDirectAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPDirectWireBaselineAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDBaselineAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDLocalBaselineAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDGlobalCandidatesAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPLockedNANDGlobalCandidates.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDGlobalBaselineDistinctAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPLockedNANDGlobalBaselineDistinct.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-global-baseline-distinct0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDGlobalUnsatisfiableFinalZeroAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPLockedNANDGlobalUnsatisfiableFinalZero.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-global-unsatisfiable-final-zero0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDGlobalSemanticThresholdAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPLockedNANDGlobalSemanticThreshold.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-locked-nand-global-semantic-threshold0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPConcreteLockedNANDSourceParserAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPConcreteLockedNANDSourceParser.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-concrete-locked-nand-source-parser0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPConcreteLockedNANDTargetEmitterAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPConcreteLockedNANDTargetEmitter.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-concrete-locked-nand-target-emitter0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPConcreteLockedNANDPolynomialReductionAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPConcreteLockedNANDPolynomialReduction.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-concrete-locked-nand-polynomial-reduction0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPConcreteCNFToNANDAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPConcreteCNFToNAND.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-concrete-cnf-to-nand0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualRoutesAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualGainChainAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDResidualGainBoundAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualGainChain.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualGainStoppingAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualGainStopping.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFullBridgeAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFullBridge.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalModeFirewallAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalModeFirewall.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProjectionMinimumAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProjectionMinimum.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProjectionTransferAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProjectionTransfer.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSaturationAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSaturation.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPhysicalSupportCompletionAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPhysicalSupportCompletion.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-physical-support-completion0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSupportExtractionAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSupportExtraction.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-support-extraction0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProperSupportAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProperSupport.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-proper-support0.test.mjs'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSupportSquareClosureAxiomAudit.lean'), true);
  assert.equal(status.verificationCommands.includes('lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSupportSquareClosure.lean'), true);
  assert.equal(status.verificationCommands.includes('node --test audits/lean-residual-terminal-support-square-closure0.test.mjs'), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('canonical finite primitive-record seed universe')), true);
  assert.equal(status.nonClaims.some((entry) => entry.includes('exact closed left, right, meet, and join record sets')), true);
  assert.deepEqual(status.lockedNANDThresholdHostileReviewLemmaInventory, [
    'DirectWireOutputLowerBound',
    'MacroDistinct',
    'TraceEquivalence',
    'ZeroOutputConvention',
    'FinalLockSeparation',
  ]);
  assert.deepEqual(status.leanLockedNANDThresholdPremiseInventory, [
    'baselineCandidate',
    'fullCandidate',
    'baselineConditions',
    'initialOutputsPreserved',
    'unsatisfiableFinalZero',
    'satisfiableFinalConditions',
  ]);
  assert.deepEqual(status.leanLockedNANDThresholdMissingInstantiationInventory, []);
  assert.equal(status.remainingBlockers.includes('Formal.LockedNANDThreshold'), false);
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

test('formal reconstruction status rejects weakened or broadened direct CNF status', async () => {
  for (const [field, value] of [
    ['leanConcreteCNFVerifierCorrectnessFormalized', false],
    ['leanConcreteCNFVerifierNoTimeoutFormalized', false],
    ['leanConcreteCNFVerifierAxiomAuditPassed', false],
    ['leanConcreteCNFWorkAxiomAuditPassed', false],
    ['leanConcreteCNFSATMembershipFormalized', false],
    ['leanConcreteCNFSATInPFormalized', true],
    ['leanConcreteCNFNPCompletenessFormalized', true],
    ['leanConcreteCNFSATMembershipTheorem', 'PNP.Main.p_eq_np'],
  ]) {
    const status = await currentStatus0();
    status[field] = value;
    const out = await CheckFormalReconstructionStatus0({
      writeOutput: false,
      statusOverride: status,
      siteOverride: status,
    });
    assert.equal(out.tag, 'reject', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
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
    'leanLockedNANDDirectCandidatesFormalized',
    'leanLockedNANDDirectAxiomAuditPassed',
    'leanLockedNANDInternalMacroConstantsAbsent',
    'leanDirectWireOutputLowerBoundFormalized',
    'leanDirectWireBaselineAxiomAuditPassed',
    'leanLockedNANDSourceDerivedCountsFormalized',
    'leanLockedNANDBaselineAccountingFormalized',
    'leanLockedNANDBaselineAxiomAuditPassed',
    'leanLockedNANDConditionalSquareBaselineExactnessFormalized',
    'leanLockedNANDLocalBaselineConditionsFormalized',
    'leanLockedNANDLocalSquareBaselineExactnessFormalized',
    'leanLockedNANDLocalBaselineAxiomAuditPassed',
    'leanLockedNANDConditionalThresholdBoundaryFormalized',
    'leanLockedNANDConditionalResidualSlackAtMostFourFormalized',
    'leanLockedNANDThresholdBoundaryAxiomAuditPassed',
    'leanLockedNANDCarrierLayoutFormalized',
    'leanLockedNANDTraceEquivalenceFormalized',
    'leanLockedNANDCarrierTraceAxiomAuditPassed',
    'leanLockedNANDGlobalCandidateAssemblyFormalized',
    'leanLockedNANDGlobalBaselineCandidateFormalized',
    'leanLockedNANDFullCandidateFormalized',
    'leanLockedNANDGlobalCandidateAxiomAuditPassed',
    'leanLockedNANDGlobalBaselineDistinctFormalized',
    'leanLockedNANDGlobalBaselineDistinctAxiomAuditPassed',
    'leanLockedNANDUnsatisfiableFinalZeroFormalized',
    'leanLockedNANDUnsatisfiableFinalZeroAxiomAuditPassed',
    'leanLockedNANDThresholdBoundaryPremisesInstantiated',
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDSatisfiableFinalConditionsFormalized',
    'leanLockedNANDGlobalSemanticThresholdFormalized',
    'leanLockedNANDGlobalSemanticThresholdAxiomAuditPassed',
    'leanConcreteLockedNANDParserMachineFormalized',
    'leanConcreteLockedNANDParserAxiomAuditPassed',
    'leanConcreteLockedNANDParserAllInputExactFormalized',
    'leanConcreteLockedNANDParserExactOutputFormalized',
    'leanConcreteLockedNANDParserCompiledNonTimeoutFormalized',
    'leanConcreteLockedNANDParserPolynomialTimeMachineFormalized',
    'leanConcreteLockedNANDParserPolynomialTimeFunctionFormalized',
    'leanConcreteLockedNANDParserRawRefinementFormalized',
    'leanConcreteLockedNANDEmitterMachineFormalized',
    'leanConcreteLockedNANDEmitterAxiomAuditPassed',
    'leanConcreteLockedNANDEmitterAllInputExactFormalized',
    'leanConcreteLockedNANDEmitterExactTargetBytesFormalized',
    'leanConcreteLockedNANDEmitterCompiledNonTimeoutFormalized',
    'leanConcreteLockedNANDEmitterPolynomialTimeMachineFormalized',
    'leanConcreteLockedNANDEmitterPolynomialTimeFunctionFormalized',
    'leanConcreteLockedNANDEmitterRawRefinementFormalized',
    'leanConcreteLockedNANDEmitterStrictParserCompositionFormalized',
    'leanConcreteLockedNANDEmitterOutputSizeBoundFormalized',
    'leanConcreteLockedNANDPolynomialReductionFormalized',
    'leanConcreteLockedNANDPolynomialReductionAxiomAuditPassed',
    'leanConcreteLockedNANDPolynomialReductionExactFunctionFormalized',
    'leanConcreteLockedNANDPolynomialReductionExactOutputFormalized',
    'leanConcreteLockedNANDPolynomialReductionLanguageEquivalenceFormalized',
    'leanConcreteLockedNANDPolynomialReductionWitnessFormalized',
    'leanConcreteLockedNANDPolynomialReductionRawRefinementFormalized',
    'leanConcreteCNFToNANDSemanticCompilerFormalized',
    'leanConcreteCNFToNANDSemanticCompilerAxiomAuditPassed',
    'leanConcreteCNFToNANDExactCodecCanonicalityFormalized',
    'leanConcreteCNFToNANDTypedTopologicalCompilationFormalized',
    'leanConcreteCNFToNANDWellFormedOutputFormalized',
    'leanConcreteCNFToNANDExactSemanticsFormalized',
    'leanConcreteCNFToNANDEdgeSemanticsFormalized',
    'leanConcreteCNFToNANDExactGateCountFormalized',
    'leanConcreteCNFToNANDPolynomialOutputSizeBoundFormalized',
    'leanConcreteCNFToNANDAllBitstringFailClosedFormalized',
    'leanConcreteCNFToNANDLockedThresholdCompositionFormalized',
    'leanConcreteCNFToNANDFiniteMachineFormalized',
    'leanConcreteCNFToNANDPolynomialTimeFunctionFormalized',
    'leanConcreteCNFToNANDPolynomialReductionFormalized',
    'leanConcreteCNFToNANDPolynomialReductionAxiomAuditPassed',
    'leanConcreteCNFToNANDAllInputExactFormalized',
    'leanConcreteCNFToNANDExactMachineOutputFormalized',
    'leanConcreteCNFToNANDCompiledNonTimeoutFormalized',
    'leanConcreteCNFToNANDRawRefinementFormalized',
    'leanConcreteCNFToNANDDirectReductionFormalized',
    'leanConcreteCNFToNANDLockedReductionCompositionFormalized',
    'leanResidualRoutesListedGainScanFormalized',
    'leanResidualRoutesAxiomAuditPassed',
    'leanResidualRoutesGainSoundnessFormalized',
    'leanResidualRoutesStrictResidualDescentFormalized',
    'leanResidualRoutesExactResultProofBearing',
    'leanResidualRoutesZeroSlackResultProofBearing',
    'leanResidualRoutesUnresolvedFailClosed',
    'leanResidualGainChainVerifierFormalized',
    'leanResidualGainChainAxiomAuditPassed',
    'leanResidualGainChainSemanticInvariantFormalized',
    'leanResidualGainChainSlackIterationBoundFormalized',
    'leanLockedNANDGainIterationsAtMostFourFormalized',
    'leanResidualGainStoppingSpecificationFormalized',
    'leanResidualGainStoppingAxiomAuditPassed',
    'leanResidualGainReferenceMinimumWitnessFormalized',
    'leanResidualGainPositiveIffGlobalStrictGainFormalized',
    'leanResidualGainZeroIffGlobalNoStrictGainFormalized',
    'leanResidualGainSemanticMinimumIffGlobalNoStrictGainFormalized',
    'leanResidualGainChainGlobalStoppingConsequenceFormalized',
    'leanResidualGainChainExactMinimumPackagingFormalized',
    'leanResidualTerminalFullBridgeFormalized',
    'leanResidualTerminalFullBridgeAxiomAuditPassed',
    'leanResidualTerminalizationExactFormalized',
    'leanResidualTerminalFullMinimumSpecificationFormalized',
    'leanResidualTerminalMuBridgeFormalized',
    'leanResidualWholeSpanPositiveWitnessIffFormalized',
    'leanResidualWholeSpanStrictDescentFormalized',
    'leanResidualWholeSpanZeroAbsenceIffFormalized',
    'leanResidualTerminalQuotientCarrierFormalized',
    'leanResidualTerminalModeFirewallFormalized',
    'leanResidualTerminalModeFirewallAxiomAuditPassed',
    'leanResidualTerminalProfileProjectionExactFormalized',
    'leanResidualTerminalCheckedFullLiftFormalized',
    'leanResidualTerminalQuotientEqualityNotConstructiveFormalized',
    'leanResidualTerminalObligationDischargePreservedFormalized',
    'leanResidualProjectionMinimumFormalized',
    'leanResidualProjectionMinimumAxiomAuditPassed',
    'leanResidualProjectionMinimumExecutableFullScanFormalized',
    'leanResidualProjectionMinimumExecutableQuotientScanFormalized',
    'leanResidualProjectionMinimumAttainmentFormalized',
    'leanResidualProjectionMinimumUniversalLowerBoundsFormalized',
    'leanResidualProjectionMinimumMonotonicityFormalized',
    'leanResidualProjectionDefectDecompositionFormalized',
    'leanResidualProjectionDefectZeroIffCheckedLiftAtMinimumFormalized',
    'leanResidualProjectionTransferFormalized',
    'leanResidualProjectionTransferAxiomAuditPassed',
    'leanResidualProjectionTransferSignedDeltasFormalized',
    'leanResidualProjectionTransferIdentityFormalized',
    'leanResidualProjectionTransferConstantCutFormalized',
    'leanResidualTerminalSaturationFormalized',
    'leanResidualTerminalSaturationAxiomAuditPassed',
    'leanResidualTerminalPrimitiveUniverseFormalized',
    'leanResidualTerminalSaturationExtensiveFormalized',
    'leanResidualTerminalSaturationLeastFormalized',
    'leanResidualTerminalSaturationMonotoneFormalized',
    'leanResidualTerminalSaturationIdempotentFormalized',
    'leanResidualTerminalExecutableSaturationFormalized',
    'leanResidualTerminalPhysicalSupportCompletionFormalized',
    'leanResidualTerminalPhysicalBoundaryFormalized',
    'leanResidualTerminalPhysicalInterfaceFormalized',
    'leanResidualTerminalPhysicalCompatibilityFormalized',
    'leanResidualTerminalPhysicalSupportCompletionAxiomAuditPassed',
    'leanResidualTerminalSupportExtractionFormalized',
    'leanResidualTerminalOpenSemanticsFormalized',
    'leanResidualTerminalInducedRecoveryFormalized',
    'leanResidualTerminalSupportExtractionAxiomAuditPassed',
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
    'leanResidualTerminalSupportSquareClosureFormalized',
    'leanResidualTerminalSupportSquareMeetJoinExactFormalized',
    'leanResidualTerminalSupportSquarePhysicalCompatibilityFormalized',
    'leanResidualTerminalSupportSquareSemanticExtractionFormalized',
    'leanResidualTerminalSupportSquareClosureAxiomAuditPassed',
    'leanResidualTerminalSupportCompletionFormalized',
    'leanResidualTerminalGovernedSupportCompletionFormalized',
    'leanResidualTerminalGovernedProfilePartitionFormalized',
    'leanResidualTerminalGovernedSupportCompletionAxiomAuditPassed',
    'leanResidualTerminalFrontierPushoutFormalized',
    'leanResidualTerminalFrontierBoundaryGlueExactFormalized',
    'leanResidualTerminalFrontierInterfaceGlueExactFormalized',
    'leanResidualTerminalFrontierProfileGlueExactFormalized',
    'leanResidualTerminalFrontierInternalizationFormalized',
    'leanResidualTerminalFrontierPushoutAxiomAuditPassed',
    'leanResidualTerminalProjectionSquareFormalized',
    'leanResidualTerminalProjectionPhysicalInvariantFormalized',
    'leanResidualTerminalProjectionProfileExactFormalized',
    'leanResidualTerminalProjectionMeetJoinCommuteFormalized',
    'leanResidualTerminalProjectionPushoutCommuteFormalized',
    'leanResidualTerminalProjectionSquareAxiomAuditPassed',
    'leanResidualTerminalSideTightMinimumArithmeticFormalized',
    'leanResidualTerminalSideTightSignedSlackIdentityFormalized',
    'leanResidualTerminalSideTightFailClosedGateFormalized',
    'leanResidualTerminalSideTightCanonicalFullBasisFormalized',
    'leanResidualTerminalSideTightCanonicalQuotientBasisFormalized',
    'leanResidualTerminalSideTightMinimumAxiomAuditPassed',
    'leanResidualTerminalFourCornerCarrierTransportFormalized',
    'leanResidualTerminalFourCornerCarrierExactEndpointsFormalized',
    'leanResidualTerminalFourCornerCarrierInjectiveCoordinatesFormalized',
    'leanResidualTerminalFourCornerCarrierProfileTransportFormalized',
    'leanResidualTerminalFourCornerCarrierFailClosedPhysicalTransportFormalized',
    'leanResidualTerminalFourCornerCarrierAxiomAuditPassed',
    'leanResidualTerminalFourCornerOptimaCarrierCompatibleFormalized',
    'leanResidualTerminalFourCornerOptimaFaithfulAmbientizationFormalized',
    'leanResidualTerminalFourCornerOptimaReferenceMinimumPreservedFormalized',
    'leanResidualTerminalFourCornerOptimaLocalizedMinimaFormalized',
    'leanResidualTerminalFourCornerOptimaSharedObserverProjectionFormalized',
    'leanResidualTerminalFourCornerOptimaAxiomAuditPassed',
    'leanResidualTerminalFourCornerOptimumLocalRouteClassifierFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSoundnessFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumSideTightCompletionUnderRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumExactCompletionValuesFormalized',
    'leanResidualTerminalFourCornerOptimumPromotionFirewallRetained',
    'leanResidualTerminalFourCornerSideTightCompletionAxiomAuditPassed',
    'leanResidualTerminalFourCornerArbitraryFamilyCoherenceFormalized',
    'leanResidualTerminalFourCornerExactMinimumFamilyEnumerated',
    'leanResidualTerminalFourCornerTightBasisFamilyComplete',
    'leanResidualTerminalFourCornerSignedTightBasisMaximumFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumEqualsDeltaFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumAxiomAuditPassed',
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalSquareStructuralCompatibilityFormalized',
    'leanResidualTerminalSquareFrontierPushoutFormalized',
    'leanResidualTerminalSquareSharedQuantityCarrierFormalized',
    'leanResidualTerminalSquareLocalConclusionUnderRouteSilenceFormalized',
    'leanResidualTerminalSquareFailClosedRouteDichotomyFormalized',
    'leanResidualTerminalSquareLegitimacyAxiomAuditPassed',
    'leanResidualTerminalCoherentFourCornerBasisFormalized',
    'leanResidualTerminalComputedBCELAnchorNucleusFormalized',
    'leanResidualTerminalBCELMinimumPositiveNucleusFormalized',
    'leanResidualTerminalBCELAnchorAlgebraFormalized',
    'leanResidualTerminalBCELCutDefectFirewallFormalized',
    'leanResidualTerminalBCELCutRouteDichotomyFormalized',
    'leanResidualTerminalBCELConstantCutConclusionFormalized',
    'leanResidualTerminalBCELAnchorNucleusAxiomAuditPassed',
    'leanResidualTerminalSaturationPositivityFirewallFormalized',
    'leanResidualTerminalSaturationPositivityFirewallAxiomAuditPassed',
    'leanResidualTerminalCandidateSaturationFormalized',
    'leanResidualTerminalSaturationCostBalanceFormalized',
    'leanResidualTerminalFirstNontransparentStepFormalized',
    'leanResidualTerminalSaturationCostBalanceAxiomAuditPassed',
    'leanResidualTerminalInterfaceExposureRoutingFormalized',
    'leanResidualTerminalFiniteInterfaceExposureRoutesToEFormalized',
    'leanResidualTerminalInterfaceExposureZeroCostRetractFormalized',
    'leanResidualTerminalFirstInterfaceExposureRouteFormalized',
    'leanResidualTerminalInterfaceExposureRoutingAxiomAuditPassed',
    'leanResidualTerminalOriginKernelObligationRoutingFormalized',
    'leanResidualTerminalFiniteOriginKernelObligationClosureRoutedFormalized',
    'leanResidualTerminalFirstOriginKernelObligationRouteFormalized',
    'leanResidualTerminalOriginKernelObligationRoutingAxiomAuditPassed',
    'leanResidualTerminalFiniteSaturatePositiveCompositionFormalized',
    'leanResidualTerminalFiniteSaturatePositiveCompositionAxiomAuditPassed',
    'leanResidualTerminalRankWFFormalized',
    'leanResidualTerminalRankWFAxiomAuditPassed',
    'leanResidualTerminalBN3RequestEnvelopeFormalized',
    'leanResidualTerminalBN3RequestEnvelopeAxiomAuditPassed',
    'leanResidualTerminalBN4ActivationCancellationFormalized',
    'leanResidualTerminalBN4ActivationCancellationAxiomAuditPassed',
    'leanResidualTerminalBN5FullShadowLocalizationFormalized',
    'leanResidualTerminalBN5FullShadowLocalizationAxiomAuditPassed',
    'leanResidualTerminalPkgCSeparatingConsumersFormalized',
    'leanResidualTerminalPkgCSeparatingConsumersAxiomAuditPassed',
    'leanResidualTerminalPkgCTypedRestorationFormalized',
    'leanResidualTerminalPkgCTypedRestorationAxiomAuditPassed',
    'leanResidualTerminalPkgCSameKeyCancellationFormalized',
    'leanResidualTerminalPkgCSameKeyCancellationAxiomAuditPassed',
    'leanResidualTerminalPkgCAmbientBN4LedgerFormalized',
    'leanResidualTerminalPkgCAmbientBN4LedgerAxiomAuditPassed',
    'leanResidualTerminalPkgCAmbientBN4ResidualReductionFormalized',
    'leanResidualTerminalPkgCAmbientBN4ResidualReductionAxiomAuditPassed',
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

test('formal reconstruction status rejects unearned downstream claims', async () => {
  const fields = [
    'leanNANDEnumeratorDeduplicated',
    'leanNANDReferenceMinimumPolynomialRuntimeProved',
    'leanCompatibleReplacementFormalized',
    'leanGlobalSlackLawFormalized',
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanResidualGainChainPolynomialRuntimeFormalized',
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
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

test('formal reconstruction status rejects restoring the discharged locked NAND blocker', async () => {
  const status = await currentStatus0();
  status.remainingBlockers = [...status.remainingBlockers, 'Formal.LockedNANDThreshold'];
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Blockers');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'remainingBlockers']);
});

test('formal reconstruction status rejects legacy locked-NAND quarantine drift', async () => {
  for (const [field, replacement] of [
    ['legacySyntheticLockedNANDM2FixtureStatus', 'accepted'],
    ['legacySyntheticLockedNANDM2HonestBaseline', 91],
    ['legacySyntheticLockedNANDM2MetadataConsistentBaseline', 91],
    ['legacySyntheticLockedNANDM2StoredBaseline', 86],
    ['legacySyntheticLockedNANDM2HonestDisplayedGateCount', 95],
    ['legacySyntheticLockedNANDM2MetadataConsistentDisplayedGateCount', 95],
    ['legacySyntheticLockedNANDM2StoredDisplayedGateCount', 90],
    ['lockedNANDOutputConvention', 'single-output'],
  ]) {
    const status = await currentStatus0();
    status[field] = replacement;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.equal(out.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('formal reconstruction status rejects threshold-boundary inventory drift', async () => {
  for (const field of [
    'lockedNANDThresholdHostileReviewLemmaInventory',
    'leanLockedNANDThresholdPremiseInventory',
    'leanLockedNANDThresholdMissingInstantiationInventory',
  ]) {
    const status = await currentStatus0();
    status[field] = field === 'leanLockedNANDThresholdMissingInstantiationInventory'
      ? ['unexpectedField']
      : status[field].slice(0, -1);
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
    assert.equal(out.tag, 'reject', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
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
