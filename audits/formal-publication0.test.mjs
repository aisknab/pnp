import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import { CheckFormalReconstructionStatus0 } from '../pcc-formal-reconstruction-status0.mjs';
import { sha256Text0, stableStringify0 } from '../formal-publication0.mjs';
import { BuildFormalPublication0 } from '../scripts/generate-formal-publication.mjs';

async function status0() {
  return JSON.parse(await readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url), 'utf8'));
}

test('status, public payload, and canonical TeX are exact generated publication outputs', async () => {
  const built = await BuildFormalPublication0(fileURLToPath(new URL('../', import.meta.url)));
  const [statusBytes, siteBytes, texBytes] = await Promise.all([
    readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url)),
    readFile(new URL('../public/pnp-status.json', import.meta.url)),
    readFile(new URL('../canonical_proof_report.tex', import.meta.url)),
  ]);
  assert.equal(statusBytes.equals(siteBytes), true);
  assert.equal(statusBytes.equals(built.statusOutput), true);
  assert.equal(texBytes.equals(built.reportOutput), true);
  assert.equal(built.publication.gate.passed, false);
});

test('publication generation starts from the closed checker schema, not its own output', async () => {
  const source = await readFile(new URL('../scripts/generate-formal-publication.mjs', import.meta.url), 'utf8');
  assert.match(source, /BuildFormalReconstructionBaseStatus0\(\)/u);
  assert.doesNotMatch(source, /readFile\(path\.join\(root, STATUS_PATH\)\)/u);
});

test('every theorem-emission field is derived from the concrete publication gate', async () => {
  const status = await status0();
  const passed = status.concretePublicationGate.passed;
  assert.equal(passed, false);
  for (const field of [
    'mathematicalTheoremEstablished',
    'publicTheoremEmissionAllowed',
    'finalTheoremReady',
    'internalFinalTheoremReady',
    'unrestrictedFinalSoundnessDischarged',
    'uniformFinalSoundnessProved',
    'satInPConclusionAccepted',
    'pEqualsNPConclusionAccepted',
  ]) assert.equal(status[field], passed, field);
  assert.equal(status.publicTheoremStatement, null);
  assert.equal(status.publicTheoremConclusion, null);
  assert.equal(status.publicationStatusDerivedOnlyFromConcreteGate, true);
  assert.equal(status.abstractPEqualsNPPublicationEligible, false);
  assert.equal(status.standardComplexityModelFormalized, true);
});

test('status checker rejects forged gate activation and independent theorem-emission overrides', async () => {
  const current = await status0();
  const forgedGate = structuredClone(current);
  forgedGate.concretePublicationGate.passed = true;
  let out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: forgedGate });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.ConcretePublicationGate');

  const forgedEmission = structuredClone(current);
  forgedEmission.publicTheoremEmissionAllowed = true;
  out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: forgedEmission });
  assert.equal(out.tag, 'reject');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'publicTheoremEmissionAllowed']);
});

test('historical activation and checker acceptance cannot override the concrete gate', async () => {
  const current = await status0();
  for (const [field, value] of [
    ['checkerAcceptanceIsMathematicalProof', true],
    ['legacyCheckerStackStatus', 'public-theorem-emission-activated'],
    ['historicalActivatedStatusCoordinate', 'PNP-ACTIVATED-STATUS-2026-07-05-01-ACTIVE'],
    ['currentStatusAuthority', false],
  ]) {
    const mutation = structuredClone(current);
    mutation[field] = value;
    const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: mutation });
    assert.equal(out.tag, 'reject', field);
    assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
    assert.equal(out.mathematicalTheoremEstablished, false, field);
    assert.equal(out.publicTheoremEmissionAllowed, false, field);
  }
});

test('status retains six blockers, four project axioms, and an absent compatibility root', async () => {
  const status = await status0();
  assert.equal(status.remainingBlockers.length, 6);
  assert.deepEqual(status.remainingBlockers, status.remainingFormalObligations);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.projectSpecificAxiomsRemaining, true);
  assert.equal(status.rootLeanTheorem, 'PNP.Main.p_eq_np');
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.rootLeanTheoremBuilt, false);
  assert.equal(status.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(status.sorryOrAdmitInRootDependencyClosure, null);
});

test('milestone ledger is evidence-backed and keeps premise/global boundaries explicit', async () => {
  const status = await status0();
  const byId = new Map(status.formalPublicationMilestones.map((entry) => [entry.id, entry]));
  assert.equal(byId.get('concrete-machine-cost-kernel').status, 'formalized-foundation-only');
  assert.equal(byId.get('concrete-cnf-universal-verifier').status,
    'formalized-np-membership-only');
  assert.equal(byId.get('concrete-cook-levin-layout').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-local-cnf').status,
    'formalized-foundation-only');
  assert.match(byId.get('concrete-cook-levin-local-cnf').nonClaim,
    /does not enumerate the verifier tableau/u);
  assert.equal(byId.get('concrete-cook-levin-tableau-cnf').status,
    'formalized-foundation-only');
  assert.match(byId.get('concrete-cook-levin-tableau-cnf').nonClaim,
    /does not yet prove that formula satisfiability is equivalent/u);
  assert.equal(byId.get('concrete-cook-levin-tableau-cnf-semantics').status,
    'formalized-foundation-only');
  assert.match(byId.get('concrete-cook-levin-tableau-cnf-semantics').nonClaim,
    /following raw-tape milestone supplies the execution bridge/u);
  assert.equal(byId.get('concrete-cook-levin-raw-tape-bridge').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-raw-tape-bridge').earned, true);
  assert.equal(byId.get('concrete-cook-levin-raw-tape-bridge').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-raw-tape-bridge')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.match(byId.get('concrete-cook-levin-raw-tape-bridge').nonClaim,
    /does not yet prove external encoded-formula-size/u);
  assert.equal(byId.get('concrete-cook-levin-formula-size').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-formula-size').earned, true);
  assert.equal(byId.get('concrete-cook-levin-formula-size').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-formula-size')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-formula-size').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_size_le'), true);
  assert.equal(byId.get('concrete-cook-levin-formula-size').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaWidthPolynomial_eval'), true);
  assert.match(byId.get('concrete-cook-levin-formula-size').nonClaim,
    /does not implement or time a raw finite formula builder/u);
  assert.equal(byId.get('concrete-cook-levin-formula-schedule').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-formula-schedule').earned, true);
  assert.equal(byId.get('concrete-cook-levin-formula-schedule').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-formula-schedule')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-formula-schedule').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSchedule_emit_eq_encodedFormula'),
  true);
  assert.match(byId.get('concrete-cook-levin-formula-schedule').nonClaim,
    /pure schedule specification/u);
  assert.equal(byId.get('concrete-cook-levin-formula-cursor').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-formula-cursor').earned, true);
  assert.equal(byId.get('concrete-cook-levin-formula-cursor').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-formula-cursor')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-formula-cursor').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_full_emit_eq_encodedFormula'),
  true);
  assert.match(byId.get('concrete-cook-levin-formula-cursor').nonClaim,
    /Lean specification cursor/u);
  assert.equal(byId.get('concrete-cook-levin-builder-input-length').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-input-length').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-input-length').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-input-length')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-input-length').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderInputLength.workRunExact_after_totalInputFramer'), true);
  assert.match(byId.get('concrete-cook-levin-builder-input-length').nonClaim,
    /only the input-length preparation stage/u);
  assert.equal(byId.get('concrete-cook-levin-builder-input-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-input-prefix').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-input-prefix').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-input-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-input-prefix').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderInputPrefix.workRunExact'), true);
  assert.match(byId.get('concrete-cook-levin-builder-input-prefix').nonClaim,
    /only an executable input-preparation prefix/u);
  assert.equal(byId.get('concrete-cook-levin-builder-token-appender').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-token-appender').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-token-appender').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-token-appender')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-token-appender').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderTokenAppender.appendToken_workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-token-appender').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderTokenAppender.firstHeaderToken_bits_eq_encodedFormula_take_two'),
  true);
  assert.match(byId.get('concrete-cook-levin-builder-token-appender').nonClaim,
    /audits the token appender independently/u);
  assert.equal(byId.get('concrete-cook-levin-builder-first-token-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-first-token-prefix').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-token-prefix').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-first-token-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-token-prefix').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderFirstTokenPrefix.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-token-prefix').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderFirstTokenPrefix.finalTokenBits_eq_encodedFormula_take_two'),
  true);
  assert.match(byId.get('concrete-cook-levin-builder-first-token-prefix').scope,
    /literal 184-rule finite work machine/u);
  assert.match(byId.get('concrete-cook-levin-builder-first-token-prefix').nonClaim,
    /only the first two canonical formula bits/u);
  assert.equal(byId.get('concrete-cook-levin-builder-complete-header').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-complete-header').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-complete-header').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-complete-header')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-complete-header').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderUnaryPolynomial.workTimePolynomial_eval'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-complete-header').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderCompleteHeader.finalTokenBits_eq_encodedFormula_header'), true);
  assert.match(byId.get('concrete-cook-levin-builder-complete-header').scope,
    /363 plus the evaluator rule count/u);
  assert.match(byId.get('concrete-cook-levin-builder-complete-header').nonClaim,
    /complete answer-independent width header only/u);
  assert.equal(byId.get('concrete-cook-levin-builder-body-start-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-body-start-prefix').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-body-start-prefix').allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-body-start-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-body-start-prefix').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderBodyStartPrefix.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-body-start-prefix').requiredTheorems.includes(
    'PNP.Concrete.CookLevin.BuilderBodyStartPrefix.finalTokenBits_eq_encodedFormula_bodyStart'),
  true);
  assert.match(byId.get('concrete-cook-levin-builder-body-start-prefix').scope,
    /440 plus the width-evaluator and next-token-slot-evaluator rule counts/u);
  assert.match(byId.get('concrete-cook-levin-builder-body-start-prefix').nonClaim,
    /not implement a dynamic formula cursor/u);
  assert.equal(byId.get('concrete-cook-levin-builder-first-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-first-literal-prefix').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-literal-prefix').allAssumptionFree,
    false);
  assert.equal(byId.get('concrete-cook-levin-builder-first-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-literal-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstLiteralPrefix.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-literal-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstLiteralPrefix.finalTokenBits_eq_encodedFormula_firstLiteral'),
  true);
  assert.match(byId.get('concrete-cook-levin-builder-first-literal-prefix').scope,
    /585 plus the width, body-start next-slot, and first-literal next-slot evaluator rule counts/u);
  assert.match(byId.get('concrete-cook-levin-builder-first-literal-prefix').nonClaim,
    /does not implement a dynamic formula cursor/u);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-prefix').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-prefix').allAssumptionFree,
    false);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstClausePrefix.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstClausePrefix.finalTokenBits_eq_encodedFormula_firstClause'),
  true);
  assert.match(byId.get('concrete-cook-levin-builder-first-clause-prefix').scope,
    /1138 plus the width, body-start next-slot, first-literal next-slot, and first-clause next-slot evaluator rule counts/u);
  assert.match(byId.get('concrete-cook-levin-builder-first-clause-prefix').nonClaim,
    /does not implement a dynamic formula cursor/u);
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step')
    .allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.specification_step'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.malformedCursorScratch_timeout'), true);
  assert.match(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step').scope,
    /1192 plus the four inherited unary-evaluator rule counts/u);
  assert.match(byId.get('concrete-cook-levin-builder-dynamic-token-cursor-step').nonClaim,
    /not a general dynamic cursor loop/u);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run')
    .allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.specification_padding_run'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-first-clause-padding-run')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.secondClauseStart_direct_eq_sep'), true);
  assert.match(byId.get('concrete-cook-levin-builder-first-clause-padding-run').scope,
    /1244 plus the six inherited and generated evaluator rule counts/u);
  assert.match(byId.get('concrete-cook-levin-builder-first-clause-padding-run').nonClaim,
    /not a general dynamic formula cursor/u);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step').status,
    'formalized-foundation-only');
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step').earned, true);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step')
    .allAssumptionFree, false);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.workRunExact'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.finalTokenBits_eq_encodedFormula_secondClauseStart'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.nextTokenSlot_direct_eq_f'), true);
  assert.equal(byId.get('concrete-cook-levin-builder-second-clause-separator-step')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep'), true);
  assert.match(byId.get('concrete-cook-levin-builder-second-clause-separator-step').scope,
    /1366 plus the six inherited and generated unary-evaluator rule counts/u);
  assert.match(byId.get('concrete-cook-levin-builder-second-clause-separator-step').nonClaim,
    /does not emit that F/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.workRunExact'), true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.finalTokenBits_eq_encodedFormula_secondClauseFirstLiteral'), true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.firstLiteralZeroTerminatorSlot_direct_eq_f'), true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix')
    .requiredTheorems.includes(
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.firstCursorEndpoint_before_secondAppender_launch_timeout'), true);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix').scope,
    /1610 plus the six inherited and generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-first-literal-prefix').nonClaim,
    /does not complete clause two/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix')
    .requiredTheorems.length, 75);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.finalTokenBits_eq_encodedFormula_secondClauseSecondLiteral',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.secondLiteralSignSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.secondLiteralUnaryUnitSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.secondLiteralTerminatorSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.nextTokenSlot_direct_eq_finish',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.unaryCursorEndpoint_before_terminator_launch_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix').scope,
    /1976 plus the six inherited and generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-second-literal-prefix').nonClaim,
    /does not emit the clause terminator/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix').requiredTheorems.length, 41);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.finalTokenBits_eq_encodedFormula_secondClause',
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.clauseTerminatorSlot_direct_eq_finish',
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.nextTokenSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix').scope,
    /complete second clause/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-prefix').nonClaim,
    /does not traverse clause-two padding/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run').requiredTheorems.length, 39);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loop_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.finalTokenBits_eq_encodedFormula_secondClause',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.remainingPaddingCount_eq_formulaTokensPerClause_sub_seven',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.paddingSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.thirdClauseStart_direct_eq_sep',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.malformedCountdownRoot_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run').scope,
    /2150 plus the six inherited\/generated predecessor evaluator rule counts and the two new evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-clause-padding-run').nonClaim,
    /does not emit the third-clause separator/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.finalTokenBits_eq_encodedFormula_thirdClauseStart',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.nextTokenSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step').scope,
    /2272 plus eight inherited unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-separator-step').nonClaim,
    /does not emit that F/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix')
    .requiredTheorems.length, 58);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.rules_length',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.finalTokenBits_eq_encodedFormula_thirdClauseFirstLiteral',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.firstLiteralSignSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.firstLiteralZeroTerminatorSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.nextTokenSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.malformedSecondCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix').scope,
    /2516 plus the eight inherited and generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-first-literal-prefix').nonClaim,
    /does not emit that following F/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix')
    .requiredTheorems.length, 92);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_length',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.finalTokenBits_eq_encodedFormula_thirdClauseSecondLiteral',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.secondLiteralSignSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.secondLiteralFirstUnaryUnitSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.secondLiteralSecondUnaryUnitSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.secondLiteralTerminatorSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.nextTokenSlot_direct_eq_finish',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.malformedTerminatorCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix').scope,
    /3004 plus the eight inherited and generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-second-literal-prefix').nonClaim,
    /does not emit the following Finish/u);
  assert.equal(byId.get('concrete-cnf-universal-verifier').requiredTheorems.includes(
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP'), true);
  assert.match(byId.get('concrete-cnf-universal-verifier').nonClaim,
    /does not prove CNF-SAT is in P, NP-completeness, or P = NP/u);
  assert.equal(byId.get('concrete-complexity-classes').status, 'formalized');
  for (const id of [
    'direct-wire-semantics',
    'finite-enumeration-minimum',
    'framed-replacement-slack',
    'locked-nand-local-baseline',
  ]) assert.equal(byId.get(id).status, 'formalized');
  assert.equal(byId.get('locked-nand-conditional-threshold').status, 'formalized-with-premises');
  assert.equal(byId.get('explicit-residual-routes').status, 'formalized-explicit-list-only');
  for (const id of [
    'global-locked-nand-threshold',
    'global-zeroslack-pccmin',
    'concrete-publication-root',
  ]) assert.equal(byId.get(id).status, 'not-formalized');
});

test('publication consumes the reviewed third-clause second-literal map and inventory counts', async () => {
  const [status, mapText] = await Promise.all([
    status0(),
    readFile(new URL('../publication/FORMAL_PUBLICATION_MAP.json', import.meta.url), 'utf8'),
  ]);
  const map = JSON.parse(mapText);
  assert.equal(sha256Text0(stableStringify0(map)),
    '45019958363732c256a7b806333e74c909c3c726325742a9ed5c2d4aa852c67c');
  assert.equal(map.milestoneSourceClosureSha256,
    '9a711cfc0c85aea0ef04efaf16a885e38f14a98831874c81b5cc889a5ef3715e');
  assert.equal(Object.keys(map.earnedMilestoneTheoremKernelTypeSha256).length, 1050);
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.PipelineCompiler.pipeline_correct'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.PipelineSequentialCompiler.sequential_correct'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.PolynomialTimeDecider.compileToMachine_accepts_iff'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClausePrefix.nextTokenSlot_direct_eq_padding'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.thirdClauseStart_direct_eq_sep'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.finalTokenBits_eq_encodedFormula_thirdClauseStart'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.finalTokenBits_eq_encodedFormula_thirdClauseFirstLiteral'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.finalTokenBits_eq_encodedFormula_thirdClauseSecondLiteral'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.LocalProgram.toFormula_satisfiable_iff'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_wellScoped'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff_finiteAccepting'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.VerifierTableauProblem.formulaBitSchedule_length'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaBitCursor.run_full_emit_eq_encodedFormula'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderInputLength.workRunExact_after_totalInputFramer'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderInputPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderTokenAppender.appendToken_workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstTokenPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstTokenPrefix.run_compile_rawTimeBound_blankEquivalent'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderUnaryPolynomial.workTimePolynomial_eval'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderCompleteHeader.finalTokenBits_eq_encodedFormula_header'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderBodyStartPrefix.finalTokenBits_eq_encodedFormula_bodyStart'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstLiteralPrefix.finalTokenBits_eq_encodedFormula_firstLiteral'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstClausePrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstClausePrefix.finalTokenBits_eq_encodedFormula_firstClause'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.VerifierTableauProblem.FormulaTokenCursor.step_of_lt'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstClausePrefix.nextTokenSlot_direct_eq_padding'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.run_compile_rawTimeBound'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.specification_padding_run'
  ], 'string');
  assert.deepEqual([
    map.gate.expectedConcreteTargetKernelTypeSha256,
    map.gate.expectedConcreteTargetKernelValueSha256,
    map.gate.expectedRootKernelTypeSha256,
    map.gate.expectedAxiomClosureSha256,
    map.gate.expectedSourceClosureSha256,
  ], [null, null, null, null, null]);
  assert.deepEqual([
    status.leanTheoremInventoryDeclarationCount,
    status.leanTheoremInventoryTheoremCount,
    status.leanTheoremInventoryAssumptionFreeTheoremCount,
    status.leanTheoremInventoryExcludedPrivateDeclarationCount,
    status.leanTheoremInventorySourceClosureModuleCount,
  ], [9024, 4688, 3108, 3089, 80]);
});

test('canonical report source is current and the committed PDF artifact exists', async () => {
  const [tex, status] = await Promise.all([
    readFile(new URL('../canonical_proof_report.tex', import.meta.url), 'utf8'),
    status0(),
  ]);
  assert.match(tex, /The repository does not currently establish \$P=NP\$\./u);
  assert.match(tex, /A literal finite builder emits\s+\\code\{FormulaWidth\} copies of \\code\{T\} followed by \\code\{F\}, \\code\{Sep\}, and the complete positive\s+clause on variables zero, one, and two/u);
  assert.match(tex, /complete positive at-least-one shape clause on variables zero,\s+one, and two/u);
  assert.match(tex, /One literal token-cursor step continues from that first-clause endpoint/u);
  assert.match(tex, /not a general cursor loop or arbitrary schedule decoder/u);
  assert.match(tex, /The remaining-padding composition continues from that one-step endpoint/u);
  assert.match(tex, /Direct lookup at that coordinate is\s+proved to return \\code\{Sep\}/u);
  assert.match(tex, /The second-clause-separator composition continues with a selected 59-rule/u);
  assert.match(tex, /does not emit the following \\code\{F\}/u);
  assert.match(tex, /Cook-Levin second-clause first-literal prefix/u);
  assert.match(tex, /complete negative literal on variable zero in clause two/u);
  assert.match(tex, /Cook-Levin second-clause second-literal prefix/u);
  assert.match(tex, /complete negative literal on variable one in clause two/u);
  assert.match(tex, /retains the following Finish coordinate/u);
  assert.match(tex, /Cook-Levin complete second-clause prefix/u);
  assert.match(tex, /complete second clause/u);
  assert.match(tex, /second-clause-padding composition evaluates/u);
  assert.match(tex, /retained coordinate is the third clause's opening/u);
  assert.match(tex, /third-clause-separator composition reuses the selected 59-rule/u);
  assert.match(tex, /emits the separator beginning clause three/u);
  assert.match(tex, /does not emit the\s+following \\code\{F\}/u);
  assert.match(tex, /third-clause-first-literal composition reuses the audited 235-rule/u);
  assert.match(tex, /complete negative literal on variable zero in clause three/u);
  assert.match(tex, /does not emit the next\s+negative sign/u);
  assert.match(tex, /third-clause-second-literal composition adds a fixed 479-rule/u);
  assert.match(tex, /complete negative literal on variable two/u);
  assert.match(tex, /does not emit\s+the following \\code\{Finish\}/u);
  assert.equal(tex.includes('It does not compute the remaining header or complete formula'), false);
  assert.ok(tex.includes(status.leanTheoremInventorySha256));
  assert.ok(tex.includes(status.coordinate.replaceAll('_', '\\_')) || tex.includes(status.coordinate));
  for (const forbidden of [
    'Accepted proof-report boundary',
    'Complete machine-checkable proof report',
    'This paper proves',
    'Hence the final conclusion of this paper is',
  ]) assert.equal(tex.includes(forbidden), false, forbidden);
  const pdf = await readFile(new URL('../canonical_proof_report.pdf', import.meta.url));
  assert.equal(pdf.subarray(0, 5).toString('ascii'), '%PDF-');
});
