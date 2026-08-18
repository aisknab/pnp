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

test('status retains five blockers, four project axioms, and an absent compatibility root', async () => {
  const status = await status0();
  assert.equal(status.remainingBlockers.length, 5);
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
  assert.equal(status.formalPublicationMilestones.length,
    new Set(status.formalPublicationMilestones.map(({ id }) => id)).size);
  assert.equal(status.formalPublicationMilestones.filter((entry) => entry.earned).length,
    status.formalPublicationMilestones.length
      - status.formalPublicationMilestones.filter((entry) => !entry.earned).length);
  assert.equal(status.formalPublicationMilestones.filter((entry) => !entry.earned).length, 2);
  const selectorCodec = byId.get('residual-terminal-packet-selector-codec');
  assert.equal(selectorCodec.status,
    'formalized-residual-terminal-packet-selector-codec');
  assert.equal(selectorCodec.earned, true);
  assert.equal(selectorCodec.requiredTheorems.length, 11);
  assert.match(selectorCodec.scope, /fail-closed/u);
  assert.match(selectorCodec.nonClaim,
    /does not bound that list by encoded circuit size/u);
  const payloadRealization = byId.get(
    'residual-terminal-packet-selector-payload-realization');
  assert.equal(payloadRealization.status,
    'formalized-residual-terminal-packet-selector-payload-realization');
  assert.equal(payloadRealization.earned, true);
  assert.equal(payloadRealization.requiredTheorems.length, 11);
  assert.match(payloadRealization.scope, /original positive payload atom/u);
  assert.match(payloadRealization.nonClaim,
    /not the manuscript's gain-or-blocker selector realizer/u);
  const gainScan = byId.get('residual-terminal-packet-selector-gain-scan');
  assert.equal(gainScan.status,
    'formalized-residual-terminal-packet-selector-gain-scan');
  assert.equal(gainScan.earned, true);
  assert.equal(gainScan.requiredTheorems.length, 12);
  assert.match(gainScan.scope, /genuine source-atom StrictEquivalentGain/u);
  assert.match(gainScan.nonClaim,
    /local no-gain result excludes only payload candidates/u);
  const universeGainScan = byId.get(
    'residual-terminal-packet-selector-universe-gain-scan');
  assert.equal(universeGainScan.status,
    'formalized-residual-terminal-packet-selector-universe-gain-scan');
  assert.equal(universeGainScan.earned, true);
  assert.equal(universeGainScan.requiredTheorems.length, 10);
  assert.match(universeGainScan.scope,
    /every canonical input-relative selector handle/u);
  assert.match(universeGainScan.nonClaim,
    /supplied input-relative selector universe/u);
  const gainCoverage = byId.get(
    'residual-terminal-packet-selector-gain-coverage');
  assert.equal(gainCoverage.status,
    'formalized-residual-terminal-packet-selector-gain-coverage');
  assert.equal(gainCoverage.earned, true);
  assert.equal(gainCoverage.requiredTheorems.length, 7);
  assert.match(gainCoverage.scope, /every strict equivalent gain/u);
  assert.match(gainCoverage.nonClaim,
    /does not construct the coverage certificate/u);
  const chargeSurplus = byId.get(
    'residual-terminal-packet-charge-surplus');
  assert.equal(chargeSurplus.status,
    'formalized-residual-terminal-packet-charge-surplus');
  assert.equal(chargeSurplus.earned, true);
  assert.equal(chargeSurplus.requiredTheorems.length, 8);
  assert.match(chargeSurplus.scope, /unmatched positive support charge/u);
  assert.match(chargeSurplus.nonClaim,
    /does not construct a replacement/u);
  const unitChargeRealizer = byId.get(
    'residual-terminal-packet-unit-charge-blueprint-realizer');
  assert.equal(unitChargeRealizer.status,
    'formalized-residual-terminal-packet-unit-charge-blueprint-realizer');
  assert.equal(unitChargeRealizer.earned, true);
  assert.equal(unitChargeRealizer.requiredTheorems.length, 13);
  assert.match(unitChargeRealizer.scope,
    /canonical unit-charge gate-occurrence ledgers/u);
  assert.match(unitChargeRealizer.scope, /every canonical handle/u);
  assert.match(unitChargeRealizer.nonClaim,
    /blueprints.*remain explicit inputs/iu);
  assert.match(unitChargeRealizer.nonClaim,
    /not BotHN, BotBUD, a lower-rank BotSeed/u);
  const typedRealizer = byId.get(
    'residual-terminal-packet-typed-realizer-contract');
  assert.equal(typedRealizer.status,
    'formalized-residual-terminal-packet-typed-realizer-contract');
  assert.equal(typedRealizer.earned, true);
  assert.equal(typedRealizer.requiredTheorems.length, 5);
  assert.match(typedRealizer.scope, /active same-or-lower-rank HN bot/u);
  assert.match(typedRealizer.scope, /every canonical input-relative Packet handle/u);
  assert.match(typedRealizer.nonClaim,
    /rank assignment.*remain explicit inputs/iu);
  assert.match(typedRealizer.nonClaim, /does not.*HB acyclicity/iu);
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
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix')
    .requiredTheorems.length, 41);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.FinishTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.finalTokenBits_eq_encodedFormula_thirdClause',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.clauseTerminatorSlot_direct_eq_finish',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.nextTokenSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix').scope,
    /3126 plus the eight inherited unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-prefix').nonClaim,
    /does not traverse clause-three padding/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run').requiredTheorems.length, 39);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loop_workRunExact',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.workRunExact',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.finalTokenBits_eq_encodedFormula_thirdClause',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.remainingPaddingCount_eq_formulaTokensPerClause_sub_eight',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.paddingSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.fourthClauseStart_direct_eq_sep',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.malformedCountdownRoot_timeout',
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run').scope,
    /3178 plus the eight inherited\/generated predecessor evaluator rule counts and the two new evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-third-clause-padding-run').nonClaim,
    /does not emit the fourth-clause separator/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.fourthClauseStartTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.finalTokenBits_eq_encodedFormula_fourthClauseStart',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.nextTokenSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.malformedAppenderTally_timeout',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step').scope,
    /3300 plus the ten inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-separator-step').nonClaim,
    /observes but does not emit the following F/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix')
    .requiredTheorems.length, 75);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_length',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.finalTokenBits_eq_encodedFormula_fourthClauseFirstLiteral',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.nextTokenSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.malformedSignAppenderTally_timeout',
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix').scope,
    /3666 plus the ten inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-first-literal-prefix').nonClaim,
    /observes but does not emit the following second-literal F/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix')
    .allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix')
    .requiredTheorems.length, 92);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_length',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.fourthClauseSecondLiteralTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.finalTokenBits_eq_encodedFormula_fourthClauseSecondLiteral',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.nextTokenSlot_direct_eq_finish',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.malformedSignAppenderTally_timeout',
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix').scope,
    /4154 plus the ten inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-second-literal-prefix').nonClaim,
    /observes but does not emit the following Finish/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix').status,
    'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix')
    .requiredTheorems.length, 41);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.FinishTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.fourthClauseTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.finalTokenBits_eq_encodedFormula_fourthClause',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.clauseTerminatorSlot_direct_eq_finish',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.nextTokenSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.work_one_step_short_timeout',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix').scope,
    /4276 plus the ten inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-prefix').nonClaim,
    /does not traverse clause-four padding/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run').requiredTheorems.length, 39);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps_le',
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loop_workRunExact',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.finalTokenBits_eq_encodedFormula_fourthClause',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.remainingPaddingCount_eq_formulaTokensPerClause_sub_nine',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.paddingSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.fifthClauseSlotStart_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.malformedCountdownRoot_timeout',
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run').scope,
    /4328 plus twelve inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fourth-clause-padding-run').nonClaim,
    /does not traverse that empty rectangle/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run').requiredTheorems.length, 39);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps_le',
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loop_workRunExact',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.finalTokenBits_eq_encodedFormula_fourthClause',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.paddingCount_eq_formulaTokensPerClause',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.paddingSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.sixthClauseSlotStart_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.malformedCountdownRoot_timeout',
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run').scope,
    /4380 plus fourteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-fifth-clause-padding-run').nonClaim,
    /does not traverse that sixth rectangle/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run').requiredTheorems.length, 39);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps_le',
    'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.loop_workRunExact',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.workRunExact',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.finalTokenBits_eq_encodedFormula_fourthClause',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.paddingCount_eq_remaining_first_constraint',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.paddingSlot_direct_eq_padding',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.secondConstraintStart_direct_eq_sep',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.malformedCountdownRoot_timeout',
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run').scope,
    /4432 plus sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-first-constraint-padding-run').nonClaim,
    /observes but does not emit that separator/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.machine_acceptState_ne_rejectState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rule_source_ne_acceptState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.finalTokenBits_eq_encodedFormula_secondConstraintStart',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.secondConstraintStartTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.nextTokenSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step').scope,
    /4554 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-separator-step').nonClaim,
    /does not emit the following T/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine_acceptState_ne_rejectState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rule_source_ne_acceptState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSign',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.secondConstraintFirstLiteralSignTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.nextTokenSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step').scope,
    /4676 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-sign-step').nonClaim,
    /does not emit the following unary T/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine_acceptState_ne_rejectState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rule_source_ne_acceptState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralFirstUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.secondConstraintFirstLiteralFirstUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.nextTokenSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step').scope,
    /4798 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step').nonClaim,
    /does not emit the following second unary T/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine_acceptState_ne_rejectState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rule_source_ne_acceptState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSecondUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.secondConstraintFirstLiteralSecondUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.nextTokenSlot_direct_eq_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step').scope,
    /4920 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step').nonClaim,
    /does not emit the following third unary T/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine_acceptState_ne_rejectState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rule_source_ne_acceptState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralThirdUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.nextTokenSlot_direct_eq_f',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step').scope,
    /5042 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step').nonClaim,
    /does not emit the following terminating F/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step').requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
    'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine_acceptState_ne_rejectState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rule_source_ne_acceptState',
    'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralTerminator',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.nextTokenSlot_direct_eq_finish_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.malformedCursorScratch_timeout',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step').scope,
    /5164 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-terminator-step').nonClaim,
    /does not emit the following Finish in the width-one case or the following positive T/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.WidthBranchAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.WidthBranchAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.WidthBranchAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.branchAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSuccessor',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.secondConstraintFirstLiteralSuccessorTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step').scope,
    /5284 plus the eighteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step').nonClaim,
    /does not emit the following padding opportunity at width one or unary T at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_optional_unary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.secondFollowingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintPaddingOrUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.secondConstraintPaddingOrUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step').scope,
    /5404 plus the twenty inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or second unary T at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_two_optional_unary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.thirdFollowingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintSecondPaddingOrUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.secondConstraintSecondPaddingOrUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step').scope,
    /5524 plus the twenty-two inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or third unary T at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_three_optional_unary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.fourthFollowingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintThirdPaddingOrUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step').scope,
    /5644 plus the twenty-four inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or fourth unary T at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_four_optional_unary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.fifthFollowingTokenSlot_direct_eq_padding_or_f',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintFourthPaddingOrUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.secondConstraintFourthPaddingOrUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.followingTokenSlot_direct_eq_padding_or_f',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step').scope,
    /5764 plus the twenty-six inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or terminating F at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_four_optional_unary_and_optional_terminator',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.sixthFollowingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.WidthOptionalTerminatorAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.WidthOptionalTerminatorAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.WidthOptionalTerminatorAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintFifthPaddingOrTerminator',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.secondConstraintFifthPaddingOrTerminatorTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step').scope,
    /5884 plus the twenty-eight inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or opening unary T at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_four_optional_unary_and_optional_terminator_and_optional_opening_unary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.seventhFollowingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintSixthPaddingOrOpeningUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.secondConstraintSixthPaddingOrOpeningUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step').scope,
    /6004 plus the thirty inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or first unary-index T at wider widths/u);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step').status,
  'formalized-foundation-only');
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step').earned, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step').allAssumptionFree, false);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step')
    .axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step')
    .requiredTheorems.length, 40);
  for (const theorem of [
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_four_optional_unary_and_optional_terminator_and_optional_opening_unary_and_optional_first_unary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.eighthFollowingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.optionalAppender_workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.workRunExact',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.finalTokenBits_eq_encodedFormula_secondConstraintSeventhPaddingOrUnary',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.secondConstraintSeventhPaddingOrUnaryTokens_eq_canonical_formula_prefix',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.followingTokenSlot_direct_eq_padding_or_t',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.rawTimeBound_le',
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.work_one_step_short_timeout',
  ]) assert.equal(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step')
    .requiredTheorems.includes(theorem), true, theorem);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step').scope,
    /6124 plus the thirty-two inherited\/generated unary-evaluator rule counts/u);
  assert.match(byId.get(
    'concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step').nonClaim,
    /does not consume the following padding opportunity at width one or second unary-index T at wider widths/u);
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
  const carrierTrace = byId.get('locked-nand-global-carrier-trace-equivalence');
  assert.equal(carrierTrace.status, 'formalized');
  assert.equal(carrierTrace.earned, true);
  assert.equal(carrierTrace.allAssumptionFree, false);
  assert.equal(carrierTrace.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(carrierTrace.requiredTheorems.length, 8);
  for (const theorem of [
    'PNP.DirectWire.LockedNANDTrace.carrierSeparation',
    'PNP.DirectWire.LockedNANDTrace.finalLock_fresh',
    'PNP.DirectWire.LockedNANDTrace.distinguishedChecks_length',
    'PNP.DirectWire.LockedNANDTrace.tracePredicate_coherentExtension',
    'PNP.DirectWire.LockedNANDTrace.trace_sound_of_predicate_true',
    'PNP.DirectWire.LockedNANDTrace.traceEquivalence',
    'PNP.DirectWire.LockedNANDTrace.satisfiable_iff_trace_extension',
    'PNP.DirectWire.LockedNANDTrace.exists_coherent_trace',
  ]) assert.equal(carrierTrace.requiredTheorems.includes(theorem), true, theorem);
  assert.match(carrierTrace.scope,
    /arbitrary finite topological NAND circuits/u);
  assert.match(carrierTrace.nonClaim,
    /does not assemble the complete exposed candidates/u);
  const globalCandidates = byId.get('locked-nand-global-candidate-assembly');
  assert.equal(globalCandidates.status, 'formalized');
  assert.equal(globalCandidates.earned, true);
  assert.equal(globalCandidates.allAssumptionFree, false);
  assert.equal(globalCandidates.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(globalCandidates.requiredTheorems.length, 11);
  for (const theorem of [
    'PNP.DirectWire.LockedNANDGlobalCandidates.macroGateCount_report_formula',
    'PNP.DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount_eq_lockedBaselineCount',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_size',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselinePrefixSource_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_size',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_initial_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_no_internal_constants',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_no_internal_constants',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_finalLock_irrelevant',
  ]) assert.equal(globalCandidates.requiredTheorems.includes(theorem), true, theorem);
  assert.match(globalCandidates.nonClaim, /does not prove global BaselineDistinct/u);
  const baselineDistinct = byId.get('locked-nand-global-baseline-distinct');
  assert.equal(baselineDistinct.status, 'formalized');
  assert.equal(baselineDistinct.earned, true);
  assert.equal(baselineDistinct.allAssumptionFree, false);
  assert.equal(baselineDistinct.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(baselineDistinct.requiredTheorems.length, 5);
  for (const theorem of [
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_outputNonconstant',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_outputNotPositiveProjection',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_outputPairwiseDistinct',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_outputConditions',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_referenceMinimum',
  ]) assert.equal(baselineDistinct.requiredTheorems.includes(theorem), true, theorem);
  assert.match(baselineDistinct.nonClaim, /does not prove either whole-carrier final-output branch law/u);
  const unsatisfiableFinalZero = byId.get(
    'locked-nand-global-unsatisfiable-final-zero',
  );
  assert.equal(unsatisfiableFinalZero.status, 'formalized');
  assert.equal(unsatisfiableFinalZero.earned, true);
  assert.equal(unsatisfiableFinalZero.allAssumptionFree, false);
  assert.equal(
    unsatisfiableFinalZero.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(unsatisfiableFinalZero.requiredTheorems, [
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_eq_false_of_unsatisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable',
  ]);
  assert.match(unsatisfiableFinalZero.scope, /whole carrier/u);
  assert.match(
    unsatisfiableFinalZero.nonClaim,
    /does not prove satisfiable FinalLockSeparation/u,
  );
  const semanticThreshold = byId.get(
    'locked-nand-global-semantic-threshold',
  );
  assert.equal(semanticThreshold.status, 'formalized');
  assert.equal(semanticThreshold.earned, true);
  assert.equal(semanticThreshold.allAssumptionFree, false);
  assert.equal(
    semanticThreshold.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(semanticThreshold.requiredTheorems, [
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_nonconstant_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_notPositiveProjection_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_distinctFromBaseline_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_satisfiableFinalConditions',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_referenceMinimum_bounds_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_residualSlack_le_four',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_satisfiable_iff_referenceMinimum_ge_succ',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable',
  ]);
  assert.match(semanticThreshold.scope, /answer-independent full candidate/u);
  assert.match(semanticThreshold.nonClaim, /does not construct or compile/u);
  const encodedBoundary = byId.get(
    'concrete-locked-nand-encoded-semantic-boundary',
  );
  assert.equal(encodedBoundary.status, 'formalized-semantic-boundary');
  assert.equal(encodedBoundary.earned, true);
  assert.equal(
    encodedBoundary.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(encodedBoundary.requiredTheorems, [
    'PNP.Concrete.LockedNAND.RawCircuit.normalize_idempotent',
    'PNP.Concrete.LockedNAND.RawCircuit.normalize_eval',
    'PNP.Concrete.LockedNAND.RawCircuit.elaborate_ofCircuit',
    'PNP.Concrete.LockedNAND.RawCandidate.elaborate_ofCandidate',
    'PNP.Concrete.LockedNAND.RawLockedInstance.elaborate_ofCandidate',
    'PNP.Concrete.LockedNAND.decodeTokens_encodeTokens',
    'PNP.Concrete.LockedNAND.decodeCircuit_encodeCircuit',
    'PNP.Concrete.LockedNAND.decodeLockedInstance_encodeLockedInstance',
    'PNP.Concrete.LockedNAND.decodeElaboratedCircuit_encodeCircuit_ofCircuit',
    'PNP.Concrete.LockedNAND.encoded_fullCandidate_threshold_iff_satisfiable',
    'PNP.Concrete.LockedNAND.buildLockedNANDInstance_correct',
  ]);
  assert.match(encodedBoundary.scope, /strict version-zero/u);
  assert.match(encodedBoundary.nonClaim, /not a parser\/validator machine/u);
  const sourceParser = byId.get(
    'concrete-locked-nand-source-parser',
  );
  assert.equal(sourceParser.status, 'formalized-foundation-only');
  assert.equal(sourceParser.earned, true);
  assert.equal(
    sourceParser.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(sourceParser.requiredTheorems, [
    'PNP.Concrete.LockedNAND.SourceParser.acceptedTape_outputBits',
    'PNP.Concrete.LockedNAND.SourceParser.allInput_exact',
    'PNP.Concrete.LockedNAND.SourceParser.canonicalSteps_le_validWorkBound',
    'PNP.Concrete.LockedNAND.SourceParser.compiledBoundedDecide_accept_iff',
    'PNP.Concrete.LockedNAND.SourceParser.compiledBoundedDecide_ne_timeout',
    'PNP.Concrete.LockedNAND.SourceParser.compiledMachineOutput_eq_validatedSourceBytes',
    'PNP.Concrete.LockedNAND.SourceParser.compiledStart_blankEquivalent',
    'PNP.Concrete.LockedNAND.SourceParser.decodeCircuitTokens_eq_none_iff_failure',
    'PNP.Concrete.LockedNAND.SourceParser.illFormed_exact',
    'PNP.Concrete.LockedNAND.SourceParser.machine_acceptState_ne_rejectState',
    'PNP.Concrete.LockedNAND.SourceParser.malformed_exact',
    'PNP.Concrete.LockedNAND.SourceParser.rules_length',
    'PNP.Concrete.LockedNAND.SourceParser.rules_pairwise_query_distinct',
    'PNP.Concrete.LockedNAND.SourceParser.statePrograms_length',
    'PNP.Concrete.LockedNAND.SourceParser.validFinalConfiguration_isHalted',
    'PNP.Concrete.LockedNAND.SourceParser.validFinalConfiguration_state',
    'PNP.Concrete.LockedNAND.SourceParser.validRawBound_eq',
    'PNP.Concrete.LockedNAND.SourceParser.validRawTimePolynomial_eval',
    'PNP.Concrete.LockedNAND.SourceParser.validatedSourceBytesPolynomialTimeFunction_output',
    'PNP.Concrete.LockedNAND.SourceParser.wellFormed_exact',
  ]);
  assert.match(sourceParser.scope, /literal nine-symbol finite work machine/u);
  assert.match(sourceParser.nonClaim, /does not emit the locked-NAND target/u);
  const targetEmitter = byId.get(
    'concrete-locked-nand-target-emitter',
  );
  assert.equal(targetEmitter.status, 'formalized-foundation-only');
  assert.equal(targetEmitter.earned, true);
  assert.equal(
    targetEmitter.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(targetEmitter.requiredTheorems, [
    'PNP.Concrete.LockedNAND.RawBuilder.rawLockedInstance_of_elaborate',
    'PNP.Concrete.LockedNAND.RawBuilder.targetBytes_of_elaborated',
    'PNP.Concrete.LockedNAND.TargetEmitterSpec.targetBytes_validatedSourceBytes_eq_buildLockedNANDInstance',
    'PNP.Concrete.LockedNAND.TargetEmitterSpec.targetBytes_size_le',
    'PNP.Concrete.LockedNAND.TargetEmitterController.rules_length_literal',
    'PNP.Concrete.LockedNAND.TargetEmitterController.rules_pairwise',
    'PNP.Concrete.LockedNAND.TargetEmitterController.machine_accept_ne_reject',
    'PNP.Concrete.LockedNAND.TargetEmitterController.graph_wellFormed',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace.malformed_bounded_exact',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace.decoded_bounded_exact',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace.allInput_bounded_exact',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.controllerWorkTimePolynomial_eval',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.allInputWorkTimePolynomial_eval',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial_eval',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.controller_complete_path_polynomial',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.controllerUniformEnvelope_le_workBound',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledStart_blankEquivalent',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledMachineOutput_eq_targetBytes',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledBoundedDecide_accept_iff',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledBoundedDecide_ne_timeout',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.rawTargetBytesPolynomialTimeFunction_output',
    'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction_output',
  ]);
  assert.match(targetEmitter.scope, /1,387,921-rule grammar-only controller/u);
  assert.match(
    targetEmitter.nonClaim,
    /standalone emitter does not itself package the language equivalence as PolynomialReduction/u,
  );
  const polynomialReduction = byId.get(
    'concrete-locked-nand-polynomial-reduction',
  );
  assert.equal(
    polynomialReduction.status,
    'formalized-polynomial-reduction',
  );
  assert.equal(polynomialReduction.earned, true);
  assert.equal(
    polynomialReduction.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(polynomialReduction.requiredTheorems, [
    'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_function',
    'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_output',
    'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_correct',
    'PNP.Concrete.LockedNAND.encodedNANDSAT_reducesTo_encodedLockedNANDThreshold',
    'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_hasRawRefinement',
  ]);
  assert.match(
    polynomialReduction.scope,
    /concrete polynomial many-one reduction/u,
  );
  assert.match(
    polynomialReduction.nonClaim,
    /all-input CNF compiler now identifies CNFSAT/u,
  );
  const cnfToNAND = byId.get(
    'concrete-cnf-to-nand-semantic-compiler',
  );
  assert.equal(cnfToNAND.status, 'formalized-semantic-boundary');
  assert.equal(cnfToNAND.earned, true);
  assert.equal(
    cnfToNAND.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(cnfToNAND.requiredTheorems, [
    'PNP.Concrete.CNFToNAND.encodeCNF_of_decodeEncodedCNF',
    'PNP.Concrete.CNFToNAND.compileFormula_inputCount',
    'PNP.Concrete.CNFToNAND.compileFormula_output_is_gate',
    'PNP.Concrete.CNFToNAND.compileFormula_wellFormed',
    'PNP.Concrete.CNFToNAND.decodeValidCircuit_encode_compileFormula',
    'PNP.Concrete.CNFToNAND.compiledFormulaCircuit_eval_eq_true_iff',
    'PNP.Concrete.CNFToNAND.compiledFormulaCircuit_satisfiable_iff',
    'PNP.Concrete.CNFToNAND.compileFormula_satisfiable_iff',
    'PNP.Concrete.CNFToNAND.formula_satisfiable_iff_encoded_compileFormula',
    'PNP.Concrete.CNFToNAND.compileFormula_gateCount_exact',
    'PNP.Concrete.CNFToNAND.compileFormula_gateCount_le',
    'PNP.Concrete.CNFToNAND.cnfToNANDOutputSizePolynomial_eval',
    'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_of_decoded',
    'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_of_malformed',
    'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_size_le',
    'PNP.Concrete.CNFToNAND.empty_not_encodedNANDSAT',
    'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_correct',
    'PNP.Concrete.CNFToNAND.buildLockedNANDFromCNF_correct',
  ]);
  assert.match(cnfToNAND.scope, /answer-independent compiler/u);
  assert.match(
    cnfToNAND.nonClaim,
    /subsequent all-input milestone supplies the finite-machine/u,
  );
  const cnfToNANDReduction = byId.get(
    'concrete-cnf-to-nand-polynomial-reduction',
  );
  assert.equal(
    cnfToNANDReduction.status,
    'formalized-polynomial-reduction',
  );
  assert.equal(cnfToNANDReduction.earned, true);
  assert.equal(
    cnfToNANDReduction.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(cnfToNANDReduction.requiredTheorems, [
    'PNP.Concrete.CNFSourceParser.allInput_exact',
    'PNP.Concrete.CNFSourceParser.compiledMachineOutput_eq_validatedCNFBytes',
    'PNP.Concrete.CNFSourceParser.compiledBoundedDecide_ne_timeout',
    'PNP.Concrete.CNFToNANDCarrierEncoder.canonical_exact',
    'PNP.Concrete.CNFToNANDCarrierEncoder.canonicalWorkSteps_polynomial_bound',
    'PNP.Concrete.CNFToNANDWorkspace.exact_execution_output',
    'PNP.Concrete.CNFToNANDController.rules_length_literal',
    'PNP.Concrete.CNFToNANDControllerTotalTrace.canonical_path',
    'PNP.Concrete.CNFToNANDControllerTotalTrace.canonical_bounded_exact',
    'PNP.Concrete.CNFToNANDCompilerMachine.rules_length_literal',
    'PNP.Concrete.CNFToNANDCompilerTotalTrace.malformed_bounded_exact',
    'PNP.Concrete.CNFToNANDCompilerTotalTrace.decoded_bounded_exact',
    'PNP.Concrete.CNFToNANDCompilerTotalTrace.allInput_bounded_exact',
    'PNP.Concrete.CNFToNANDCompilerPolynomialBound.allInputWorkTimePolynomial_eval',
    'PNP.Concrete.CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial_eval',
    'PNP.Concrete.CNFToNANDCompilerCompiled.compiledMachineOutput_eq_compileEncodedCNFToNAND',
    'PNP.Concrete.CNFToNANDCompilerCompiled.compiledBoundedDecide_accept_iff',
    'PNP.Concrete.CNFToNANDCompilerCompiled.compiledBoundedDecide_ne_timeout',
    'PNP.Concrete.CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output',
    'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_function',
    'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_output',
    'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_correct',
    'PNP.Concrete.CNFToNAND.cnfSAT_reducesTo_encodedNANDSAT',
    'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_hasRawRefinement',
    'PNP.Concrete.CNFToNAND.cnfToLockedNANDPolynomialReduction_output',
    'PNP.Concrete.CNFToNAND.cnfToLockedNANDPolynomialReduction_correct',
    'PNP.Concrete.CNFToNAND.cnfSAT_reducesTo_encodedLockedNANDThreshold',
    'PNP.Concrete.CNFToNAND.cnfToLockedNANDPolynomialReduction_hasRawRefinement',
  ]);
  assert.match(cnfToNANDReduction.scope, /fixed 135,070-rule/u);
  assert.match(
    cnfToNANDReduction.nonClaim,
    /does not itself decide CNF-SAT/u,
  );
  assert.equal(byId.get('locked-nand-conditional-threshold').status, 'formalized-with-premises');
  assert.equal(byId.get('explicit-residual-routes').status, 'formalized-explicit-list-only');
  const residualGainChain = byId.get('residual-gain-chain-bound');
  assert.equal(residualGainChain.status, 'formalized-iteration-bound-only');
  assert.equal(residualGainChain.earned, true);
  assert.equal(residualGainChain.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(residualGainChain.requiredTheorems, [
    'PNP.DirectWire.StrictEquivalentGain.strictResidualDescent',
    'PNP.DirectWire.strictGainChainBool_eq_true_iff',
    'PNP.DirectWire.StrictGainChain.end_equivalent',
    'PNP.DirectWire.StrictGainChain.end_referenceMinimum_eq',
    'PNP.DirectWire.StrictGainChain.end_residualSlack_add_length_le',
    'PNP.DirectWire.StrictGainChain.length_le_residualSlack',
    'PNP.DirectWire.strictGainChainBool_length_le_residualSlack',
    'PNP.DirectWire.strictGainChainBool_length_le_of_residualSlack_le',
    'PNP.DirectWire.StrictGainChain.eq_nil_of_residualSlack_eq_zero',
    'PNP.DirectWire.strictGainChainBool_eq_nil_of_residualSlack_eq_zero',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_residualSlack_le_four',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidateImplementation_residualSlack_le_four',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_strictGainChain_length_le_four',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_strictGainChainBool_length_le_four',
  ]);
  assert.match(residualGainChain.nonClaim, /does not find the next gain/u);
  const residualGainStopping = byId.get('residual-gain-stopping-specification');
  assert.equal(residualGainStopping.status, 'formalized-semantic-stopping-only');
  assert.equal(residualGainStopping.earned, true);
  assert.equal(residualGainStopping.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(residualGainStopping.requiredTheorems, [
    'PNP.DirectWire.referenceMinimumImplementation_gateCount_eq_referenceMinimum',
    'PNP.DirectWire.referenceMinimumImplementation_equivalent',
    'PNP.DirectWire.referenceMinimumImplementation_isSemanticallyMinimum',
    'PNP.DirectWire.referenceMinimumImplementation_residualSlack_eq_zero',
    'PNP.DirectWire.referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos',
    'PNP.DirectWire.residualSlack_pos_iff_exists_strictEquivalentGain',
    'PNP.DirectWire.residualSlack_eq_zero_iff_forall_not_strictEquivalentGain',
    'PNP.DirectWire.isSemanticallyMinimum_iff_forall_not_strictEquivalentGain',
    'PNP.DirectWire.StrictGainChain.end_residualSlack_eq_zero_of_no_strictEquivalentGain',
    'PNP.DirectWire.strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain',
  ]);
  assert.match(residualGainStopping.nonClaim, /semantic stopping criterion/u);
  assert.match(residualGainStopping.nonClaim, /does not derive global absence from a finite scan/u);
  const terminalFullBridge = byId.get('residual-terminal-full-carrier-bridge');
  assert.equal(terminalFullBridge.status,
    'formalized-terminal-full-mode-semantic-bridge');
  assert.equal(terminalFullBridge.earned, true);
  assert.equal(terminalFullBridge.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalFullBridge.requiredTheorems, [
    'PNP.DirectWire.terminalize_implementation',
    'PNP.DirectWire.terminalize_gateCount',
    'PNP.DirectWire.TerminalFullRealization.realize_equivalent',
    'PNP.DirectWire.TerminalFullRealization.realize_semantics',
    'PNP.DirectWire.referenceMinimumTerminalFullRealization_gateCount',
    'PNP.DirectWire.terminalFullMinimum_eq_referenceMinimum',
    'PNP.DirectWire.terminalFullMinimum_spec',
    'PNP.DirectWire.isTerminalFullMinimum_iff_eq_terminalFullMinimum',
    'PNP.DirectWire.isTerminalFullMinimum_iff_eq_referenceMinimum',
    'PNP.DirectWire.WholeSpanResidualWitness.strictResidualDescent',
    'PNP.DirectWire.residualSlack_pos_iff_exists_wholeSpanResidualWitness',
    'PNP.DirectWire.residualSlack_eq_zero_iff_no_wholeSpanResidualWitness',
    'PNP.DirectWire.StrictEquivalentGain.strictResidualDescent',
  ]);
  assert.match(terminalFullBridge.scope, /every input\/output coordinate/u);
  assert.match(terminalFullBridge.nonClaim, /does not formalize the quotient carrier/u);
  const terminalModeFirewall = byId.get('residual-terminal-mode-firewall');
  assert.equal(terminalModeFirewall.status,
    'formalized-terminal-mode-firewall');
  assert.equal(terminalModeFirewall.earned, true);
  assert.equal(terminalModeFirewall.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalModeFirewall.requiredTheorems, [
    'PNP.DirectWire.TerminalFullCarrierRealization.project_realization',
    'PNP.DirectWire.TerminalFullCarrierRealization.project_implementation',
    'PNP.DirectWire.TerminalFullCarrierRealization.project_gateCount',
    'PNP.DirectWire.TerminalFullCarrierRealization.project_equivalent',
    'PNP.DirectWire.TerminalFullCarrierRealization.project_semantics',
    'PNP.DirectWire.TerminalCheckedFullLift.fullRealization_realization',
    'PNP.DirectWire.TerminalCheckedFullLift.fullRealization_profileEqual',
    'PNP.DirectWire.terminalCheckedFullLift_iff_fullProfileEqual',
    'PNP.DirectWire.TerminalQuotientComparison.checkedFullLift_of_keepsAll',
    'PNP.DirectWire.TerminalFullCarrierRealization.obligationsDischarged',
    'PNP.DirectWire.TerminalCheckedFullLift.obligationsDischarged',
    'PNP.DirectWire.terminalQuotientEqualityNotConstructive',
  ]);
  assert.match(terminalModeFirewall.scope, /computed finite profile observer/u);
  assert.match(terminalModeFirewall.nonClaim, /no proper or governed supports/u);
  const terminalProjectionMinimum = byId.get('residual-terminal-projection-minimum');
  assert.equal(terminalProjectionMinimum.status,
    'formalized-terminal-projection-minimum');
  assert.equal(terminalProjectionMinimum.earned, true);
  assert.equal(terminalProjectionMinimum.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalProjectionMinimum.requiredTheorems, [
    'PNP.DirectWire.terminalFullProfileMatchBool_complete',
    'PNP.DirectWire.terminalQuotientProfileMatchBool_complete',
    'PNP.DirectWire.terminalFullProfileMinimumRealization_gateCount',
    'PNP.DirectWire.terminalQuotientProfileMinimumComparison_gateCount',
    'PNP.DirectWire.terminalFullProfileMinimum_le',
    'PNP.DirectWire.terminalQuotientProfileMinimum_le',
    'PNP.DirectWire.terminalFullProfileMinimum_spec',
    'PNP.DirectWire.terminalQuotientProfileMinimum_spec',
    'PNP.DirectWire.terminalProjectionMinimum_mono',
    'PNP.DirectWire.terminalQuotientMinimum_add_projectionDefect',
    'PNP.DirectWire.terminalProjectionDefect_eq_zero_iff_minima_eq',
    'PNP.DirectWire.terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum',
    'PNP.DirectWire.terminalProfileMinima_eq_of_keepsAll',
    'PNP.DirectWire.terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum',
  ]);
  assert.match(terminalProjectionMinimum.scope, /complete enumeration through the current gate count/u);
  assert.match(terminalProjectionMinimum.nonClaim, /no polynomial runtime/u);
  const terminalProjectionTransfer = byId.get('residual-terminal-projection-transfer');
  assert.equal(terminalProjectionTransfer.status,
    'formalized-terminal-projection-transfer');
  assert.equal(terminalProjectionTransfer.earned, true);
  assert.equal(terminalProjectionTransfer.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalProjectionTransfer.requiredTheorems, [
    'PNP.DirectWire.terminalProjectionDefect_int',
    'PNP.DirectWire.TerminalProjectionFourCorners.transferIdentity',
    'PNP.DirectWire.TerminalProjectionFourCorners.constantCutEquation_of_defects',
    'PNP.DirectWire.TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut',
  ]);
  assert.match(terminalProjectionTransfer.scope, /signed full and quotient minimum deltas/u);
  assert.match(terminalProjectionTransfer.nonClaim, /does not construct or certify a proper governed support square/u);
  const terminalSaturation = byId.get('residual-terminal-saturation-closure');
  assert.equal(terminalSaturation.status,
    'formalized-terminal-saturation-closure');
  assert.equal(terminalSaturation.earned, true);
  assert.equal(terminalSaturation.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalSaturation.requiredTheorems, [
    'PNP.DirectWire.mem_allTerminalPrimitiveRecords',
    'PNP.DirectWire.terminalSaturate_extensive',
    'PNP.DirectWire.terminalSaturate_closed',
    'PNP.DirectWire.terminalSaturate_least',
    'PNP.DirectWire.terminalSaturate_monotone',
    'PNP.DirectWire.terminalSaturate_idempotent',
    'PNP.DirectWire.terminalSaturate_fixed_iff_closed',
  ]);
  assert.match(terminalSaturation.scope, /reflexive transitive closure/u);
  assert.match(terminalSaturation.nonClaim, /does not derive the dependency relation from an arbitrary circuit/u);
  const terminalPhysicalSupport = byId.get('residual-terminal-physical-support-completion');
  assert.equal(terminalPhysicalSupport.status,
    'formalized-terminal-physical-support-completion');
  assert.equal(terminalPhysicalSupport.earned, true);
  assert.equal(terminalPhysicalSupport.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalPhysicalSupport.requiredTheorems, [
    'PNP.DirectWire.mem_allTerminalSaturationRuleKinds',
    'PNP.DirectWire.terminalSaturationEdge_eq_true_iff',
    'PNP.DirectWire.terminalSaturateRecords_extensive',
    'PNP.DirectWire.terminalSaturateRecords_sound',
    'PNP.DirectWire.terminalSaturateRecords_closed',
    'PNP.DirectWire.mem_terminalSaturateRecords_iff',
    'PNP.DirectWire.mem_allTerminalSupportWires',
    'PNP.DirectWire.mem_terminalBoundaryPorts_iff',
    'PNP.DirectWire.mem_terminalInterfacePorts_iff',
    'PNP.DirectWire.completeTerminalPhysicalSupport_incoming_complete',
    'PNP.DirectWire.completeTerminalPhysicalSupport_outgoing_complete',
    'PNP.DirectWire.completeTerminalPhysicalSupport_compatible',
    'PNP.DirectWire.completeSaturatedTerminalPhysicalSupport_records',
    'PNP.DirectWire.completeSaturatedTerminalPhysicalSupport_compatible',
  ]);
  assert.match(terminalPhysicalSupport.scope, /deterministic finite work list/u);
  assert.match(terminalPhysicalSupport.nonClaim, /proper positive support/u);
  const terminalSupportExtraction = byId.get('residual-terminal-support-extraction');
  assert.equal(terminalSupportExtraction.status,
    'formalized-terminal-support-extraction');
  assert.equal(terminalSupportExtraction.earned, true);
  assert.equal(terminalSupportExtraction.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalSupportExtraction.requiredTheorems, [
    'PNP.DirectWire.mem_terminalSelectedGateIndices_iff',
    'PNP.DirectWire.mem_terminalSelectedGates_iff',
    'PNP.DirectWire.terminalSelectedGateIndices_nodup',
    'PNP.DirectWire.terminalSelectedGates_nodup',
    'PNP.DirectWire.extractTerminalSupport_records',
    'PNP.DirectWire.extractTerminalSupport_boundary',
    'PNP.DirectWire.extractTerminalSupport_selectedGates',
    'PNP.DirectWire.extractTerminalSupport_interface',
    'PNP.DirectWire.extractTerminalSupport_gateCount',
    'PNP.DirectWire.terminalOpenGateEvaluation_induced_selected',
    'PNP.DirectWire.terminalOpenSupportSemantics_induced',
    'PNP.DirectWire.extractTerminalSupport_semantics',
    'PNP.DirectWire.extractTerminalSupport_induced',
    'PNP.DirectWire.extractSaturatedTerminalSupport_records',
    'PNP.DirectWire.extractSaturatedTerminalSupport_gateCount',
    'PNP.DirectWire.extractSaturatedTerminalSupport_semantics',
    'PNP.DirectWire.extractSaturatedTerminalSupport_induced',
    'PNP.DirectWire.mem_terminalSaturateRecords_iff',
    'PNP.DirectWire.completeTerminalPhysicalSupport_incoming_complete',
    'PNP.DirectWire.completeTerminalPhysicalSupport_compatible',
    'PNP.DirectWire.completeSaturatedTerminalPhysicalSupport_compatible',
  ]);
  assert.match(terminalSupportExtraction.scope, /noncontiguous selections/u);
  assert.match(terminalSupportExtraction.nonClaim, /proper positive support/u);
  const terminalProperSupport = byId.get('residual-terminal-proper-positive-support-search');
  assert.equal(terminalProperSupport.status,
    'formalized-governed-proper-positive-support-search');
  assert.equal(terminalProperSupport.earned, true);
  assert.equal(terminalProperSupport.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalProperSupport.requiredTheorems, [
    'PNP.DirectWire.canonicalTerminalSupportSeed_mem',
    'PNP.DirectWire.mem_canonicalTerminalSupportSeed_iff',
    'PNP.DirectWire.terminalProperPositiveSupportBool_eq_true_iff',
    'PNP.DirectWire.findTerminalProperPositiveSupport_sound',
    'PNP.DirectWire.findTerminalProperPositiveSupport_exists_of_seed',
    'PNP.DirectWire.findTerminalProperPositiveSupport_eq_none_iff',
    'PNP.DirectWire.findTerminalProperPositiveSupport_unique',
    'PNP.DirectWire.TerminalProperPositiveSupport.saturatedRecords_closed',
    'PNP.DirectWire.TerminalProperPositiveSupport.physically_compatible',
    'PNP.DirectWire.TerminalProperPositiveSupport.gateCount_bounds',
    'PNP.DirectWire.TerminalProperPositiveSupport.extracted_semantics',
    'PNP.DirectWire.TerminalProperPositiveSupport.extracted_induced',
    'PNP.DirectWire.TerminalProperPositiveSupport.minimumReplacement_equivalent',
    'PNP.DirectWire.TerminalProperPositiveSupport.referenceMinimum_lt_gateCount',
    'PNP.DirectWire.TerminalProperPositiveSupport.minimumReplacement_size_lt',
    'PNP.DirectWire.mem_terminalSaturateRecords_iff',
    'PNP.DirectWire.completeSaturatedTerminalPhysicalSupport_compatible',
    'PNP.DirectWire.extractSaturatedTerminalSupport_gateCount',
    'PNP.DirectWire.extractSaturatedTerminalSupport_semantics',
    'PNP.DirectWire.extractSaturatedTerminalSupport_induced',
    'PNP.DirectWire.Candidate.referenceMinimumReplacement_equivalent',
    'PNP.DirectWire.Candidate.referenceMinimumReplacement_size',
  ]);
  assert.match(terminalProperSupport.scope, /complete canonical finite universe/u);
  assert.match(terminalProperSupport.nonClaim, /exhaustive reference computation/u);
  const terminalSupportSquare = byId.get(
    'residual-terminal-saturated-support-square-closure',
  );
  assert.equal(terminalSupportSquare.status,
    'formalized-terminal-saturated-support-square-closure');
  assert.equal(terminalSupportSquare.earned, true);
  assert.equal(terminalSupportSquare.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(terminalSupportSquare.requiredTheorems, [
    'PNP.DirectWire.TerminalSaturatedSupportSquare.mem_meetRecords_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.leftRecords_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.rightRecords_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.meetRecords_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.mem_joinRecords_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.joinRecords_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.records_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.meetRecords_subset_left',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.meetRecords_subset_right',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.leftRecords_subset_join',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.rightRecords_subset_join',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.meetRecords_greatest',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.joinRecords_least',
    'PNP.DirectWire.terminalSaturateRecords_mem_congr',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.records_congr',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.physically_compatible',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.extracted_gateCount',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.extracted_semantics',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.extracted_induced',
    'PNP.DirectWire.mem_terminalSaturateRecords_iff',
    'PNP.DirectWire.completeTerminalPhysicalSupport_compatible',
    'PNP.DirectWire.extractTerminalSupport_semantics',
    'PNP.DirectWire.extractTerminalSupport_induced',
  ]);
  assert.match(terminalSupportSquare.scope, /pair of finite terminal seeds/u);
  assert.match(terminalSupportSquare.nonClaim, /projection-compatible square/u);
  const terminalGovernedCompletion = byId.get(
    'residual-terminal-governed-support-completion',
  );
  assert.equal(terminalGovernedCompletion.status,
    'formalized-terminal-governed-support-completion');
  assert.equal(terminalGovernedCompletion.earned, true);
  assert.equal(
    terminalGovernedCompletion.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalGovernedCompletion.requiredTheorems, [
    'PNP.DirectWire.mem_allTerminalProfileRoles',
    'PNP.DirectWire.mem_terminalProfileCoordinatesForRole_iff',
    'PNP.DirectWire.terminalProfileCoordinatesForRole_nodup',
    'PNP.DirectWire.completeTerminalGovernedSupport_records',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.frontier_boundary',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.frontier_interface',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.mem_profileCoordinates_iff',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.profileCoordinates_nodup',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.mem_own_profile_role_iff',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.profile_role_unique',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.profileCoordinates_disjoint',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.profile_record_covered_iff',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.required_mem',
    'PNP.DirectWire.TerminalGovernedCompletedSupport.required_profile_mem',
    'PNP.DirectWire.completeSaturatedTerminalGovernedSupport_records',
    'PNP.DirectWire.completeSaturatedTerminalGovernedSupport_compatible',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_records',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_compatible',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_required_mem',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_required_profile_mem',
    'PNP.DirectWire.completeTerminalPhysicalSupport_compatible',
    'PNP.DirectWire.terminalSaturateRecords_closed',
    'PNP.DirectWire.mem_terminalSaturateRecords_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.records_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.physically_compatible',
  ]);
  assert.match(terminalGovernedCompletion.scope, /ten terminal profile roles/u);
  assert.match(terminalGovernedCompletion.nonClaim, /dependency system remains explicit/u);
  const terminalFrontierPushout = byId.get(
    'residual-terminal-governed-frontier-pushout',
  );
  assert.equal(terminalFrontierPushout.status,
    'formalized-terminal-governed-frontier-pushout');
  assert.equal(terminalFrontierPushout.earned, true);
  assert.equal(
    terminalFrontierPushout.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalFrontierPushout.requiredTheorems, [
    'PNP.DirectWire.allTerminalSupportWires_nodup',
    'PNP.DirectWire.TerminalGovernedFrontier.extensionality',
    'PNP.DirectWire.mem_terminalBoundaryFrontierPushout_iff',
    'PNP.DirectWire.mem_terminalInterfaceFrontierPushout_iff',
    'PNP.DirectWire.mem_terminalProfileFrontierPushout_iff',
    'PNP.DirectWire.terminalBoundaryFrontierPushout_nodup',
    'PNP.DirectWire.terminalInterfaceFrontierPushout_nodup',
    'PNP.DirectWire.terminalProfileFrontierPushout_nodup',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_profile_eq_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.side_profile_mem_join',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.left_boundary_disposition',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.right_boundary_disposition',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.side_interface_disposition',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governed_frontier_pushout',
    'PNP.DirectWire.terminalGateSelected_eq_true_iff',
    'PNP.DirectWire.terminalWireExternal_eq_true_iff',
    'PNP.DirectWire.terminalBoundaryWire_eq_true_iff',
    'PNP.DirectWire.terminalGateHasExternalConsumer_eq_true_iff',
    'PNP.DirectWire.terminalInterfaceGate_eq_true_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.mem_meetRecords_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.mem_joinRecords_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.records_closed',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.physically_compatible',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_profile_iff',
  ]);
  assert.match(terminalFrontierPushout.scope, /computed saturated support square/u);
  assert.match(terminalFrontierPushout.nonClaim, /projection compatibility/u);
  const terminalProjectionSquare = byId.get(
    'residual-terminal-governed-projection-square',
  );
  assert.equal(terminalProjectionSquare.status,
    'formalized-terminal-governed-projection-square');
  assert.equal(terminalProjectionSquare.earned, true);
  assert.equal(
    terminalProjectionSquare.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalProjectionSquare.requiredTheorems, [
    'PNP.DirectWire.TerminalGovernedFrontier.project_boundary',
    'PNP.DirectWire.TerminalGovernedFrontier.project_interface',
    'PNP.DirectWire.TerminalGovernedFrontier.mem_project_profiles_iff',
    'PNP.DirectWire.TerminalGovernedFrontier.project_profiles_nodup',
    'PNP.DirectWire.TerminalGovernedFrontier.project_idempotent',
    'PNP.DirectWire.mem_terminalProjectedGovernedFrontierPushout_profiles_iff',
    'PNP.DirectWire.TerminalGovernedFrontier.project_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.projectedFrontier_boundary',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.projectedFrontier_interface',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.mem_projectedFrontier_profiles_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.projectedFrontier_profiles_nodup',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.forgotten_not_mem_projectedFrontier',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.projected_meet_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.projected_join_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.projected_join_eq_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governed_projection_compatible',
    'PNP.DirectWire.TerminalGovernedFrontier.extensionality',
    'PNP.DirectWire.mem_terminalProfileFrontierPushout_iff',
    'PNP.DirectWire.terminalProfileFrontierPushout_nodup',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governed_frontier_pushout',
  ]);
  assert.match(terminalProjectionSquare.scope, /forgetful terminal projection/u);
  assert.match(terminalProjectionSquare.nonClaim, /BN2 square legitimacy/u);
  const terminalSideTightMinimum = byId.get(
    'residual-terminal-side-tight-minimum-arithmetic',
  );
  assert.equal(terminalSideTightMinimum.status,
    'formalized-residual-terminal-side-tight-minimum-arithmetic');
  assert.equal(terminalSideTightMinimum.earned, true);
  assert.equal(
    terminalSideTightMinimum.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalSideTightMinimum.requiredTheorems, [
    'PNP.DirectWire.TerminalFourCornerSizes.componentwiseLE_refl',
    'PNP.DirectWire.TerminalFourCornerSizes.numericallySideTight_iff_eq',
    'PNP.DirectWire.TerminalFourCornerSizes.sideTightBool_eq_true_iff',
    'PNP.DirectWire.TerminalFourCornerSizes.tightValue?_eq_some_iff',
    'PNP.DirectWire.TerminalFourCornerSizes.tightValue?_sound',
    'PNP.DirectWire.TerminalFourCornerSizes.tightValue?_complete',
    'PNP.DirectWire.TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks',
    'PNP.DirectWire.TerminalProjectionFourCorners.fullMinimumSizes_incidenceValue',
    'PNP.DirectWire.TerminalFullFourCornerBasis.minimum_componentwiseLE_sizes',
    'PNP.DirectWire.TerminalFullFourCornerBasis.incidenceValue_eq_fullDelta_add_slacks',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalFullBasis_sizes',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalFullBasis_tightValue?',
    'PNP.DirectWire.TerminalProjectionFourCorners.quotientMinimumSizes_incidenceValue',
    'PNP.DirectWire.TerminalQuotientFourCornerBasis.minimum_componentwiseLE_sizes',
    'PNP.DirectWire.TerminalQuotientFourCornerBasis.incidenceValue_eq_quotientDelta_add_slacks',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalQuotientBasis_sizes',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalQuotientBasis_tightValue?',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonical_numericallySideTight_values',
    'PNP.DirectWire.terminalFullProfileMinimumRealization_gateCount',
    'PNP.DirectWire.terminalQuotientProfileMinimumComparison_gateCount',
    'PNP.DirectWire.terminalFullProfileMinimum_le',
    'PNP.DirectWire.terminalQuotientProfileMinimum_le',
  ]);
  assert.match(terminalSideTightMinimum.scope,
    /every finite terminal projection four-corner family/u);
  assert.match(terminalSideTightMinimum.scope, /independently attained/u);
  assert.match(terminalSideTightMinimum.nonClaim, /coherent four-corner basis/u);
  assert.match(terminalSideTightMinimum.nonClaim, /BN2 square legitimacy/u);
  const terminalFourCornerCarrier = byId.get(
    'residual-terminal-four-corner-carrier-transport',
  );
  assert.equal(terminalFourCornerCarrier.status,
    'formalized-residual-terminal-four-corner-carrier-transport');
  assert.equal(terminalFourCornerCarrier.earned, true);
  assert.equal(
    terminalFourCornerCarrier.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalFourCornerCarrier.requiredTheorems, [
    'PNP.DirectWire.TerminalFourCornerCarrier.boundaryDisposition?_eq_some_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.interfaceDisposition?_eq_some_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.boundary_nodup',
    'PNP.DirectWire.TerminalFourCornerCarrier.interface_nodup',
    'PNP.DirectWire.TerminalFourCornerCarrier.profile_nodup',
    'PNP.DirectWire.TerminalFourCornerCarrier.extracted_boundary',
    'PNP.DirectWire.TerminalFourCornerCarrier.extracted_interface',
    'PNP.DirectWire.TerminalFourCornerCarrier.corner_compatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.meet_profile_transport',
    'PNP.DirectWire.TerminalFourCornerCarrier.side_profile_transport',
    'PNP.DirectWire.TerminalFourCornerCarrier.join_profile_transport',
    'PNP.DirectWire.TerminalFourCornerCarrier.boundary_retained',
    'PNP.DirectWire.TerminalFourCornerCarrier.boundary_internalized',
    'PNP.DirectWire.TerminalFourCornerCarrier.interface_retained',
    'PNP.DirectWire.TerminalFourCornerCarrier.interface_internalized',
    'PNP.DirectWire.TerminalFourCornerCarrier.projection_compatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.complete_transport',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_compatible',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.side_profile_mem_join',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.left_boundary_disposition',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.right_boundary_disposition',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.side_interface_disposition',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governed_projection_compatible',
  ]);
  assert.match(terminalFourCornerCarrier.scope,
    /every finite computed saturated terminal support square/u);
  assert.match(terminalFourCornerCarrier.scope, /common ambient coordinates/u);
  assert.match(terminalFourCornerCarrier.nonClaim, /four-corner optimum/u);
  assert.match(terminalFourCornerCarrier.nonClaim, /BN2 square legitimacy/u);
  const terminalFourCornerOptimumCompatibility = byId.get(
    'residual-terminal-four-corner-optimum-carrier-compatibility',
  );
  assert.equal(terminalFourCornerOptimumCompatibility.status,
    'formalized-residual-terminal-four-corner-optimum-carrier-compatibility');
  assert.equal(terminalFourCornerOptimumCompatibility.earned, true);
  assert.equal(
    terminalFourCornerOptimumCompatibility.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalFourCornerOptimumCompatibility.requiredTheorems, [
    'PNP.DirectWire.terminalSupportWireAt_ambientIndex',
    'PNP.DirectWire.TerminalSupportWire.ambientIndex_terminalSupportWireAt',
    'PNP.DirectWire.TerminalSupportWire.ambientIndex_injective',
    'PNP.DirectWire.TerminalFourCornerCarrier.boundaryIndex?_eq_some_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.interfaceIndex?_eq_some_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.boundaryIndex?_ambient_get',
    'PNP.DirectWire.TerminalFourCornerCarrier.interfaceIndex?_get',
    'PNP.DirectWire.TerminalFourCornerCarrier.boundaryAdapter_semantics_get',
    'PNP.DirectWire.TerminalFourCornerCarrier.ambientizeCandidate_semantics_present',
    'PNP.DirectWire.TerminalFourCornerCarrier.ambientizeCandidate_semantics_absent',
    'PNP.DirectWire.TerminalFourCornerCarrier.localizeCandidate_semantics',
    'PNP.DirectWire.TerminalFourCornerCarrier.localize_ambientize_semantics',
    'PNP.DirectWire.TerminalFourCornerCarrier.ambientizeCandidate_gateCount',
    'PNP.DirectWire.TerminalFourCornerCarrier.localizeCandidate_gateCount',
    'PNP.DirectWire.TerminalFourCornerCarrier.ambientizeCandidate_equivalent',
    'PNP.DirectWire.TerminalFourCornerCarrier.localizeCandidate_equivalent',
    'PNP.DirectWire.TerminalFourCornerCarrier.localize_ambientize_equivalent',
    'PNP.DirectWire.TerminalFourCornerCarrier.localizeImplementation_gateCount',
    'PNP.DirectWire.TerminalFourCornerCarrier.ambient_referenceMinimum_eq_corner',
    'PNP.DirectWire.TerminalFourCornerCarrier.optimizationCorners_at',
    'PNP.DirectWire.TerminalFourCornerCarrier.optimizationCorners_role',
    'PNP.DirectWire.TerminalFourCornerCarrier.optimizationCorners_projection',
    'PNP.DirectWire.TerminalFourCornerCarrier.localizeRealization_gateCount',
    'PNP.DirectWire.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.complete_transport',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalFullBasis_sizes',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalQuotientBasis_sizes',
    'PNP.DirectWire.terminalFullProfileMinimumRealization_gateCount',
    'PNP.DirectWire.terminalQuotientProfileMinimumComparison_gateCount',
    'PNP.DirectWire.referenceMinimum_le_of_equivalent',
  ]);
  assert.match(terminalFourCornerOptimumCompatibility.scope,
    /every finite computed saturated terminal support square/u);
  assert.match(terminalFourCornerOptimumCompatibility.scope,
    /one common ambient carrier/u);
  assert.match(terminalFourCornerOptimumCompatibility.nonClaim, /coherent transport/u);
  assert.match(terminalFourCornerOptimumCompatibility.nonClaim, /BN2 square legitimacy/u);
  const terminalFourCornerOptimumCoherence = byId.get(
    'residual-terminal-four-corner-optimum-coherence-dichotomy',
  );
  assert.equal(terminalFourCornerOptimumCoherence.status,
    'formalized-residual-terminal-four-corner-optimum-coherence-dichotomy');
  assert.equal(terminalFourCornerOptimumCoherence.earned, true);
  assert.equal(
    terminalFourCornerOptimumCoherence.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalFourCornerOptimumCoherence.requiredTheorems, [
    'PNP.DirectWire.TerminalOptimumLegTransport.recordsSubset',
    'PNP.DirectWire.TerminalOptimumLegTransport.profileTransport',
    'PNP.DirectWire.TerminalOptimumLegTransport.ambientCoordinate_exact',
    'PNP.DirectWire.TerminalOptimumLegTransport.retainedOutput?_eq_some_iff',
    'PNP.DirectWire.TerminalOptimumLegTransport.retained_or_internalized',
    'PNP.DirectWire.TerminalFourCornerCarrier.optimumTransportTheta',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumModeMismatch?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.noFailure_iff_coherentOptimumTuple',
    'PNP.DirectWire.TerminalFourCornerCarrier.classifyOptimumCoherence_exhaustive',
    'PNP.DirectWire.TerminalFourCornerCarrier.fourCornerOptimumCoherenceDichotomy',
    'PNP.DirectWire.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.complete_transport',
    'PNP.DirectWire.TerminalFourCornerCarrier.meet_profile_transport',
    'PNP.DirectWire.TerminalFourCornerCarrier.side_profile_transport',
    'PNP.DirectWire.TerminalFourCornerCarrier.interfaceIndex?_eq_some_iff',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonical_numericallySideTight_values',
  ]);
  assert.match(terminalFourCornerOptimumCoherence.scope,
    /every finite computed terminal support square/u);
  assert.match(terminalFourCornerOptimumCoherence.scope,
    /deterministic first failure/u);
  assert.match(terminalFourCornerOptimumCoherence.nonClaim, /no-outcome route/u);
  assert.match(terminalFourCornerOptimumCoherence.nonClaim,
    /sideTightCompletionExists/u);
  const terminalFourCornerSideTightCompletion = byId.get(
    'residual-terminal-four-corner-side-tight-completion',
  );
  assert.equal(terminalFourCornerSideTightCompletion.status,
    'formalized-residual-terminal-four-corner-side-tight-completion-under-local-route-silence');
  assert.equal(terminalFourCornerSideTightCompletion.earned, true);
  assert.equal(
    terminalFourCornerSideTightCompletion.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalFourCornerSideTightCompletion.requiredTheorems, [
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumRoute?_coherence',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumRoute?_quotientPromotion',
    'PNP.DirectWire.TerminalFourCornerOptimumRoutedFailure.sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.noOptimumCoherenceRoute_iff_noFailure',
    'PNP.DirectWire.TerminalFourCornerCarrier.noOptimumPromotionRoute_iff_noModeMismatch',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumRoute?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletionOrFirstRoute',
    'PNP.DirectWire.TerminalFourCornerOptimumRoutedFailure.excludesCoherentOptimum',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletionExists',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletionExistsEachMode',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletion_fullValue',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletion_quotientValue',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumModeMismatch?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.noFailure_iff_coherentOptimumTuple',
    'PNP.DirectWire.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.optimumTransportTheta',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight',
    'PNP.DirectWire.TerminalProjectionFourCorners.canonical_numericallySideTight_values',
  ]);
  assert.match(terminalFourCornerSideTightCompletion.scope,
    /every finite computed terminal support square/u);
  assert.match(terminalFourCornerSideTightCompletion.scope, /local route silence/u);
  assert.match(terminalFourCornerSideTightCompletion.nonClaim,
    /complete global no-outcome route system/u);
  assert.match(terminalFourCornerSideTightCompletion.nonClaim,
    /BN2 square legitimacy/u);
  const terminalFourCornerTightBasisMaximum = byId.get(
    'residual-terminal-four-corner-tight-basis-maximum',
  );
  assert.equal(terminalFourCornerTightBasisMaximum.status,
    'formalized-residual-terminal-four-corner-complete-tight-basis-maximum');
  assert.equal(terminalFourCornerTightBasisMaximum.earned, true);
  assert.equal(
    terminalFourCornerTightBasisMaximum.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalFourCornerTightBasisMaximum.requiredTheorems, [
    'PNP.DirectWire.TerminalOptimumCoherenceMode.minimumAt_le_current',
    'PNP.DirectWire.TerminalProjectionFourCorners.mem_minimumImplementationsAt_sound',
    'PNP.DirectWire.TerminalProjectionFourCorners.mem_minimumImplementationsAt_complete',
    'PNP.DirectWire.TerminalProjectionFourCorners.mem_minimumImplementationsAt_iff',
    'PNP.DirectWire.TerminalProjectionFourCorners.mem_minimumImplementationBases_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasisBool_eq_true_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.mem_tightBasisFamily_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.mem_tightBasisFamily_complete',
    'PNP.DirectWire.TerminalFourCornerCarrier.mem_tightBasisFamily_iff',
    'PNP.DirectWire.TerminalFourCornerCarrier.canonicalImplementationBasis_at',
    'PNP.DirectWire.TerminalFourCornerCarrier.canonicalImplementationBasis_sizes',
    'PNP.DirectWire.TerminalFourCornerCarrier.canonicalImplementationBasis_isTightCoherent',
    'PNP.DirectWire.TerminalFourCornerCarrier.canonicalImplementationBasis_mem_tightFamily',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasis_incidenceValue_eq_delta',
    'PNP.DirectWire.TerminalFourCornerCarrier.mem_tightBasisValues_eq_delta',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasisMaximum?_eq_delta',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasisMaximum?_full',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasisMaximum?_quotient',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstBasisCoherenceFailure?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_eq_basis',
    'PNP.DirectWire.mem_allBoundedCandidates',
    'PNP.DirectWire.terminalFullProfileMatchBool_complete',
    'PNP.DirectWire.terminalQuotientProfileMatchBool_complete',
    'PNP.DirectWire.terminalFullProfileMinimum_le',
    'PNP.DirectWire.terminalQuotientProfileMinimum_le',
    'PNP.DirectWire.TerminalFourCornerSizes.numericallySideTight_iff_eq',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletionExists',
  ]);
  assert.match(terminalFourCornerTightBasisMaximum.scope,
    /complete finite tight-basis family/u);
  assert.match(terminalFourCornerTightBasisMaximum.scope,
    /signed maximum equals the selected delta/u);
  assert.match(terminalFourCornerTightBasisMaximum.nonClaim,
    /universal route silence/u);
  assert.match(terminalFourCornerTightBasisMaximum.nonClaim,
    /BN2 square legitimacy/u);
  const terminalComputedBN2SquareLegitimacy = byId.get(
    'residual-terminal-computed-bn2-square-legitimacy',
  );
  assert.equal(terminalComputedBN2SquareLegitimacy.status,
    'formalized-residual-terminal-computed-bn2-square-legitimacy');
  assert.equal(terminalComputedBN2SquareLegitimacy.earned, true);
  assert.equal(
    terminalComputedBN2SquareLegitimacy.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalComputedBN2SquareLegitimacy.requiredTheorems, [
    'PNP.DirectWire.TerminalComputedBN2SquareLegitimate.cornerCompatible',
    'PNP.DirectWire.TerminalComputedBN2SquareLegitimate.meetProfile',
    'PNP.DirectWire.TerminalComputedBN2SquareLegitimate.joinProfile',
    'PNP.DirectWire.TerminalComputedBN2SquareLegitimate.projectionCompatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.computedBN2SquareLegitimate',
    'PNP.DirectWire.TerminalComputedBN2SquareQuantities.sharedRole',
    'PNP.DirectWire.TerminalComputedBN2SquareQuantities.sharedProjection',
    'PNP.DirectWire.TerminalComputedBN2SquareQuantities.referenceMinimumPreserved',
    'PNP.DirectWire.TerminalComputedBN2SquareQuantities.transferIdentity',
    'PNP.DirectWire.TerminalFourCornerCarrier.computedBN2SquareQuantities',
    'PNP.DirectWire.TerminalFourCornerCarrier.computedBN2LocalConclusion',
    'PNP.DirectWire.TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute',
    'PNP.DirectWire.TerminalFourCornerCarrier.complete_transport',
    'PNP.DirectWire.TerminalSaturatedSupportSquare.governed_frontier_pushout',
    'PNP.DirectWire.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible',
    'PNP.DirectWire.TerminalFourCornerCarrier.sideTightCompletionExistsEachMode',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasisMaximum?_full',
    'PNP.DirectWire.TerminalFourCornerCarrier.tightBasisMaximum?_quotient',
    'PNP.DirectWire.TerminalFourCornerOptimumRoutedFailure.sound',
    'PNP.DirectWire.TerminalProjectionFourCorners.transferIdentity',
  ]);
  assert.match(terminalComputedBN2SquareLegitimacy.scope,
    /every finite computed terminal support square/u);
  assert.match(terminalComputedBN2SquareLegitimacy.scope,
    /full-then-quotient/u);
  assert.match(terminalComputedBN2SquareLegitimacy.nonClaim,
    /complete global no-outcome route system/u);
  assert.match(terminalComputedBN2SquareLegitimacy.nonClaim,
    /SaturatePositive/u);
  const terminalComputedBCELAnchorNucleus = byId.get(
    'residual-terminal-computed-bcel-anchor-nucleus',
  );
  assert.equal(terminalComputedBCELAnchorNucleus.status,
    'formalized-residual-terminal-computed-bcel-anchor-nucleus');
  assert.equal(terminalComputedBCELAnchorNucleus.earned, true);
  assert.equal(
    terminalComputedBCELAnchorNucleus.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalComputedBCELAnchorNucleus.requiredTheorems, [
    'PNP.DirectWire.TerminalBCELAnchorProblem.mem_anchorRecords_iff',
    'PNP.DirectWire.TerminalBCELAnchorProblem.anchorRecords_nodup',
    'PNP.DirectWire.TerminalBCELAnchorProblem.anchorRecords_mem_allAnchorSubfamilies',
    'PNP.DirectWire.findTerminalPositiveAnchorNucleus_sound',
    'PNP.DirectWire.findTerminalPositiveAnchorNucleus_eq_none_iff',
    'PNP.DirectWire.findTerminalPositiveAnchorNucleus_exists_of_whole_positive',
    'PNP.DirectWire.findTerminalPositiveAnchorNucleus_unique',
    'PNP.DirectWire.TerminalBCELAnchorAlgebraCheck.disagrees_eq_true_iff',
    'PNP.DirectWire.terminalBCELAnchorAlgebraCheck_mem',
    'PNP.DirectWire.mem_allTerminalBCELAnchorAlgebraChecks_governed',
    'PNP.DirectWire.firstTerminalBCELAnchorAlgebraMismatch?_sound',
    'PNP.DirectWire.firstTerminalBCELAnchorAlgebraMismatch?_eq_none_iff',
    'PNP.DirectWire.terminalBCELProperCutSeedBool_eq_true_iff',
    'PNP.DirectWire.mem_allTerminalBCELProperCutSeeds_iff',
    'PNP.DirectWire.TerminalBCELCutDefectCheck.disagrees_eq_true_iff',
    'PNP.DirectWire.terminalBCELCutDefectCheck_mem',
    'PNP.DirectWire.mem_allTerminalBCELCutDefectChecks_proper',
    'PNP.DirectWire.firstTerminalBCELCutDefectMismatch?_sound',
    'PNP.DirectWire.firstTerminalBCELCutDefectMismatch?_eq_none_all',
    'PNP.DirectWire.firstTerminalBCELCutRoute?_sound',
    'PNP.DirectWire.firstTerminalBCELCutRoute?_eq_none_noRoutes',
    'PNP.DirectWire.computedBCELCutConclusionOfNoFailures',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.strictSubfamily_defect_zero',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.anchorSizeAtLeastTwo',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.properCutConstantEquation',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.properCutLocalConclusion',
    'PNP.DirectWire.classifyTerminalBCELAnchorNucleus_exhaustive',
    'PNP.DirectWire.allTerminalPrimitiveRecords_nodup',
    'PNP.DirectWire.filter_mem_terminalListSubsets',
    'PNP.DirectWire.mem_allTerminalPrimitiveRecords',
    'PNP.DirectWire.TerminalFourCornerCarrier.firstOptimumRoute?_sound',
    'PNP.DirectWire.TerminalFourCornerOptimumRoutedFailure.sound',
    'PNP.DirectWire.TerminalFourCornerCarrier.computedBN2SquareLegitimate',
    'PNP.DirectWire.TerminalFourCornerCarrier.computedBN2LocalConclusion',
    'PNP.DirectWire.TerminalProjectionFourCorners.constantCutEquation_of_defects',
    'PNP.DirectWire.TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut',
  ]);
  assert.match(terminalComputedBCELAnchorNucleus.scope,
    /minimum-cardinality positive anchor nucleus/u);
  assert.match(terminalComputedBCELAnchorNucleus.scope,
    /full-before-quotient/u);
  assert.match(terminalComputedBCELAnchorNucleus.nonClaim,
    /positive whole-support projection defect/u);
  assert.match(terminalComputedBCELAnchorNucleus.nonClaim,
    /SaturatePositive/u);
  const terminalSaturationPositivityFirewall = byId.get(
    'residual-terminal-saturation-positivity-firewall',
  );
  assert.equal(terminalSaturationPositivityFirewall.status,
    'formalized-residual-terminal-saturation-positivity-firewall');
  assert.equal(terminalSaturationPositivityFirewall.earned, true);
  assert.equal(
    terminalSaturationPositivityFirewall.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.deepEqual(terminalSaturationPositivityFirewall.requiredTheorems, [
    'PNP.DirectWire.TerminalBCELAnchorProblem.wholeCorners_projectionDefect',
    'PNP.DirectWire.TerminalProjectionPositivityLoss.minima_eq',
    'PNP.DirectWire.classifyTerminalSaturationPositivity_loss_of_zero',
    'PNP.DirectWire.classifyTerminalSaturationPositivity_bcel_of_positive',
    'PNP.DirectWire.terminalSaturationPositivity_no_checkedFullLiftAtMinimum',
    'PNP.DirectWire.classifyTerminalSaturationPositivity_exhaustive',
    'PNP.DirectWire.terminalProjectionDefect_eq_zero_iff_minima_eq',
    'PNP.DirectWire.terminalFullProfileMinimumRealization_gateCount',
    'PNP.DirectWire.terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum',
    'PNP.DirectWire.TerminalProperPositiveSupport.saturatedRecords_closed',
    'PNP.DirectWire.TerminalProperPositiveSupport.physically_compatible',
    'PNP.DirectWire.TerminalProperPositiveSupport.extracted_semantics',
  ]);
  assert.match(terminalSaturationPositivityFirewall.scope,
    /zero projection defect/u);
  assert.match(terminalSaturationPositivityFirewall.scope,
    /positive defect/u);
  assert.match(terminalSaturationPositivityFirewall.nonClaim,
    /projectionPositivityNotLostSilently/u);
  assert.match(terminalSaturationPositivityFirewall.nonClaim,
    /transparentSaturationCostBalanced/u);
  const terminalSaturationCostBalance = byId.get(
    'residual-terminal-candidate-saturation-cost-balance',
  );
  assert.equal(terminalSaturationCostBalance.status,
    'formalized-residual-terminal-candidate-saturation-cost-balance');
  assert.equal(terminalSaturationCostBalance.earned, true);
  assert.equal(
    terminalSaturationCostBalance.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalSaturationCostBalance.requiredTheorems.length, 17);
  assert.match(terminalSaturationCostBalance.scope,
    /candidate-derived dependency system/u);
  assert.match(terminalSaturationCostBalance.scope,
    /first nontransparent event/u);
  assert.match(terminalSaturationCostBalance.nonClaim,
    /interfaceExposureRoutesToE/u);
  assert.match(terminalSaturationCostBalance.nonClaim,
    /originKernelObligationClosureRouted/u);
  const terminalInterfaceExposureRouting = byId.get(
    'residual-terminal-interface-exposure-routing',
  );
  assert.equal(terminalInterfaceExposureRouting.status,
    'formalized-residual-terminal-interface-exposure-routing');
  assert.equal(terminalInterfaceExposureRouting.earned, true);
  assert.equal(
    terminalInterfaceExposureRouting.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalInterfaceExposureRouting.requiredTheorems.length, 10);
  assert.match(terminalInterfaceExposureRouting.scope,
    /candidate-derived interface-consumer edge/u);
  assert.match(terminalInterfaceExposureRouting.scope,
    /first nontransparent event/u);
  assert.match(terminalInterfaceExposureRouting.nonClaim, /local E-route/u);
  assert.match(terminalInterfaceExposureRouting.nonClaim, /VerifyDW/u);
  assert.match(terminalInterfaceExposureRouting.nonClaim,
    /originKernelObligationClosureRouted/u);
  const terminalFiniteSaturatePositive = byId.get(
    'residual-terminal-finite-saturate-positive-composition',
  );
  assert.equal(terminalFiniteSaturatePositive.status,
    'formalized-residual-terminal-finite-saturate-positive-composition');
  assert.equal(terminalFiniteSaturatePositive.earned, true);
  assert.equal(
    terminalFiniteSaturatePositive.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalFiniteSaturatePositive.requiredTheorems.length, 9);
  assert.match(terminalFiniteSaturatePositive.scope,
    /origin, kernel, and obligation/u);
  assert.match(terminalFiniteSaturatePositive.scope,
    /positive full slack/u);
  assert.match(terminalFiniteSaturatePositive.nonClaim, /local route/u);
  assert.match(terminalFiniteSaturatePositive.nonClaim, /Package E/u);
  assert.match(terminalFiniteSaturatePositive.nonClaim, /RankWF/u);
  const terminalRankWF = byId.get('residual-terminal-rank-wf');
  assert.equal(terminalRankWF.status,
    'formalized-residual-terminal-rank-wf');
  assert.equal(terminalRankWF.earned, true);
  assert.equal(terminalRankWF.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(terminalRankWF.requiredTheorems.length, 18);
  assert.match(terminalRankWF.scope, /ten natural coordinates/u);
  assert.match(terminalRankWF.scope, /kernel-checked well-foundedness/u);
  assert.match(terminalRankWF.nonClaim, /does not map/u);
  assert.match(terminalRankWF.nonClaim, /strictly decreases/u);
  const terminalBN3RequestEnvelope = byId.get(
    'residual-terminal-bn3-request-envelope',
  );
  assert.equal(terminalBN3RequestEnvelope.status,
    'formalized-residual-terminal-bn3-request-envelope');
  assert.equal(terminalBN3RequestEnvelope.earned, true);
  assert.equal(
    terminalBN3RequestEnvelope.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalBN3RequestEnvelope.requiredTheorems.length, 11);
  assert.match(terminalBN3RequestEnvelope.scope, /canonical duplicate-free/u);
  assert.match(terminalBN3RequestEnvelope.scope, /every proper cut/u);
  assert.match(terminalBN3RequestEnvelope.nonClaim, /exponential/u);
  assert.match(terminalBN3RequestEnvelope.nonClaim, /BN4-BN6/u);
  const terminalBN4ActivationCancellation = byId.get(
    'residual-terminal-bn4-activation-cancellation',
  );
  assert.equal(terminalBN4ActivationCancellation.status,
    'formalized-residual-terminal-bn4-activation-cancellation');
  assert.equal(terminalBN4ActivationCancellation.earned, true);
  assert.equal(
    terminalBN4ActivationCancellation.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalBN4ActivationCancellation.requiredTheorems.length, 13);
  assert.match(terminalBN4ActivationCancellation.scope, /complete typed key/u);
  assert.match(terminalBN4ActivationCancellation.scope, /integer mass/u);
  assert.match(terminalBN4ActivationCancellation.nonClaim,
    /explicit typed cell ledger/u);
  assert.match(terminalBN4ActivationCancellation.nonClaim,
    /not the full historical BN4/u);
  const terminalBN5FullShadowLocalization = byId.get(
    'residual-terminal-bn5-full-shadow-localization',
  );
  assert.equal(terminalBN5FullShadowLocalization.status,
    'formalized-residual-terminal-bn5-full-shadow-localization');
  assert.equal(terminalBN5FullShadowLocalization.earned, true);
  assert.equal(
    terminalBN5FullShadowLocalization.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalBN5FullShadowLocalization.requiredTheorems.length, 12);
  assert.match(terminalBN5FullShadowLocalization.scope, /exact-coordinate/u);
  assert.match(terminalBN5FullShadowLocalization.scope, /Hall deficit/u);
  assert.match(terminalBN5FullShadowLocalization.nonClaim,
    /explicit finite inputs/u);
  assert.match(terminalBN5FullShadowLocalization.nonClaim,
    /not the full historical BN5/u);
  const terminalPkgCTypedRestoration = byId.get(
    'residual-terminal-pkgc-typed-restoration',
  );
  assert.equal(terminalPkgCTypedRestoration.status,
    'formalized-residual-terminal-pkgc-typed-restoration');
  assert.equal(terminalPkgCTypedRestoration.earned, true);
  assert.equal(
    terminalPkgCTypedRestoration.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalPkgCTypedRestoration.requiredTheorems.length, 9);
  assert.match(terminalPkgCTypedRestoration.scope,
    /typed full-restoration candidates/u);
  assert.match(terminalPkgCTypedRestoration.scope,
    /multiplicity coverage/u);
  assert.match(terminalPkgCTypedRestoration.nonClaim,
    /restoration operation remains explicit/u);
  assert.match(terminalPkgCTypedRestoration.nonClaim,
    /does not construct it from a terminal candidate/u);
  const terminalPkgCSameKeyCancellation = byId.get(
    'residual-terminal-pkgc-same-key-cancellation',
  );
  assert.equal(terminalPkgCSameKeyCancellation.status,
    'formalized-residual-terminal-pkgc-same-key-cancellation');
  assert.equal(terminalPkgCSameKeyCancellation.earned, true);
  assert.equal(
    terminalPkgCSameKeyCancellation.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalPkgCSameKeyCancellation.requiredTheorems.length, 11);
  assert.match(terminalPkgCSameKeyCancellation.scope,
    /opposite-sign unit cells/u);
  assert.match(terminalPkgCSameKeyCancellation.scope,
    /empty canonical residual and zero signed mass/u);
  assert.match(terminalPkgCSameKeyCancellation.nonClaim,
    /complete coordinate maps remain explicit/u);
  assert.match(terminalPkgCSameKeyCancellation.nonClaim,
    /ambient BN4 ledger/u);
  const terminalPkgCAmbientBN4Ledger = byId.get(
    'residual-terminal-pkgc-ambient-bn4-ledger',
  );
  assert.equal(terminalPkgCAmbientBN4Ledger.status,
    'formalized-residual-terminal-pkgc-ambient-bn4-ledger');
  assert.equal(terminalPkgCAmbientBN4Ledger.earned, true);
  assert.equal(
    terminalPkgCAmbientBN4Ledger.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalPkgCAmbientBN4Ledger.requiredTheorems.length, 12);
  assert.match(terminalPkgCAmbientBN4Ledger.scope, /exact multiset/u);
  assert.match(terminalPkgCAmbientBN4Ledger.scope, /explicit remainder/u);
  assert.match(terminalPkgCAmbientBN4Ledger.nonClaim,
    /explicit proof-bearing inputs/u);
  assert.match(terminalPkgCAmbientBN4Ledger.nonClaim,
    /does not derive the ambient ledger/u);
  const terminalPkgCAmbientBN4ResidualReduction = byId.get(
    'residual-terminal-pkgc-ambient-bn4-residual-reduction',
  );
  assert.equal(terminalPkgCAmbientBN4ResidualReduction.status,
    'formalized-residual-terminal-pkgc-ambient-bn4-residual-reduction');
  assert.equal(terminalPkgCAmbientBN4ResidualReduction.earned, true);
  assert.equal(
    terminalPkgCAmbientBN4ResidualReduction
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalPkgCAmbientBN4ResidualReduction.requiredTheorems.length,
    8);
  assert.match(terminalPkgCAmbientBN4ResidualReduction.scope,
    /complete canonical executable residual ledger/u);
  assert.match(terminalPkgCAmbientBN4ResidualReduction.nonClaim,
    /does not derive those inputs/u);
  const terminalHBActiveDependencyClosure = byId.get(
    'residual-terminal-hb-active-dependency-closure',
  );
  assert.equal(terminalHBActiveDependencyClosure.status,
    'formalized-residual-terminal-hb-active-dependency-closure');
  assert.equal(terminalHBActiveDependencyClosure.earned, true);
  assert.equal(
    terminalHBActiveDependencyClosure.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalHBActiveDependencyClosure.requiredTheorems.length, 7);
  assert.match(terminalHBActiveDependencyClosure.scope,
    /every supplied HN and budget activity bit is false/u);
  assert.match(terminalHBActiveDependencyClosure.scope,
    /faithful strictly lower-rank seed/u);
  assert.match(terminalHBActiveDependencyClosure.nonClaim,
    /semantic dependency completeness/u);
  assert.match(terminalHBActiveDependencyClosure.nonClaim,
    /does not establish.*gain exclusion.*lower-seed closure/u);
  const terminalHBSelectorSilenceClosure = byId.get(
    'residual-terminal-hb-selector-silence-closure',
  );
  assert.equal(terminalHBSelectorSilenceClosure.status,
    'formalized-residual-terminal-hb-selector-silence-closure');
  assert.equal(terminalHBSelectorSilenceClosure.earned, true);
  assert.equal(
    terminalHBSelectorSilenceClosure.axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(terminalHBSelectorSilenceClosure.requiredTheorems.length, 4);
  assert.match(terminalHBSelectorSilenceClosure.scope,
    /every canonical selector.*nonfaithful/u);
  assert.match(terminalHBSelectorSilenceClosure.scope,
    /semantic exclusion of every strict equivalent gain/u);
  assert.match(terminalHBSelectorSilenceClosure.nonClaim,
    /explicit proof-bearing premise/u);
  assert.match(terminalHBSelectorSilenceClosure.nonClaim,
    /does not establish selector faithfulness or compatibility/u);
  const terminalHBExecutableSelectorSilenceInduction = byId.get(
    'residual-terminal-hb-executable-selector-silence-induction',
  );
  assert.equal(terminalHBExecutableSelectorSilenceInduction.status,
    'formalized-residual-terminal-hb-executable-selector-silence-induction');
  assert.equal(terminalHBExecutableSelectorSilenceInduction.earned, true);
  assert.equal(
    terminalHBExecutableSelectorSilenceInduction
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalHBExecutableSelectorSilenceInduction.requiredTheorems.length,
    7,
  );
  assert.match(terminalHBExecutableSelectorSilenceInduction.scope,
    /every canonical realizer claim is a typed bottom/u);
  assert.match(terminalHBExecutableSelectorSilenceInduction.scope,
    /without global semantic no-gain/u);
  assert.match(terminalHBExecutableSelectorSilenceInduction.nonClaim,
    /remain explicit data inputs/u);
  assert.match(terminalHBExecutableSelectorSilenceInduction.nonClaim,
    /does not construct them from terminal candidates/u);
  const terminalPacketSelectorFaithfulnessRouting = byId.get(
    'residual-terminal-packet-selector-faithfulness-routing',
  );
  assert.equal(terminalPacketSelectorFaithfulnessRouting.status,
    'formalized-residual-terminal-packet-selector-faithfulness-routing');
  assert.equal(terminalPacketSelectorFaithfulnessRouting.earned, true);
  assert.equal(
    terminalPacketSelectorFaithfulnessRouting
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketSelectorFaithfulnessRouting.requiredTheorems.length,
    11,
  );
  assert.match(terminalPacketSelectorFaithfulnessRouting.scope,
    /positive Packet.*faithful canonical handle/u);
  assert.match(terminalPacketSelectorFaithfulnessRouting.scope,
    /contradiction with selector silence/u);
  assert.match(terminalPacketSelectorFaithfulnessRouting.nonClaim,
    /route-clear payload checks.*explicit/u);
  assert.match(terminalPacketSelectorFaithfulnessRouting.nonClaim,
    /does not derive positive slack/u);
  const terminalPacketSelectorFaithfulnessTable = byId.get(
    'residual-terminal-packet-selector-faithfulness-table',
  );
  assert.equal(terminalPacketSelectorFaithfulnessTable.status,
    'formalized-residual-terminal-packet-selector-faithfulness-table');
  assert.equal(terminalPacketSelectorFaithfulnessTable.earned, true);
  assert.equal(
    terminalPacketSelectorFaithfulnessTable
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketSelectorFaithfulnessTable.requiredTheorems.length,
    8,
  );
  assert.match(terminalPacketSelectorFaithfulnessTable.scope,
    /canonicalizes a typed-realizer table/u);
  assert.match(terminalPacketSelectorFaithfulnessTable.scope,
    /without an independent binding premise/u);
  assert.match(terminalPacketSelectorFaithfulnessTable.nonClaim,
    /payload field Booleans.*explicit inputs/u);
  assert.match(terminalPacketSelectorFaithfulnessTable.nonClaim,
    /does not derive those inputs from a terminal candidate/u);
  const terminalPacketSelectorFirstRouteOutcome = byId.get(
    'residual-terminal-packet-selector-first-route-outcome',
  );
  assert.equal(terminalPacketSelectorFirstRouteOutcome.status,
    'formalized-residual-terminal-packet-selector-first-route-outcome');
  assert.equal(terminalPacketSelectorFirstRouteOutcome.earned, true);
  assert.equal(
    terminalPacketSelectorFirstRouteOutcome
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketSelectorFirstRouteOutcome.requiredTheorems.length,
    7,
  );
  assert.match(terminalPacketSelectorFirstRouteOutcome.scope,
    /positive Packet.*first typed route/u);
  assert.match(terminalPacketSelectorFirstRouteOutcome.scope,
    /without route-clear or binding premises/u);
  assert.match(terminalPacketSelectorFirstRouteOutcome.nonClaim,
    /does not prove.*external semantics/u);
  assert.match(terminalPacketSelectorFirstRouteOutcome.nonClaim,
    /does not.*decreasing complete global outcome system/u);
  const terminalPacketSelectorFirstRouteSemantics = byId.get(
    'residual-terminal-packet-selector-first-route-semantics',
  );
  assert.equal(terminalPacketSelectorFirstRouteSemantics.status,
    'formalized-residual-terminal-packet-selector-first-route-semantics');
  assert.equal(terminalPacketSelectorFirstRouteSemantics.earned, true);
  assert.equal(
    terminalPacketSelectorFirstRouteSemantics
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketSelectorFirstRouteSemantics.requiredTheorems.length,
    6,
  );
  assert.match(terminalPacketSelectorFirstRouteSemantics.scope,
    /all ten route constructors.*exact earliest failed/u);
  assert.match(terminalPacketSelectorFirstRouteSemantics.scope,
    /positive Packet.*exact field-failure/u);
  assert.match(terminalPacketSelectorFirstRouteSemantics.nonClaim,
    /does not derive.*terminal data/u);
  assert.match(terminalPacketSelectorFirstRouteSemantics.nonClaim,
    /does not prove.*external manuscript semantics/u);
  const terminalPacketDescentRouteReflection = byId.get(
    'residual-terminal-packet-descent-route-reflection',
  );
  assert.equal(terminalPacketDescentRouteReflection.status,
    'formalized-residual-terminal-packet-descent-route-reflection');
  assert.equal(terminalPacketDescentRouteReflection.earned, true);
  assert.equal(
    terminalPacketDescentRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketDescentRouteReflection.requiredTheorems.length,
    9,
  );
  assert.match(terminalPacketDescentRouteReflection.scope,
    /strict-descent.*ten-coordinate.*RankWF/u);
  assert.match(terminalPacketDescentRouteReflection.scope,
    /earlier.*route.*nondecreasing/u);
  assert.match(terminalPacketDescentRouteReflection.nonClaim,
    /first nine.*explicit/u);
  assert.match(terminalPacketDescentRouteReflection.nonClaim,
    /does not construct.*ranks/u);
  const terminalPacketRankRouteReflection = byId.get(
    'residual-terminal-packet-rank-route-reflection',
  );
  assert.equal(terminalPacketRankRouteReflection.status,
    'formalized-residual-terminal-packet-rank-route-reflection');
  assert.equal(terminalPacketRankRouteReflection.earned, true);
  assert.equal(
    terminalPacketRankRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketRankRouteReflection.requiredTheorems.length,
    12,
  );
  assert.match(terminalPacketRankRouteReflection.scope,
    /rank tag.*authoritative.*handle rank/u);
  assert.match(terminalPacketRankRouteReflection.scope,
    /cannot return.*rank.*nondecreasing/u);
  assert.match(terminalPacketRankRouteReflection.nonClaim,
    /eight remaining routes/u);
  assert.match(terminalPacketRankRouteReflection.nonClaim,
    /does not construct.*rank map/u);
  const terminalPacketExactRouteReflection = byId.get(
    'residual-terminal-packet-exact-route-reflection',
  );
  assert.equal(terminalPacketExactRouteReflection.status,
    'formalized-residual-terminal-packet-exact-route-reflection');
  assert.equal(terminalPacketExactRouteReflection.earned, true);
  assert.equal(
    terminalPacketExactRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketExactRouteReflection.requiredTheorems.length,
    16,
  );
  assert.match(terminalPacketExactRouteReflection.scope,
    /canonical.*handle.*cell.*payload/u);
  assert.match(terminalPacketExactRouteReflection.scope,
    /cannot return.*exactRoute.*rank/u);
  assert.match(terminalPacketExactRouteReflection.nonClaim,
    /seven remaining routes/u);
  assert.match(terminalPacketExactRouteReflection.nonClaim,
    /internal route.*not.*exact minimum/u);
  const terminalPacketChargeRouteReflection = byId.get(
    'residual-terminal-packet-charge-route-reflection',
  );
  assert.equal(terminalPacketChargeRouteReflection.status,
    'formalized-residual-terminal-packet-charge-route-reflection');
  assert.equal(terminalPacketChargeRouteReflection.earned, true);
  assert.equal(
    terminalPacketChargeRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketChargeRouteReflection.requiredTheorems.length,
    19,
  );
  assert.match(terminalPacketChargeRouteReflection.scope,
    /positive.*source.*charge/u);
  assert.match(terminalPacketChargeRouteReflection.scope,
    /cannot return.*charge.*rank.*exactRoute/u);
  assert.match(terminalPacketChargeRouteReflection.nonClaim,
    /six remaining routes/u);
  assert.match(terminalPacketChargeRouteReflection.nonClaim,
    /positive source mass.*not.*charge-surplus/u);
  const terminalPacketColourRouteReflection = byId.get(
    'residual-terminal-packet-colour-route-reflection',
  );
  assert.equal(terminalPacketColourRouteReflection.status,
    'formalized-residual-terminal-packet-colour-route-reflection');
  assert.equal(terminalPacketColourRouteReflection.earned, true);
  assert.equal(
    terminalPacketColourRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketColourRouteReflection.requiredTheorems.length,
    22,
  );
  assert.match(terminalPacketColourRouteReflection.scope,
    /canonical handle.*grouped footprint.*family carrier/u);
  assert.match(terminalPacketColourRouteReflection.scope,
    /cannot return colour, charge, rank, or exactRoute/u);
  assert.match(terminalPacketColourRouteReflection.nonClaim,
    /five remaining.*fields/u);
  assert.match(terminalPacketColourRouteReflection.nonClaim,
    /not the full external manuscript colour equivalence/u);
  const terminalPacketFrontierRouteReflection = byId.get(
    'residual-terminal-packet-frontier-route-reflection',
  );
  assert.equal(terminalPacketFrontierRouteReflection.status,
    'formalized-residual-terminal-packet-frontier-route-reflection');
  assert.equal(terminalPacketFrontierRouteReflection.earned, true);
  assert.equal(
    terminalPacketFrontierRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketFrontierRouteReflection.requiredTheorems.length,
    23,
  );
  assert.match(terminalPacketFrontierRouteReflection.scope,
    /typed frontier-signature domain.*decidable equality/u);
  assert.match(terminalPacketFrontierRouteReflection.scope,
    /frontier first route is exactly typed signature inequality/u);
  assert.match(terminalPacketFrontierRouteReflection.nonClaim,
    /four remaining routes/u);
  assert.match(terminalPacketFrontierRouteReflection.nonClaim,
    /does not construct the supplied signatures from terminal data/u);
  const terminalPacketBN5ObligationRouteReflection = byId.get(
    'residual-terminal-packet-bn5-obligation-route-reflection',
  );
  assert.equal(terminalPacketBN5ObligationRouteReflection.status,
    'formalized-residual-terminal-packet-bn5-obligation-route-reflection');
  assert.equal(terminalPacketBN5ObligationRouteReflection.earned, true);
  assert.equal(
    terminalPacketBN5ObligationRouteReflection
      .axiomClosureUsesOnlyLeanStandardAllowlist,
    true,
  );
  assert.equal(
    terminalPacketBN5ObligationRouteReflection.requiredTheorems.length,
    26,
  );
  assert.match(terminalPacketBN5ObligationRouteReflection.scope,
    /typed terminal BN5 coordinate.*frontier and obligation/u);
  assert.match(terminalPacketBN5ObligationRouteReflection.scope,
    /obligation first route.*frontier equality.*obligation inequality/u);
  assert.match(terminalPacketBN5ObligationRouteReflection.nonClaim,
    /three remaining routes/u);
  assert.match(terminalPacketBN5ObligationRouteReflection.nonClaim,
    /does not construct those coordinates from terminal data/u);
  const lockedNANDThreshold = byId.get('global-locked-nand-threshold');
  assert.equal(lockedNANDThreshold.status,
    'formalized-concrete-locked-nand-threshold');
  assert.equal(lockedNANDThreshold.earned, true);
  assert.equal(lockedNANDThreshold.allAssumptionFree, false);
  assert.equal(lockedNANDThreshold.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.deepEqual(lockedNANDThreshold.requiredTheorems,
    ['PNP.Main.locked_nand_threshold']);
  assert.match(lockedNANDThreshold.nonClaim, /does not put the concrete locked threshold language in P/u);
  for (const id of [
    'global-zeroslack-pccmin',
    'concrete-publication-root',
  ]) assert.equal(byId.get(id).status, 'not-formalized');
});

test('publication consumes the reviewed locked-NAND carrier map and inventory counts', async () => {
  const [status, mapText, inventoryText] = await Promise.all([
    status0(),
    readFile(new URL('../publication/FORMAL_PUBLICATION_MAP.json', import.meta.url), 'utf8'),
    readFile(new URL('../status/LEAN_THEOREM_INVENTORY.json', import.meta.url), 'utf8'),
  ]);
  const map = JSON.parse(mapText);
  const inventory = JSON.parse(inventoryText);
  assert.equal(sha256Text0(mapText), status.formalPublicationMapSha256);
  assert.equal(map.milestoneSourceClosureSha256,
    status.leanSourceClosureSha256);
  assert.equal(Object.keys(map.earnedMilestoneTheoremKernelTypeSha256).length,
    inventory.milestoneCandidates.length);
  for (const theorem of [
    'PNP.DirectWire.TerminalBCELAnchorProblem.wholeCorners_projectionDefect',
    'PNP.DirectWire.TerminalProjectionPositivityLoss.minima_eq',
    'PNP.DirectWire.classifyTerminalSaturationPositivity_loss_of_zero',
    'PNP.DirectWire.classifyTerminalSaturationPositivity_bcel_of_positive',
    'PNP.DirectWire.terminalSaturationPositivity_no_checkedFullLiftAtMinimum',
    'PNP.DirectWire.classifyTerminalSaturationPositivity_exhaustive',
    'PNP.DirectWire.terminalSaturateTrace_eventsLinked',
    'PNP.DirectWire.TerminalTransparentSaturationStep.fullSlack_preserved',
    'PNP.DirectWire.TerminalSaturationEventsLinked.projectionDefect_mono',
    'PNP.DirectWire.TerminalSaturationBalanceOutcome.balanced_fullPositive_preserved',
    'PNP.DirectWire.terminalCandidateInterfaceExposureCoordinate?_edge',
    'PNP.DirectWire.terminalInterfaceExposure_transparent_or_eRoute',
    'PNP.DirectWire.TerminalFirstInterfaceExposureRoute.sound',
    'PNP.DirectWire.classifyTerminalSaturationInterfaceRouting_exhaustive',
    'PNP.DirectWire.terminalOriginKernelObligationCoordinate?_sound',
    'PNP.DirectWire.terminalCandidateOriginKernelObligationCoordinate?_shape',
    'PNP.DirectWire.terminalCandidateOriginKernelObligationCoordinate?_edge',
    'PNP.DirectWire.TerminalOriginKernelObligationClosureRoute.sound',
    'PNP.DirectWire.terminalOriginKernelObligation_safe_or_route',
    'PNP.DirectWire.TerminalSaturationClosureSafeStep.transparent',
    'PNP.DirectWire.classifyTerminalSaturationClosureRouting_exhaustive',
    'PNP.DirectWire.TerminalFiniteSaturatePositiveOutcome.sound',
    'PNP.DirectWire.classifyTerminalFiniteSaturatePositive_exhaustive',
    'PNP.DirectWire.TerminalResidualRank.coordinates_mk',
    'PNP.DirectWire.TerminalResidualRank.coordinates_length',
    'PNP.DirectWire.terminalResidualRankLTBool_eq_true_iff',
    'PNP.DirectWire.terminalResidualRankLTBool_eq_false_iff',
    'PNP.DirectWire.terminalResidualRankLexLT_wellFounded',
    'PNP.DirectWire.terminalResidualRank_accessible',
    'PNP.DirectWire.terminalResidualRank_induction',
    'PNP.DirectWire.terminalResidualRank_witnessType_lt',
    'PNP.DirectWire.terminalResidualRank_spanType_lt',
    'PNP.DirectWire.terminalResidualRank_mode_lt',
    'PNP.DirectWire.terminalResidualRank_frontierDefect_lt',
    'PNP.DirectWire.terminalResidualRank_projectionDefect_lt',
    'PNP.DirectWire.terminalResidualRank_saturationDefect_lt',
    'PNP.DirectWire.terminalResidualRank_anchorCount_lt',
    'PNP.DirectWire.terminalResidualRank_chargeSize_lt',
    'PNP.DirectWire.terminalResidualRank_profileSize_lt',
    'PNP.DirectWire.terminalResidualRank_canonicalCode_lt',
    'PNP.DirectWire.TerminalResidualRankDescent.sound',
    'PNP.DirectWire.terminalListSubsets_sublist',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.requestAtoms_nodup',
    'PNP.DirectWire.terminalBN3RequestPredicateBool_eq_true_iff',
    'PNP.DirectWire.terminalBN3RequestPredicate_monotone',
    'PNP.DirectWire.terminalBN3RequestPredicate_stable',
    'PNP.DirectWire.terminalBN3MinimalConsumer_exact',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.mem_activeRequestAtoms_iff_properCut',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.activeRequestAtoms_nodup',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.canonicalRequestBasis_jointlySideTight',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.computedBN3RequestEnvelope',
    'PNP.DirectWire.classifyTerminalBN3RequestEnvelope_exhaustive',
    'PNP.DirectWire.terminalBN4ActivationCode_active_iff',
    'PNP.DirectWire.terminalBN4ActivationCode_eq_iff_activation',
    'PNP.DirectWire.terminalBN4ActivationKey_eq_iff',
    'PNP.DirectWire.terminalBN4IntegerMassLedger_exact',
    'PNP.DirectWire.TerminalBN4KeyCancellation.residual_key_eq',
    'PNP.DirectWire.TerminalBN4KeyCancellation.residual_mass_positive',
    'PNP.DirectWire.TerminalBN4KeyCancellation.no_opposite_sign_residual',
    'PNP.DirectWire.TerminalBN4KeyCancellation.residual_signedContribution_exact',
    'PNP.DirectWire.terminalBN4CancelAtKey_signedContribution_exact',
    'PNP.DirectWire.terminalBN4CanonicalKeys_nodup',
    'PNP.DirectWire.terminalBN4CellsUseCanonicalAtoms_iff',
    'PNP.DirectWire.TerminalComputedBCELAnchorNucleus.computedBN4ActivationCancellation',
    'PNP.DirectWire.classifyTerminalBN4ActivationCancellation_exhaustive',
    'PNP.DirectWire.terminalBN5ShadowCoordinate_eq_iff',
    'PNP.DirectWire.terminalBN5FullUnits_length',
    'PNP.DirectWire.terminalBN5FullUnits_key_eq',
    'PNP.DirectWire.TerminalBN5HallDeficit.neighbor_card_lt_full_card',
    'PNP.DirectWire.TerminalBN5HallDeficit.fullSubset_coordinate_eq',
    'PNP.DirectWire.TerminalBN5HallDeficit.neighbor_coordinate_eq',
    'PNP.DirectWire.classifyTerminalBN5ShadowMatching_exhaustive',
    'PNP.DirectWire.TerminalBN4KeyCancellation.negativeResidualMass?_positive',
    'PNP.DirectWire.TerminalBN5HallDeficit.namedLocalRoute_eq_x1Hall',
    'PNP.DirectWire.classifyTerminalBN5FullShadowLocalization_active',
    'PNP.DirectWire.TerminalBN5HallDeficit.unmatchedShadowNotSilent',
    'PNP.DirectWire.classifyTerminalBN5FullShadowLocalization_exhaustive',
    'PNP.DirectWire.TerminalPkgCSeparatingPair.fullRestorationCandidates_length',
    'PNP.DirectWire.TerminalPkgCSeparatingPair.fullRestorationCandidates_coordinates',
    'PNP.DirectWire.TerminalPkgCTypedRestorer.coordinateUniverse_coordinates',
    'PNP.DirectWire.terminalBN5FullMultiplicity_indexed_eq',
    'PNP.DirectWire.terminalBN5ShadowMultiplicity_indexed_eq',
    'PNP.DirectWire.TerminalPkgCSeparatingPair.typedRestoration_exactCoverage',
    'PNP.DirectWire.terminalBN5CompleteMultiplicityMatching_not_hallDeficit',
    'PNP.DirectWire.terminalPkgC_typedRestoration_realization',
    'PNP.DirectWire.classifyTerminalPkgCTypedRestoration_exhaustive',
  ]) assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[theorem],
    'string', theorem);
  for (const theorem of [
    'PNP.DirectWire.LockedNANDTrace.carrierSeparation',
    'PNP.DirectWire.LockedNANDTrace.finalLock_fresh',
    'PNP.DirectWire.LockedNANDTrace.distinguishedChecks_length',
    'PNP.DirectWire.LockedNANDTrace.tracePredicate_coherentExtension',
    'PNP.DirectWire.LockedNANDTrace.trace_sound_of_predicate_true',
    'PNP.DirectWire.LockedNANDTrace.traceEquivalence',
    'PNP.DirectWire.LockedNANDTrace.satisfiable_iff_trace_extension',
    'PNP.DirectWire.LockedNANDTrace.exists_coherent_trace',
  ]) assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[theorem],
    'string', theorem);
  assert.equal(
    map.earnedMilestoneTheoremKernelTypeSha256[
      'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_eq_false_of_unsatisfiable'
    ],
    '3841bbc176784b6dfd3c889e576fe74d117ca420f5f79f31063d85797f0bd3de',
  );
  assert.equal(
    map.earnedMilestoneTheoremKernelTypeSha256[
      'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable'
    ],
    'da9bb9d292f6cb2952d58120a4579503d87bd1ac94cd5d9248f40ba5007edf94',
  );
  for (const theorem of [
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_nonconstant_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_notPositiveProjection_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_distinctFromBaseline_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_satisfiableFinalConditions',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_referenceMinimum_bounds_of_satisfiable',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_residualSlack_le_four',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_satisfiable_iff_referenceMinimum_ge_succ',
  ]) assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[theorem],
    'string', theorem);
  for (const theorem of [
    'PNP.DirectWire.LockedNANDGlobalCandidates.macroGateCount_report_formula',
    'PNP.DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount_eq_lockedBaselineCount',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_size',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselinePrefixSource_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_size',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_initial_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_semantics',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_no_internal_constants',
    'PNP.DirectWire.LockedNANDGlobalCandidates.fullCandidate_no_internal_constants',
    'PNP.DirectWire.LockedNANDGlobalCandidates.baselineCandidate_finalLock_irrelevant',
  ]) assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[theorem],
    'string', theorem);
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.secondFollowingTokenSlot_direct_eq_padding_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.thirdFollowingTokenSlot_direct_eq_padding_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.fourthFollowingTokenSlot_direct_eq_padding_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.sixthFollowingTokenSlot_direct_eq_padding_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.seventhFollowingTokenSlot_direct_eq_padding_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.eighthFollowingTokenSlot_direct_eq_padding_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.fifthFollowingTokenSlot_direct_eq_padding_or_f'
  ], 'string');
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
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClausePaddingRun.fifthClauseSlotStart_direct_eq_padding'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.sixthClauseSlotStart_direct_eq_padding'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFirstConstraintPaddingRun.secondConstraintStart_direct_eq_sep'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintSeparatorStep.nextTokenSlot_direct_eq_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSignStep.nextTokenSlot_direct_eq_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.nextTokenSlot_direct_eq_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.nextTokenSlot_direct_eq_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.nextTokenSlot_direct_eq_f'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.nextTokenSlot_direct_eq_finish_or_t'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.followingTokenSlot_direct_eq_padding_or_t'
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
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.nextTokenSlot_direct_eq_padding'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderThirdClausePaddingRun.fourthClauseStart_direct_eq_sep'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClauseSeparatorStep.nextTokenSlot_direct_eq_f'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.nextTokenSlot_direct_eq_f'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.nextTokenSlot_direct_eq_finish'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.workRunExact'
  ], 'string');
  assert.equal(typeof map.earnedMilestoneTheoremKernelTypeSha256[
    'PNP.Concrete.CookLevin.BuilderFourthClausePrefix.nextTokenSlot_direct_eq_padding'
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
  ], [
    inventory.declarationCount,
    inventory.theoremCount,
    inventory.assumptionFreeTheoremCount,
    inventory.excludedPrivateDeclarationCount,
    inventory.sourceClosureModuleCount,
  ]);
});

test('canonical report source is current and the committed PDF artifact exists', async () => {
  const [tex, status] = await Promise.all([
    readFile(new URL('../canonical_proof_report.tex', import.meta.url), 'utf8'),
    status0(),
  ]);
  assert.match(tex, /The repository does not currently establish \$P=NP\$\./u);
  assert.match(
    tex,
    /Locked-NAND satisfiable separation and typed semantic threshold/u,
  );
  assert.match(
    tex,
    /one answer-independent full candidate instantiates all six semantic premises/u,
  );
  assert.match(
    tex,
    /A strict version-zero grammar\s+serializes source circuits, the complete full candidate/u,
  );
  assert.match(
    tex,
    /That module is a pure semantic transformation and does not\s+by itself supply an executable parser or emitter/u,
  );
  assert.match(
    tex,
    /The following strict-v0 source-parser milestone supplies a direct\s+nine-symbol machine with 228 control states and 2,052 pairwise/u,
  );
  assert.match(
    tex,
    /accepts exactly the valid source encodings, preserves valid source bytes\s+verbatim, and returns the empty word for invalid grammar or references/u,
  );
  assert.match(
    tex,
    /target-emitter milestone supplies a literal finite controller\s+with an exact all-input polynomial work bound/u,
  );
  assert.match(
    tex,
    /binds that exact composed function and the already-proved\s+encoded language equivalence as a concrete \\code\{PolynomialReduction\}/u,
  );
  assert.match(
    tex,
    /Its 16-declaration audit has two empty closures, two\s+using only \\code\{propext\}, and twelve using only \\code\{propext\} and\s+\\code\{Quot\.sound\}/u,
  );
  assert.match(
    tex,
    /fixed parser\/carrier\/controller work graph now implements exactly that pure\s+compiler on every bitstring within one external-input polynomial/u,
  );
  assert.match(
    tex,
    /separate fixed all-input machine now translates\s+strict canonical CNF into well-formed topological NAND, preserves satisfiability exactly, supplies\s+a polynomial-time function and raw refinement/u,
  );
  assert.match(
    tex,
    /compiled\s+machine never times out at the advertised bound, retains literal\s+\\code\{RawRefinement\}/u,
  );
  assert.match(
    tex,
    /The global strict-gain stopping milestone reconstructs the corresponding\s+semantic endpoint condition from legacy report Section 16/u,
  );
  assert.match(
    tex,
    /finite-list failure still cannot establish global absence/u,
  );
  assert.match(
    tex,
    /The terminal full-carrier milestone reconstructs the direct-wire full-mode[\s\S]*legacy report Section 8/u,
  );
  assert.match(
    tex,
    /All 22 public declarations have empty axiom closure/u,
  );
  assert.match(tex, /Four-corner optimum coherence dichotomy/u);
  assert.match(tex, /exact deterministic first failure/u);
  assert.match(tex, /does not prove that every square is coherent/u);
  assert.match(
    tex,
    /\\code\{PolynomialReduction CNFSAT EncodedNANDSAT\}/u,
  );
  assert.match(
    tex,
    /explicitly composes with\s+the strict locked-NAND reduction/u,
  );
  assert.match(
    tex,
    /report-facing theorem\s+\\code\{PNP\.Main\.locked\\_nand\\_threshold\} now publishes that composition as a\s+uniform all-bitstring reduction/u,
  );
  assert.match(
    tex,
    /This reduction still does not decide CNF-SAT, put the\s+locked target in P, discharge residual-band\/ZeroSlack\/PCCMin, or prove \$P=NP\$/u,
  );
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
  assert.match(tex, /Cook-Levin complete third-clause prefix/u);
  assert.match(tex, /global table has exactly 3126/u);
  assert.match(tex, /canonical prefix through the complete third clause/u);
  assert.match(tex, /retains its first in-range padding coordinate/u);
  assert.match(tex, /does not traverse clause-three padding/u);
  assert.match(tex, /third-clause-padding composition evaluates/u);
  assert.match(tex, /retained coordinate is the fourth clause's opening/u);
  assert.match(tex, /does not emit the fourth-clause separator/u);
  assert.match(tex, /fourth-clause-separator composition reuses the selected 59-rule/u);
  assert.match(tex, /global table with exactly 3300/u);
  assert.match(tex, /emits exactly the separator beginning clause four/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 28\)\)/u);
  assert.match(tex, /does not emit the\s+following \\code\{F\}, complete clause four/u);
  assert.match(tex, /fourth-clause-first-literal composition reuses the fixed 357-rule/u);
  assert.match(tex, /global table has exactly\s+3666/u);
  assert.match(tex, /complete first negative literal on variable one/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 31\)\)/u);
  assert.match(tex, /does not emit the second literal, complete clause four/u);
  assert.match(tex, /fourth-clause-second-literal composition reuses the fixed 479-rule/u);
  assert.match(tex, /global table has exactly\s+4154/u);
  assert.match(tex, /complete second negative literal on variable two/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 35\)\)/u);
  assert.match(tex, /does not emit the\s+following \\code\{Finish\}, complete clause four/u);
  assert.match(tex, /complete-fourth-clause composition reuses a selected 59-rule/u);
  assert.match(tex, /global table has exactly 4276/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 36\)\)/u);
  assert.match(tex, /completes clause four\s+but does not traverse its padding/u);
  assert.match(tex, /Cook-Levin fourth-clause remaining-padding run/u);
  assert.match(tex, /traverses exactly FormulaTokensPerClause - 9 padding opportunities/u);
  assert.match(tex, /first opportunity in the intentionally empty fifth fixed-width clause slot is padding/u);
  assert.match(tex, /does not traverse that empty rectangle/u);
  assert.match(tex, /Cook-Levin empty fifth-clause padding run/u);
  assert.match(tex, /traverses exactly FormulaTokensPerClause padding opportunities in the intentionally empty fifth fixed-width clause rectangle/u);
  assert.match(tex, /first opportunity in the intentionally empty sixth slot are padding/u);
  assert.match(tex, /does not traverse that sixth rectangle/u);
  assert.match(tex, /Cook-Levin remaining first-constraint padding run/u);
  assert.match(tex, /4432 plus sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(tex, /FormulaClauseSlotsPerConstraint - 5/u);
  assert.match(tex, /endpoint is the Sep beginning the second scheduled constraint/u);
  assert.match(tex, /observes but does not emit that separator/u);
  assert.match(tex, /Cook-Levin second-constraint separator step/u);
  assert.match(tex, /4554 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 37\)\)/u);
  assert.match(tex, /direct next schedule token is T/u);
  assert.match(tex, /does not emit the following T/u);
  assert.match(tex, /Cook-Levin second-constraint first-literal sign step/u);
  assert.match(tex, /4676 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 38\)\)/u);
  assert.match(tex, /direct next schedule token is the first unary T of a nonzero variable index/u);
  assert.match(tex, /does not emit the following unary T/u);
  assert.match(tex, /Cook-Levin second-constraint first-literal first unary-unit step/u);
  assert.match(tex, /4798 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 39\)\)/u);
  assert.match(tex, /direct next schedule token is the second unary T/u);
  assert.match(tex, /does not emit the following second unary T/u);
  assert.match(tex,
    /Cook\\allowbreak\{\}Levin\\allowbreak\{\}Builder\\allowbreak\{\}Second\\allowbreak\{\}Constraint\\allowbreak\{\}First\\allowbreak\{\}Literal\\allowbreak\{\}First\\allowbreak\{\}Unary\\allowbreak\{\}Unit\\allowbreak\{\}Step/u);
  assert.match(tex, /Cook-Levin second-constraint first-literal terminator step/u);
  assert.match(tex, /5164 plus the sixteen inherited\/generated unary-evaluator rule counts/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 42\)\)/u);
  assert.match(tex, /direct next schedule token is Finish when tapeWidth is one/u);
  assert.match(tex, /does not emit the following Finish in the width-one case/u);
  assert.match(tex, /successor-token composition now evaluates the represented tableau width/u);
  assert.match(tex, /5284 plus the eighteen\s+inherited\/generated unary-evaluator rule counts/u);
  assert.match(tex, /encodedFormula\.take \(2 \* \(FormulaWidth \+ 43\)\)/u);
  assert.match(tex, /next opportunity is proved to be padding at width one and unary/u);
  assert.match(tex, /82-declaration audit has 37 empty/u);
  assert.match(tex, /sixth opportunity machine reuses the reviewed 93-rule/u);
  assert.match(tex, /complete table has exactly 6004 literal rules plus thirty/u);
  assert.match(tex,
    /encodedFormula\.take \(2 \* \(FormulaWidth \+ 43 \+ if tapeWidth = 1 then 0 else 6\)\)/u);
  assert.match(tex, /first unary-index\s+\\code\{T\} of the following literal/u);
  assert.match(tex, /Locked-NAND global carrier and trace equivalence/u);
  assert.match(tex, /Exact X\/T\/O\/R\/L\/z carrier separation/u);
  assert.match(tex, /does not assemble the complete exposed candidates/u);
  assert.equal(tex.includes('The terminator and rest of clause three'), false);
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
