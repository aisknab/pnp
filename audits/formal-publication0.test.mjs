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

test('publication consumes the reviewed recursive-refinement map and inventory counts', async () => {
  const [status, mapText] = await Promise.all([
    status0(),
    readFile(new URL('../publication/FORMAL_PUBLICATION_MAP.json', import.meta.url), 'utf8'),
  ]);
  const map = JSON.parse(mapText);
  assert.equal(sha256Text0(stableStringify0(map)),
    '364acf9b53699aab89b2a927683e1f8ee8d7830c810b935c315e1302cae4f141');
  assert.equal(map.milestoneSourceClosureSha256,
    'fb3ecdea2590b6a65ae8de5ebd9e1b86c1e36f2ae9659de7febb817f4306ce3d');
  assert.equal(Object.keys(map.earnedMilestoneTheoremKernelTypeSha256).length, 323);
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
  ], [6901, 3143, 2585, 1228, 63]);
});

test('canonical report source is current and the committed PDF artifact exists', async () => {
  const [tex, status] = await Promise.all([
    readFile(new URL('../canonical_proof_report.tex', import.meta.url), 'utf8'),
    status0(),
  ]);
  assert.match(tex, /The repository does not currently establish \$P=NP\$\./u);
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
