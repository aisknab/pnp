import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import { REQUIRED_MILESTONE_THEOREMS0 } from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const MODULE = 'CookLevinCompleteBuilder';
const NAMESPACE = 'PNP.Concrete.CookLevin';
const SOURCE = 'lean/PNP/Concrete/CookLevinCompleteBuilder.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinCompleteBuilderAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinCompleteBuilder.lean';
const TEST = 'audits/lean-concrete-cook-levin-complete-builder0.test.mjs';
const DOC = 'docs/lean_cook_levin_complete_builder.md';
const PLAN = 'docs/plans/2026-09-06-complete-cook-levin-formula-builder.md';
const MILESTONE = 'concrete-cook-levin-complete-builder';
const CHECKPOINT = 'reductions-complete-cook-levin-builder';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-10-230';
const PUBLIC_NAMES = [
  'formulaBuilderMachine', 'formulaBuilderTimeBound',
  'formulaBuilderMachine_accept', 'formulaBuilderMachine_output',
  'formulaBuilder', 'formulaBuilder_output', 'formulaBuilder_rawRefinement_output',
  'polynomialReduction', 'polynomialReduction_output',
  'cook_levin_formula_builder_checked_complete',
];
const THEOREMS = PUBLIC_NAMES.filter(name =>
  !['formulaBuilderMachine', 'formulaBuilderTimeBound', 'formulaBuilder',
    'polynomialReduction'].includes(name)).map(name => NAMESPACE + '.' + name);
const FLAGS = [
  'leanConcreteCookLevinBuilderDynamicCursorFormalized',
  'leanConcreteCookLevinFormulaBuilderFormalized',
  'leanConcreteCookLevinBuilderRawRefinementFormalized',
  'leanConcreteCookLevinBuilderPolynomialReductionFormalized',
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => value.replace(/\s+/gu, ' ').trim();
const imports0 = value => [...value.matchAll(/^import\s+(\S+)\s*$/gmu)].map(m => m[1]);

function validateSource0(source) {
  const errors = [];
  const require0 = (condition, label) => { if (!condition) errors.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(stripped);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|choice)\b/u.test(stripped), 'shortcut');
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderOutputFinalizer',
    'PNP.Concrete.LockedNANDTargetEmitterControllerCompletionTrace',
    'PNP.Concrete.PipelineRefinement',
  ]), 'imports');
  require0(compact.includes('private def completeWorkMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine := WorkMachineChain.machine (BuilderRawInputLoop.machine verifier) BuilderOutputFinalizer.machine')
    && compact.includes('def formulaBuilderMachine {language : Language} (verifier : PolynomialTimeVerifier language) : Machine := compileWorkMachine (completeWorkMachine verifier)'), 'finite-machine');
  require0(compact.includes('def formulaBuilderTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial := .add (.add (BuilderRawInputLoop.rawTimeBound verifier) (.constant 6)) (BuilderOutputFinalizer.rawTimeBound verifier)')
    && compact.includes('6 * steps ≤ (formulaBuilderTimeBound problem.verifier).eval problem.input.length'), 'complete-budget');
  require0(compact.includes('BuilderCanonicalOutput.workRun_canonical_from_raw problem')
    && compact.includes('BuilderOutputFinalizer.canonical_workRun_exact problem')
    && compact.includes('WorkMachineChain.workRunExact')
    && compact.includes('startConfig_compileWorkMachine_blankEquivalent')
    && compact.includes('Tape.outputBits_eq_of_blankEquivalent'), 'ordinary-input-output-bridge');
  require0(compact.includes('theorem formulaBuilderMachine_accept {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) : boundedDecide (formulaBuilderMachine verifier) ((formulaBuilderTimeBound verifier).eval input.length) input = .accept')
    && compact.includes('theorem formulaBuilderMachine_output {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) : machineOutput (formulaBuilderMachine verifier) ((formulaBuilderTimeBound verifier).eval input.length) input = (VerifierTableauProblem.mk verifier input).encodedFormula'), 'all-input-execution');
  require0(compact.includes('def formulaBuilder {language : Language} (verifier : PolynomialTimeVerifier language) : PolynomialTimeFunction := {program := .machine (formulaBuilderMachine verifier) (formulaBuilderTimeBound verifier) runtimeBound := formulaBuilderTimeBound verifier outputSizeBound := BuilderCanonicalOutput.encodedSizeBound verifier haltsWithin := by')
    && compact.includes('runtime_le := by')
    && compact.includes('output_size_le := by')
    && compact.includes('BuilderCanonicalOutput.encodedFormula_length_le (VerifierTableauProblem.mk verifier input)'), 'polynomial-function');
  require0(compact.includes('theorem formulaBuilder_rawRefinement_output {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) : machineOutput (FunctionProgram.RawRefinement.compile (formulaBuilder verifier).program).machine ((FunctionProgram.RawRefinement.compile (formulaBuilder verifier).program).timeBound.eval (BitString.size input)) input = (VerifierTableauProblem.mk verifier input).encodedFormula')
    && compact.includes('FunctionProgram.RawRefinement.compile_output_eq'), 'complete-raw-refinement');
  require0(compact.includes('def polynomialReduction {language : Language} (verifier : PolynomialTimeVerifier language) : PolynomialReduction language CNFSAT := {function := formulaBuilder verifier correctness := by')
    && compact.includes('VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language'), 'exact-reduction');
  require0(compact.includes('theorem cook_levin_formula_builder_checked_complete {language : Language} (verifier : PolynomialTimeVerifier language) : ∀ input, (polynomialReduction verifier).function.output input = (VerifierTableauProblem.mk verifier input).encodedFormula :='), 'source-only-endpoint');
  return errors;
}

test('M230 source closes the all-input finite-machine polynomial builder interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M230 axiom audit covers every public declaration through the root', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  assert.deepEqual(explicitLeanDeclarationHeads0(source).map(({ name }) => name), PUBLIC_NAMES);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(m => m[1]),
    PUBLIC_NAMES.map(name => NAMESPACE + '.' + name));
});

test('M230 registers one exact theorem-pin interface across producers and consumers', async () => {
  const [root, packageText, verifier, workflow, regression, inventorySource,
    publicationText] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
    text0('lean-audit/PNPTheoremInventory.lean'), text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]);
  assert.ok(imports0(root).includes('PNP.Concrete.' + MODULE));
  assert.equal(JSON.parse(packageText).scripts['audit:m230'], 'node --test ' + TEST);
  for (const consumer of [verifier, workflow]) assert.ok(consumer.includes(TEST));
  assert.ok(workflow.includes(AUDIT) && workflow.includes(REGRESSION));
  assert.ok(regression.includes('cook_levin_formula_builder_checked_complete'));
  for (const theorem of THEOREMS) {
    assert.ok(inventorySource.includes(String.fromCharCode(96) + theorem));
    assert.ok(REQUIRED_MILESTONE_THEOREMS0.includes(theorem));
  }
  const publication = JSON.parse(publicationText);
  assert.deepEqual(publication.milestones.find(row => row.id === MILESTONE)?.requiredTheorems,
    THEOREMS);
  for (const theorem of THEOREMS) {
    assert.ok(Object.hasOwn(publication.earnedMilestoneTheoremKernelTypeSha256, theorem));
  }
});

test('M230 compiled publication earns only the fixed complete-builder checkpoint', async () => {
  const [statusText, mirrorStatus, inventoryText, mirrorInventory, progressText, report] =
    await Promise.all([
      text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('public/pnp-status.json'),
      text0('status/LEAN_THEOREM_INVENTORY.json'), text0('public/pnp-theorem-inventory.json'),
      text0('status/PROOF_PROGRESS.json'), text0('canonical_proof_report.tex'),
    ]);
  assert.equal(statusText, mirrorStatus);
  assert.equal(inventoryText, mirrorInventory);
  const status = JSON.parse(statusText);
  const inventory = JSON.parse(inventoryText);
  const progress = JSON.parse(progressText);
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  assert.equal(status.formalPublicationMilestones.find(row => row.id === MILESTONE)?.earned, true);
  for (const flag of FLAGS) assert.equal(status[flag], true, flag);
  for (const name of THEOREMS) {
    const declaration = inventory.milestoneCandidates.find(row => row.name === name);
    assert.equal(declaration?.kind, 'theorem', name);
    const semantic = ['polynomialReduction_output', 'cook_levin_formula_builder_checked_complete']
      .includes(name.split('.').at(-1));
    assert.deepEqual(declaration.axioms, semantic
      ? ['Classical.choice', 'Quot.sound', 'propext'] : ['Quot.sound', 'propext']);
  }
  assert.ok(report.includes(status.coordinate));
  assert.ok(compact0(report).includes('risk-weighted proof completion estimate is '
    + progress.proofCompletion.percent + ' percent'));
  assert.ok(compact0(report).includes('Formal artefact coverage: '
    + progress.formalArtefactCoverage.earnedRows + ' of '
    + progress.formalArtefactCoverage.totalRows + ' current scoped publication rows earned.'));
  const review = progress.history.find(entry => entry.asOfCoordinate === COORDINATE);
  assert.equal(review?.scoreChanged, true);
  assert.deepEqual(review.changedCheckpointIds, [CHECKPOINT]);
  assert.equal(review.riskWeightedProofCompletionPercent, 38);
  assert.deepEqual(review.changeRecords[0].oldAndNewTotal, { old: 35, new: 38 });
  assert.equal(review.globalGatesClosed, 0);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  const rows = status.formalPublicationMilestones;
  assert.equal(progress.formalArtefactCoverage.earnedRows, rows.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, rows.length);
  if (progress.asOfCoordinate === COORDINATE) {
    assert.equal(progress.tracks.find(track => track.id === 'concrete-reductions').pointsEarned, 18);
    assert.equal(progress.tracks.flatMap(track => track.checkpoints)
      .find(checkpoint => checkpoint.id === CHECKPOINT).status, 'earned');
    assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
    assert.deepEqual(inventory.projectAxioms, []);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);
    assert.equal(progress.globalGates.filter(gate => gate.status === 'closed').length, 0);
  }
});

test('M230 current documentation separates the builder checkpoint from global proof gates', async () => {
  const [doc, plan, ...active] = await Promise.all([
    text0(DOC), text0(PLAN), text0('README.md'), text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'), text0('docs/proof_pipeline.md'),
    text0('docs/audit_questions.md'), text0('docs/proof_progress.md'),
  ]);
  for (const text of [doc, ...active]) assert.match(text, /M230/u);
  assert.ok(doc.includes('cook_levin_formula_builder_checked_complete'));
  assert.ok(doc.includes(CHECKPOINT));
  for (const phrase of ['all-input', 'polynomial', 'ZeroSlack', 'NP-completeness', 'PCCMin']) {
    assert.ok(doc.includes(phrase), phrase);
  }
  assert.match(compact0(plan), /legacy|manuscript/iu);
});

test('M230 hostile source mutations reject finite-only, supplied, unbounded, or inexact builders', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['(verifier : PolynomialTimeVerifier language) : Machine :=',
      '(verifier : PolynomialTimeVerifier language) (trace : True) : Machine :=', 'finite-machine'],
    ['(.constant 6)', '(.constant 0)', 'complete-budget'],
    ['BuilderCanonicalOutput.workRun_canonical_from_raw problem', 'suppliedWorkRun problem',
      'ordinary-input-output-bridge'],
    ['(input : BitString) :\n    boundedDecide', '(input : Fin 1) :\n    boundedDecide', 'all-input-execution'],
    ['outputSizeBound := BuilderCanonicalOutput.encodedSizeBound verifier',
      'outputSizeBound := .constant 0', 'polynomial-function'],
    ['FunctionProgram.RawRefinement.compile_output_eq', 'suppliedRawOutput', 'complete-raw-refinement'],
    ['{function := formulaBuilder verifier', '{function := suppliedBuilder verifier', 'exact-reduction'],
    [':\n    ∀ input, (polynomialReduction verifier).function.output input =',
      '(certificate : True) :\n    ∀ input, (polynomialReduction verifier).function.output input =',
      'source-only-endpoint'],
  ];
  for (const [before, after, rejection] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + rejection);
    assert.ok(validateSource0(source.replace(before, after)).includes(rejection), rejection);
  }
  assert.ok(validateSource0(source + '\naxiom suppliedAuthority : True\n').includes('assumption'));
});

test('M230 hostile progress transitions reject credit without compiled builder evidence', async () => {
  const [p, s, i] = await Promise.all([
    text0('status/PROOF_PROGRESS.json'), text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
    text0('status/LEAN_THEOREM_INVENTORY.json'),
  ]);
  const progress = JSON.parse(p);
  const status = JSON.parse(s);
  const inventory = JSON.parse(i);
  if (progress.asOfCoordinate !== COORDINATE) return;
  const withoutBuilder = structuredClone(status);
  withoutBuilder.leanConcreteCookLevinFormulaBuilderFormalized = false;
  assert.throws(() => validateProofProgress0(progress, withoutBuilder, inventory));
  const missingTheorem = structuredClone(inventory);
  missingTheorem.declarations = missingTheorem.declarations
    .filter(row => row.name !== NAMESPACE + '.cook_levin_formula_builder_checked_complete');
  assert.throws(() => validateProofProgress0(progress, status, missingTheorem));
  const noRationale = structuredClone(progress);
  noRationale.history.at(-1).changeRecords[0].loadBearingRationale = '';
  assert.throws(() => validateProofProgress0(noRationale, status, inventory));
  const unearnedExtra = structuredClone(progress);
  unearnedExtra.proofCompletion.pointsEarned += 2;
  unearnedExtra.proofCompletion.percent += 2;
  assert.throws(() => validateProofProgress0(unearnedExtra, status, inventory));
});
