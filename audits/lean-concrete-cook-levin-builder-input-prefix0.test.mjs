import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderInputPrefix.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinBuilderInputPrefixAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinBuilderInputPrefix.lean';
const TEST = 'audits/lean-concrete-cook-levin-builder-input-prefix0.test.mjs';
const PREFIX = 'PNP.Concrete.CookLevin.BuilderInputPrefix.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'framerState'],
  ['def', 'tallyState'],
  ['theorem', 'framerState_injective'],
  ['theorem', 'tallyState_injective'],
  ['theorem', 'framerState_ne_tallyState'],
  ['def', 'renamedFramer'],
  ['def', 'renamedTally'],
  ['def', 'launchRules'],
  ['def', 'rules'],
  ['def', 'machine'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['def', 'workSteps'],
  ['def', 'rawTimeBound'],
  ['def', 'finalTape'],
  ['def', 'finalConfiguration'],
  ['theorem', 'finalTape_represents'],
  ['theorem', 'finalTape_tally_length'],
  ['theorem', 'machine_isHalted_framer_false'],
  ['theorem', 'machine_isHalted_tally_false_of_local'],
  ['theorem', 'findWorkRule_framer_of_some'],
  ['theorem', 'findWorkRule_tally_of_some'],
  ['theorem', 'framer_workStep?_of_some'],
  ['theorem', 'tally_workStep?_of_some'],
  ['theorem', 'framer_workRunExact'],
  ['theorem', 'launch_workStep'],
  ['theorem', 'tally_workRunExact'],
  ['theorem', 'workRunExact'],
  ['theorem', 'finalConfiguration_isHalted'],
  ['theorem', 'rawTimeBound_eval'],
  ['theorem', 'rawTimeBound_le'],
  ['theorem', 'run_compile_exact'],
  ['theorem', 'run_compile_rawTimeBound'],
  ['theorem', 'run_compile_rawTimeBound_blankEquivalent'],
  ['theorem', 'boundedDecide_compile_accept'],
  ['theorem', 'boundedDecide_compile_ne_timeout'],
  ['def', 'malformedTallyConfiguration'],
  ['theorem', 'malformedTallyScanSymbol_isHalted_false'],
  ['theorem', 'malformedTallyScanSymbol_workStep_none'],
  ['theorem', 'malformedTallyScanSymbol_timeout'],
  ['theorem', 'work_one_step_short_timeout'],
]);

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function publicHeadPairs0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ kind, name }) => [kind, name]);
}

function declarationBlocks0(source) {
  const declarations = explicitLeanDeclarationHeads0(source);
  return declarations.map((declaration, index) => ({
    ...declaration,
    block: source.slice(declaration.index,
      declarations[index + 1]?.index ?? source.length),
  }));
}

function declarationBlock0(source, name) {
  return declarationBlocks0(source)
    .find((entry) => entry.name === name)?.block ?? '';
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const prose = source.replaceAll('\x60', '').replace(/\s+/gu, ' ');
  const rulesBlock = declarationBlock0(stripped, 'rules');
  const machineBlock = declarationBlock0(stripped, 'machine');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderInputLength',
    'PNP.Concrete.PipelineStageBridges',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace BuilderInputPrefix$/mu.test(stripped)
    && /end BuilderInputPrefix\s+end CookLevin\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum|SATOracle|formulaBitSlotDirect)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('Literal composition of the all-input framer')
    && prose.includes('only an executable input-preparation prefix')
    && prose.includes('emits no formula bit')
    && prose.includes('polynomial reduction')
    && prose.includes('P = NP theorem'), 'explicit-nonclaims');
  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|cnfSATNPComplete|p_eq_np|formulaBitSlotDirect)\b/u
    .test(stripped), 'no-reduction-or-class-claim');

  require0(compact.includes('def framerState (state : Nat) : Nat := inputState state')
    && compact.includes('def tallyState (state : Nat) : Nat := simulationState state')
    && compact.includes('theorem framerState_ne_tallyState'),
  'disjoint-injective-state-images');
  require0(compact.includes('def launchRules : List WorkRule := PipelineStageBridges.launchRules (framerState PipelineInputFramer.pairedInputFramer.acceptState) (tallyState BuilderInputLength.machine.startState)')
    && compact.includes('def rules : List WorkRule := launchRules ++ (PipelineInputFramer.pairedInputFramer.rules.map (renameRule framerState) ++ BuilderInputLength.machine.rules.map (renameRule tallyState))'),
  'literal-bridge-first-table');
  require0(compact.includes('def machine : WorkMachine := { rules := rules startState := framerState PipelineInputFramer.pairedInputFramer.startState acceptState := tallyState BuilderInputLength.machine.acceptState rejectState := tallyState BuilderInputLength.machine.rejectState }'),
  'global-start-and-halts');
  require0(!/\binput\b/u.test(rulesBlock)
    && !/formulaBitSlotDirect|NatPolynomial\.eval|encodedFormula/u.test(rulesBlock + machineBlock),
  'answer-independent-executable-rules');

  require0(compact.includes('def workSteps (input : BitString) : Nat := PipelineInputFramer.totalInputFramerWorkSteps input + 1 + BuilderInputLength.workSteps input.length')
    && compact.includes('def rawTimeBound : NatPolynomial := .add (.quadratic 18 93) (.linear 63 0)'),
  'explicit-cumulative-polynomial');
  require0(compact.includes('def finalTape (input : BitString) : WorkTape := BuilderInputLength.finalTape input (PipelineInputFramer.totalInputFramerOutsideLeft input)')
    && compact.includes('theorem finalTape_represents')
    && compact.includes('theorem finalTape_tally_length'),
  'exact-preserved-input-and-tally');
  require0(compact.includes('theorem launch_workStep (input : BitString)')
    && compact.includes('theorem workRunExact (input : BitString)')
    && compact.includes('workRunExact? machine (workSteps input)')
    && compact.includes('some (finalConfiguration input)'),
  'literal-launch-and-all-input-trace');
  require0(compact.includes('theorem rawTimeBound_le (input : BitString)')
    && compact.includes('6 * workSteps input ≤ rawTimeBound.eval (BitString.size input)')
    && compact.includes('theorem run_compile_rawTimeBound (input : BitString)')
    && compact.includes('theorem boundedDecide_compile_accept (input : BitString)'),
  'compiled-external-bound');
  require0(compact.includes('def malformedTallyConfiguration')
    && compact.includes('head := WorkSymbol.zeroOne')
    && compact.includes('theorem malformedTallyScanSymbol_timeout (fuel : Nat)')
    && compact.includes('= WorkVerdict.timeout := by'),
  'malformed-scan-symbol-timeout');
  require0(compact.includes('theorem work_one_step_short_timeout (input : BitString)')
    && compact.includes('workSteps input - 1')
    && compact.includes('= .timeout := by'), 'one-step-short-timeout');

  return failures;
}

test('Cook-Levin builder input prefix is literal, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel transcript covers all 40 public declarations exactly once', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 40);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 40);
});

test('root, package, verifier, workflow, and regression enforce the milestone', async () => {
  const [root, packageText, verifier, workflow, regression] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0(REGRESSION),
  ]);
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinBuilderInputPrefix'));
  assert.match(packageText, /audits\/lean-concrete-cook-levin-builder-input-prefix0\.test\.mjs/u);
  assert.match(verifier, /audits\/lean-concrete-cook-levin-builder-input-prefix0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderInputPrefixAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderInputPrefix\.lean/u);
  assert.match(workflow, /Cook-Levin builder input-prefix axiom closure/u);
  assert.ok(workflow.includes(
    "grep -Fc 'does not depend on any axioms')\" -eq 29",
  ));
  assert.ok(workflow.includes(
    "grep -Fc 'depends on axioms: [propext]')\" -eq 1",
  ));
  assert.ok(workflow.includes(
    "grep -Fc 'depends on axioms: [propext, Quot.sound]')\" -eq 10",
  ));
  assert.match(regression, /workSteps \(\[\] : BitString\) = 7[\s\S]*workSteps \(\[true, true, false, false\] : BitString\) = 92/u);
  assert.match(regression, /rawTimeBound\.eval 0 = 93[\s\S]*rawTimeBound\.eval 4 = 633/u);
  assert.match(regression, /\[false, false, false, false\][\s\S]*\[true, true, true, true\]/u);
  assert.match(regression, /launch_workStep/u);
  assert.match(regression, /work_one_step_short_timeout/u);
  assert.match(regression, /malformedTallyScanSymbol_timeout/u);
  assert.equal(TEST.endsWith('0.test.mjs'), true);
});

test('namespace, bridge, bound, endpoint, timeout, assumption, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('def tallyState (state : Nat) : Nat := simulationState state',
      'def tallyState (state : Nat) : Nat := inputState state'),
    source.replace('launchRules ++', '[] ++'),
    source.replace('(tallyState BuilderInputLength.machine.startState)',
      '(tallyState BuilderInputLength.machine.acceptState)'),
    source.replace('.quadratic 18 93', '.quadratic 17 93'),
    source.replace('.linear 63 0', '.linear 62 0'),
    source.replace('totalInputFramerWorkSteps input + 1 +',
      'totalInputFramerWorkSteps input +'),
    source.replace('BuilderInputLength.finalTape input',
      'BuilderInputLength.inputTape input'),
    source.replaceAll('workSteps input - 1', 'workSteps input'),
    `${source}\naxiom hiddenBuilderOracle : True\n`,
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('input prefix remains below formula emission, reduction, and class theorems', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixAxiomAuditPassed, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixAuditedDeclarationCount, 40);
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixCompiledRawMachineFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixExternalInputSizePolynomialFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixMalformedScanSymbolTimeoutFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputPrefixLiteralFramerLaunchFormalized, true);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
