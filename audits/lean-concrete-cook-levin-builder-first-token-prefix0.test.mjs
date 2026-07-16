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
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderFirstTokenPrefix.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinBuilderFirstTokenPrefixAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinBuilderFirstTokenPrefix.lean';
const TEST = 'audits/lean-concrete-cook-levin-builder-first-token-prefix0.test.mjs';
const PREFIX = 'PNP.Concrete.CookLevin.BuilderFirstTokenPrefix.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'prefixState'],
  ['def', 'appenderState'],
  ['theorem', 'prefixState_injective'],
  ['theorem', 'appenderState_injective'],
  ['theorem', 'prefixState_ne_appenderState'],
  ['def', 'renamedPrefix'],
  ['def', 'renamedAppender'],
  ['def', 'launchRules'],
  ['def', 'rules'],
  ['def', 'machine'],
  ['theorem', 'rules_length'],
  ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['def', 'workSteps'],
  ['def', 'rawTimeBound'],
  ['def', 'finalTape'],
  ['def', 'finalConfiguration'],
  ['theorem', 'finalTape_represents'],
  ['theorem', 'findWorkRule_prefix_of_some'],
  ['theorem', 'findWorkRule_appender_of_some'],
  ['theorem', 'launch_workStep'],
  ['theorem', 'prefix_workRunExact'],
  ['theorem', 'appender_workRunExact'],
  ['theorem', 'workRunExact'],
  ['theorem', 'finalTokenBits_eq_encodedFormula_take_two'],
  ['theorem', 'rawTimeBound_eval'],
  ['theorem', 'rawTimeBound_le'],
  ['theorem', 'run_compile_exact'],
  ['theorem', 'run_compile_rawTimeBound'],
  ['theorem', 'run_compile_rawTimeBound_blankEquivalent'],
  ['theorem', 'boundedDecide_compile_accept'],
  ['theorem', 'boundedDecide_compile_ne_timeout'],
  ['theorem', 'prefixEndpoint_before_launch_timeout'],
  ['theorem', 'malformedPrefixTally_timeout'],
  ['theorem', 'malformedAppenderTally_timeout'],
  ['theorem', 'malformedAppenderOutput_timeout'],
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
  const executable = ['launchRules', 'rules', 'machine']
    .map((name) => declarationBlock0(stripped, name)).join(' ');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderTokenAppender',
  ]), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace BuilderFirstTokenPrefix$/mu.test(stripped)
    && /end BuilderFirstTokenPrefix\s+end CookLevin\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice|referenceMinimum|SATOracle)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(!/\b(?:FunctionProgram|DecisionProgram|PolynomialTimeFunction|PolynomialReduction|RawRefinement|NPComplete|cnfSATInP|cnfSATNPComplete|p_eq_np|certificate)\b/u
    .test(stripped), 'forbidden-host-composition-or-overclaim');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('Literal composition of the complete raw-input preparation prefix')
    && prose.includes('first two bits of the encoded formula')
    && prose.includes('does not compute the remaining width header')
    && prose.includes('construct the complete formula')
    && prose.includes('P = NP'), 'explicit-boundary');

  require0(compact.includes('def prefixState (state : Nat) : Nat := inputState state')
    && compact.includes('def appenderState (state : Nat) : Nat := simulationState state')
    && compact.includes('theorem prefixState_injective')
    && compact.includes('theorem appenderState_injective')
    && compact.includes('theorem prefixState_ne_appenderState'),
  'disjoint-injective-state-images');
  require0(compact.includes('def renamedPrefix : WorkMachine := renameMachine prefixState BuilderInputPrefix.machine')
    && compact.includes('def renamedAppender : WorkMachine := renameMachine appenderState BuilderTokenAppender.machine'),
  'complete-component-renaming');
  require0(compact.includes('def launchRules : List WorkRule := PipelineStageBridges.launchRules (prefixState BuilderInputPrefix.machine.acceptState) (appenderState BuilderTokenAppender.machine.startState)')
    && compact.includes('def rules : List WorkRule := launchRules ++ (BuilderInputPrefix.machine.rules.map (renameRule prefixState) ++ BuilderTokenAppender.machine.rules.map (renameRule appenderState))'),
  'nine-rule-bridge-first-table');
  require0(compact.includes('theorem rules_length : rules.length = 184')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'literal-table-audit');
  require0(compact.includes('startState := prefixState BuilderInputPrefix.machine.startState')
    && compact.includes('acceptState := appenderState BuilderTokenAppender.machine.acceptState')
    && compact.includes('rejectState := appenderState BuilderTokenAppender.machine.rejectState'),
  'global-start-and-halts');
  require0(!/\b(?:input|problem|encodedFormula|NatPolynomial\.eval|SAT)\b/u.test(executable),
    'answer-independent-executable-rules');

  require0(compact.includes('def workSteps (input : BitString) : Nat := BuilderInputPrefix.workSteps input + 1 + BuilderTokenAppender.workSteps input []')
    && compact.includes('def rawTimeBound : NatPolynomial := .add (.add BuilderInputPrefix.rawTimeBound (.constant 6)) BuilderTokenAppender.firstTokenRawTimeBound')
    && compact.includes('18 * input.length * input.length + 87 * input.length + 147'),
  'exact-composed-bound');
  require0(compact.includes('def finalTape (input : BitString) : WorkTape := BuilderTokenAppender.workspaceTape input (PipelineInputFramer.totalInputFramerOutsideLeft input) [.t]')
    && compact.includes('theorem finalTape_represents')
    && compact.includes('CNFToken.t.bits = problem.encodedFormula.take 2'),
  'exact-first-token-endpoint');
  require0(compact.includes('theorem findWorkRule_prefix_of_some')
    && compact.includes('theorem findWorkRule_appender_of_some')
    && compact.includes('theorem launch_workStep (input : BitString)')
    && compact.includes('theorem prefix_workRunExact (input : BitString)')
    && compact.includes('theorem appender_workRunExact (input : BitString)')
    && compact.includes('theorem workRunExact (input : BitString)'),
  'isolated-exact-composition');
  require0(compact.includes('theorem run_compile_rawTimeBound (input : BitString)')
    && compact.includes('theorem run_compile_rawTimeBound_blankEquivalent')
    && compact.includes('theorem boundedDecide_compile_accept'),
  'compiled-external-bound');
  require0(compact.includes('theorem prefixEndpoint_before_launch_timeout')
    && compact.includes('theorem malformedPrefixTally_timeout')
    && compact.includes('theorem malformedAppenderTally_timeout')
    && compact.includes('theorem malformedAppenderOutput_timeout')
    && compact.includes('theorem work_one_step_short_timeout')
    && compact.includes('workSteps input - 1'),
  'fail-closed-negative-boundary');

  return failures;
}

test('first-token prefix is literal, exact, composed, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel transcript covers all 37 public declarations exactly once', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 37);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 37);
});

test('root, package, verifier, workflow, and regression enforce the milestone', async () => {
  const [root, packageText, verifier, workflow, regression] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0(REGRESSION),
  ]);
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinBuilderFirstTokenPrefix'));
  assert.match(packageText, /audits\/lean-concrete-cook-levin-builder-first-token-prefix0\.test\.mjs/u);
  assert.match(verifier, /audits\/lean-concrete-cook-levin-builder-first-token-prefix0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderFirstTokenPrefixAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderFirstTokenPrefix\.lean/u);
  assert.match(workflow, /Cook-Levin builder first-token-prefix axiom closure/u);
  assert.ok(workflow.includes(
    "grep -Fc 'does not depend on any axioms')\" -eq 21",
  ));
  assert.ok(workflow.includes(
    "grep -Fc 'depends on axioms: [propext]')\" -eq 3",
  ));
  assert.ok(workflow.includes(
    "grep -Fc 'depends on axioms: [propext, Quot.sound]')\" -eq 13",
  ));
  assert.match(regression, /rules\.length = 184/u);
  assert.match(regression, /workSteps \(\[\] : BitString\) = 16[\s\S]*workSteps \(\[true, true, true, true\] : BitString\) = 115/u);
  assert.match(regression, /rawTimeBound\.eval 0 = 147[\s\S]*rawTimeBound\.eval 4 = 783/u);
  assert.match(regression, /prefixEndpoint_before_launch_timeout/u);
  assert.match(regression, /malformedPrefixTally_timeout/u);
  assert.match(regression, /malformedAppenderTally_timeout/u);
  assert.match(regression, /malformedAppenderOutput_timeout/u);
  assert.equal(TEST.endsWith('0.test.mjs'), true);
});

test('collision, bridge, shadowing, token, bound, timeout, and shortcut mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('def appenderState (state : Nat) : Nat := simulationState state',
      'def appenderState (state : Nat) : Nat := inputState state'),
    source.replace('launchRules ++', '[] ++'),
    source.replace('launchRules ++\n    (BuilderInputPrefix.machine.rules.map',
      'BuilderInputPrefix.machine.rules.map (renameRule prefixState) ++\n    (launchRules ++'),
    source.replace('(appenderState BuilderTokenAppender.machine.startState)',
      '(appenderState BuilderTokenAppender.machine.acceptState)'),
    source.replace('rules.length = 184', 'rules.length = 183'),
    source.replace('BuilderTokenAppender.workSteps input []',
      'BuilderTokenAppender.workSteps input [.t]'),
    source.replace('(.constant 6)', '(.constant 5)'),
    source.replace('87 * input.length + 147', '86 * input.length + 147'),
    source.replace('input) [.t]', 'input) [.f]'),
    source.replace('CNFToken.t.bits = problem.encodedFormula.take 2',
      'CNFToken.f.bits = problem.encodedFormula.take 2'),
    source.replaceAll('workSteps input - 1', 'workSteps input'),
    source.replace('theorem prefixEndpoint_before_launch_timeout',
      'private theorem prefixEndpoint_before_launch_timeout'),
    `${source}\naxiom hiddenBuilderOracle : True\n`,
    `${source}\ntheorem usesChoice : True := Classical.choice (show Nonempty True from \u27e8True.intro\u27e9)\n`,
    `${source}\ntheorem callerCertificate (certificate : True) : True := certificate\n`,
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
    `${source}\ndef hostComposition := FunctionProgram.compose\n`,
    `${source}\ntheorem minimizerCall : True := by exact referenceMinimum_invariant\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('first-token composition remains earned beneath the complete-header boundary', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCookLevinBuilderFirstTokenPrefixFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderFirstTokenPrefixAxiomAuditPassed, true);
  assert.equal(status.leanConcreteCookLevinBuilderFirstTokenPrefixAuditedDeclarationCount, 37);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderInputPrefixComposed, true);
  assert.equal(status.leanConcreteCookLevinBuilderUnaryPolynomialFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderCompleteHeaderFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderCompleteHeaderInputPrefixAppenderComposed, true);
  assert.equal(status.leanConcreteCookLevinBuilderDynamicCursorFormalized, false);
  assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
  assert.equal(status.leanConcreteCookLevinBuilderRawRefinementFormalized, false);
  assert.equal(status.leanConcreteCookLevinBuilderPolynomialReductionFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.deepEqual(status.projectSpecificAxiomInventory, [
    'PNP.CheckPCCPackexp',
    'PNP.GeneratePCCPack',
    'PNP.LockedNANDThreshold',
    'PNP.ResidualBandExactMinimization',
  ]);
  assert.equal(status.remainingBlockers.length, 6);
});
