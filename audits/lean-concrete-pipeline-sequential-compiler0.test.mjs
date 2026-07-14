import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE = 'lean/PNP/Concrete/PipelineSequentialCompiler.lean';
const AUDIT = 'lean-audit/PNPConcretePipelineSequentialCompilerAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcretePipelineSequentialCompiler.lean';
const PREFIX = 'PNP.Concrete.PipelineSequentialCompiler.';

const HEADS = Object.freeze([
  ['def', 'sequentialMachine'],
  ['def', 'secondSuffixWorkSteps'],
  ['def', 'sequentialWorkSteps'],
  ['def', 'sequentialRawSteps'],
  ['def', 'firstOutputSizeBound'],
  ['def', 'sequentialOutputSizeBound'],
  ['def', 'sequentialRawTimeBound'],
  ['theorem', 'firstOutputSizeBound_eval'],
  ['theorem', 'sequentialOutputSizeBound_eval'],
  ['theorem', 'secondAcceptingSuffix_workRunExact_of_rawRunExact'],
  ['theorem', 'secondRejectingSuffix_workRunExact_of_rawRunExact'],
  ['theorem', 'firstTraceAndLaunch_workRunExact_of_rawRunExact'],
  ['theorem', 'acceptingSequentialTrace_workRunExact_of_rawRunExact'],
  ['theorem', 'rejectingSequentialTrace_workRunExact_of_rawRunExact'],
  ['theorem', 'acceptingSequentialFinal_state_eq_accept'],
  ['theorem', 'rejectingSequentialFinal_state_eq_reject'],
  ['theorem', 'acceptingSequentialFinal_isHalted'],
  ['theorem', 'rejectingSequentialFinal_isHalted'],
  ['theorem', 'sequentialRawSteps_eq_stage_costs'],
  ['theorem', 'sequentialRawSteps_le_sequentialRawTimeBound'],
  ['theorem', 'sequentialRawSteps_le_of_rawRunExact'],
  ['theorem', 'run_sequential_accept_at_bound_of_rawRunExact'],
  ['theorem', 'run_sequential_reject_at_bound_of_rawRunExact'],
  ['theorem', 'sequential_correct'],
  ['theorem', 'sequential_boundedDecide_eq'],
  ['theorem', 'sequential_machineOutput_eq'],
  ['theorem', 'sequential_ne_timeout'],
  ['theorem', 'sequential_accepts_iff'],
  ['theorem', 'firstSimulationPrefix_workBoundedDecide_timeout'],
  ['theorem', 'sequential_timeout_of_stuck_first_rawRunExact'],
  ['def', 'toPolynomialTimeMachine'],
]);

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function heads0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) => [kind, name]);
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.PipelineSequentialStateNamespace',
  ]), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineSequentialCompiler$/mu.test(stripped)
    && /end PipelineSequentialCompiler end PNP\.Concrete$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'proof-shortcut');
  require0(!/\b(?:referenceMinimum|minimization|oracle|SAT|CNFSAT|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'oracle-or-overclaim');
  require0(JSON.stringify(heads0(source)) === JSON.stringify(HEADS),
    'declaration-surface');
  require0(compact.includes(
    'def sequentialMachine (first second : Machine) : Machine := compileWorkMachine (sequentialWorkMachine first second)'),
  'literal-compiled-table');
  require0(compact.includes('PipelineCompiler.pipelineRawTimeBound firstBound')
    && compact.includes('PipelineCompiler.pipelineRawTimeBound secondBound')
    && compact.includes('NatPolynomial.substitute')
    && compact.includes('firstOutputSizeBound firstBound'),
  'external-polynomial-substitution');
  require0((compact.match(/rawRunExact\?_exists_le_run/gu) ?? []).length >= 2,
    'internally-extracted-two-prefixes');
  require0(compact.includes(
    'PipelineMachineSimulation.rawRunExact?_exists_le_run first firstFuel')
    && compact.includes(
      'PipelineMachineSimulation.rawRunExact?_exists_le_run second secondFuel'),
  'correct-machine-prefix-extraction');
  require0(compact.includes('firstFinal.state = first.acceptState ∨')
    && compact.includes('firstFinal.state = first.rejectState')
    && compact.includes('firstAcceptLaunch_workStep')
    && compact.includes('firstRejectLaunch_workStep'),
  'both-first-verdicts-continue');
  require0(compact.includes('secondAcceptingSuffix_workRunExact_of_rawRunExact')
    && compact.includes('secondRejectingSuffix_workRunExact_of_rawRunExact')
    && compact.includes('PipelineTape.Represents (Tape.ofInput input) startWorkTape'),
  'represented-second-input');
  require0(compact.includes('startConfig_compileWorkMachine_blankEquivalent')
    && compact.includes('run_blankEquivalent')
    && compact.includes('Tape.outputBits_eq_of_blankEquivalent'),
  'ordinary-start-and-output');
  require0(compact.includes('theorem sequential_correct')
    && compact.includes('boundedDecide (sequentialMachine first second)')
    && compact.includes('machineOutput (sequentialMachine first second)'),
  'all-input-correctness');
  require0(compact.includes('theorem sequential_timeout_of_stuck_first_rawRunExact')
    && compact.includes('_hNonhalting : first.isHalted final = false')
    && compact.includes('_hStuck : step? first final = none'),
  'stuck-timeout');
  require0(!/FunctionProgram\.RawRefinement|DecisionProgram\.RawRefinement/u.test(stripped),
    'no-refinement-overclaim');
  return failures;
}

test('two-machine compiler is literal, uniform, polynomial, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 31 public declarations exactly once', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  assert.equal(HEADS.length, 31);
  assert.deepEqual(heads0(source), HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), HEADS.map(([, name]) => `${PREFIX}${name}`));
  assert.equal(new Set(printed0(audit)).size, 31);
});

test('root, regression, package, and durable workflow enforce the milestone', async () => {
  const [root, regression, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0(REGRESSION), text0('package.json'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineSequentialCompiler'), true);
  assert.match(regression, /sequential_boundedDecide_eq rejectAllPolynomialTime\s+acceptAllPolynomialTime/u);
  assert.match(regression, /sequential_machineOutput_eq/u);
  assert.match(regression, /sequential_timeout_of_stuck_first_rawRunExact/u);
  assert.match(packageText, /lean-concrete-pipeline-sequential-compiler0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineSequentialCompilerAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcretePipelineSequentialCompiler\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 31/u);
});

test('host composition, verdict suppression, weak bounds, and overclaims fail', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('compileWorkMachine (sequentialWorkMachine first second)', 'second'),
    source.replace('firstRejectLaunch_workStep first second', 'firstAcceptLaunch_workStep first second'),
    source.replaceAll('PipelineCompiler.pipelineRawTimeBound secondBound', 'secondBound'),
    source.replaceAll('NatPolynomial.substitute', 'NatPolynomial.add'),
    source.replace('PipelineMachineSimulation.rawRunExact?_exists_le_run\n      second',
      'PipelineMachineSimulation.rawRunExact?_exists_le_run\n      first'),
    source.replace('_hStuck : step? first final = none', '_hStuck : True'),
    `${source}\naxiom hiddenSequentialOracle : True\n`,
    `${source}\ntheorem cnfSATInP : True := True.intro\n`,
    `${source}\ntheorem fakeRawRefinement : FunctionProgram.RawRefinement := by trivial\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('recursive refinements are earned while publication remains fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcretePipelineSequentialCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineSequentialCompilerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineSequentialCompilerAuditedDeclarationCount, 31);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, true);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
