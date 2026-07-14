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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineCompiler.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPConcretePipelineCompiler.lean';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'pipelineMachine'],
  ['theorem', 'pipelineMachine_eq_pairedPipelineMachine'],
  ['def', 'simulationPrefixWorkSteps'],
  ['def', 'bridgedWorkSteps'],
  ['def', 'suppliedTraceWorkSteps'],
  ['def', 'suppliedTraceRawSteps'],
  ['def', 'pipelineOutputSizeBound'],
  ['def', 'pipelineRawTimeBound'],
  ['theorem', 'totalInputLaunch_workStep'],
  ['theorem', 'simulationPrefix_workRunExact_of_rawRunExact'],
  ['theorem', 'bridgedAccept_workRunExact_of_rawRunExact'],
  ['theorem', 'bridgedReject_workRunExact_of_rawRunExact'],
  ['theorem', 'acceptingSuppliedTrace_workRunExact_of_rawRunExact'],
  ['theorem', 'rejectingSuppliedTrace_workRunExact_of_rawRunExact'],
  ['theorem', 'pipelineOutputSizeBound_eval'],
  ['theorem', 'suppliedTraceRawSteps_eq_components'],
  ['theorem', 'suppliedTraceRawSteps_le_pipelineRawTimeBound'],
  ['theorem', 'outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact'],
  ['theorem', 'suppliedTraceRawSteps_le_of_rawRunExact'],
  ['theorem', 'run_pipeline_accept_at_bound_of_rawRunExact'],
  ['theorem', 'run_pipeline_reject_at_bound_of_rawRunExact'],
  ['theorem', 'simulationPrefix_workBoundedDecide_timeout'],
  ['theorem', 'pipeline_timeout_of_stuck_rawRunExact'],
  ['theorem', 'pipeline_correct'],
  ['theorem', 'pipeline_boundedDecide_eq'],
  ['theorem', 'pipeline_machineOutput_eq'],
  ['theorem', 'pipeline_ne_timeout'],
  ['theorem', 'pipeline_accepts_iff'],
  ['def', 'toPolynomialTimeMachine'],
]);

const EXPECTED_AXIOM_NAMES = Object.freeze(EXPECTED_HEADS.map(([, name]) =>
  `PNP.Concrete.PipelineCompiler.${name}`));

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function publicHeadPairs0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ kind, name }) => [kind, name]);
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const prose = source.replaceAll('\x60', '').replace(/\s+/gu, ' ');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.PipelinePairedCompiler',
  ]), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineCompiler$/mu.test(stripped)
    && /end PipelineCompiler\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespaces');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-proof-shortcut');
  require0(!/\b(?:referenceMinimum|minimization|certificate|oracle|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'forbidden-oracle-or-claim');
  require0(!/\b(?:decodePair|unpair|SAT|CNFSAT)\b/u.test(stripped),
    'no-host-parser-or-sat');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('PipelineRefinement uses it together with the sequential compiler')
    && prose.includes('close the concrete complexity machine link')
    && prose.includes('CNF-SAT in P')
    && prose.includes('CNF-SAT NP-completeness')
    && prose.includes('PNP.Main.p_eq_np')
    && prose.includes('P = NP')
    && prose.includes('publication gate remains false'), 'explicit-boundary');

  require0(compact.includes(
    'def pipelineMachine (target : Machine) : Machine := compileWorkMachine (terminalBridgeMachine target)'),
  'literal-compiled-machine');
  require0(compact.includes(
    'pipelineMachine target = PipelinePairedCompiler.pairedPipelineMachine target'),
  'same-executable-as-paired');
  require0(compact.includes(
    'def pipelineOutputSizeBound (targetBound : NatPolynomial) : NatPolynomial := .add (.add .variable targetBound) (.constant 1)')
    && compact.includes(
      '(pipelineOutputSizeBound targetBound).eval inputSize = inputSize + targetBound.eval inputSize + 1'),
  'external-output-polynomial');
  require0(compact.includes('PipelineInputFramer.totalInputFramerRawTimeBound')
    && compact.includes('PipelineInputFramer.totalInputFramerRawTimeBound_le input')
    && compact.includes('(.mul (.constant 18) targetBound)')
    && compact.includes('PipelineOutputHandoff.framedOutputHandoffRawTimeBound')
    && compact.includes('terminalBridgeRawTimeBound')
    && (compact.match(/NatPolynomial\.substitute/gu) ?? []).length >= 2,
  'complete-external-runtime-polynomial');
  require0(compact.includes('PipelineInputFramer.totalInputFramer_workRunExact input')
    && compact.includes('PipelineInputFramer.totalInputFramerFinal_represents input')
    && compact.includes('rawInputWorkTape input'), 'all-input-framer-trace');
  require0(compact.includes('startConfig_compileWorkMachine_blankEquivalent')
    && compact.includes('run_blankEquivalent')
    && compact.includes('Tape.outputBits_eq_of_blankEquivalent'),
  'ordinary-start-blank-equivalence');
  require0(compact.includes(
    'PipelineMachineSimulation.rawRunExact?_exists_le_run machine fuel (startConfig machine input)')
    && compact.includes('⟨steps, hSteps, hRaw⟩'),
  'internally-extracted-exact-prefix');
  require0(compact.includes(
    'theorem pipeline_correct (machine : Machine) (targetBound : NatPolynomial) (input : BitString)')
    && compact.includes('hHalts : boundedDecide machine')
    && compact.includes('boundedDecide (pipelineMachine machine)')
    && compact.includes('machineOutput (pipelineMachine machine)'),
  'uniform-verdict-and-output-correctness');
  require0(compact.includes(
    'theorem pipeline_boundedDecide_eq {language : BitString → Prop} (target : PolynomialTimeMachine language) (input : BitString)')
    && compact.includes(
      'theorem pipeline_machineOutput_eq {language : BitString → Prop} (target : PolynomialTimeMachine language) (input : BitString)')
    && compact.includes(
      'theorem pipeline_ne_timeout {language : BitString → Prop} (target : PolynomialTimeMachine language) (input : BitString)')
    && compact.includes(
      'theorem pipeline_accepts_iff {language : BitString → Prop} (target : PolynomialTimeMachine language) (input : BitString)'),
  'proof-bearing-all-input-interface');
  require0(compact.includes('target.haltsWithin input')
    && compact.includes('target.accepts_iff input'), 'compiled-target-evidence');
  require0(compact.includes('theorem pipeline_timeout_of_stuck_rawRunExact')
    && compact.includes('_hNonhalting : machine.isHalted final = false')
    && compact.includes('_hStuck : step? machine final = none'),
  'stuck-remains-timeout');
  require0(!/BitString\.pair/u.test(stripped), 'no-pair-domain-restriction');
  require0(!/FunctionProgram\.RawRefinement|DecisionProgram\.RawRefinement/u.test(stripped),
    'no-general-refinement-claim');

  return failures;
}

test('all-input compiler is literal, uniform, polynomial, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('all-input compiler axiom transcript covers all 29 public declarations', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  assert.equal(EXPECTED_HEADS.length, 29);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), EXPECTED_AXIOM_NAMES);
  assert.equal(new Set(printed0(audit)).size, 29);
});

test('root, regression, package, and workflow enforce the all-input compiler audit', async () => {
  const [root, regression, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0(REGRESSION_PATH), text0('package.json'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineCompiler'), true);
  assert.match(regression, /pipeline_boundedDecide_eq acceptAllPolynomialTime \[\]/u);
  assert.match(regression, /pipeline_boundedDecide_eq rejectAllPolynomialTime \[bit\]/u);
  assert.match(regression, /pipeline_machineOutput_eq acceptAllPolynomialTime input/u);
  assert.match(regression, /pipeline_timeout_of_stuck_rawRunExact/u);
  assert.match(packageText, /audits\/lean-concrete-pipeline-compiler0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineCompilerAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcretePipelineCompiler\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 29/u);
});

test('all-input compiler audit rejects narrowed input, hidden evidence, weak bounds, and overclaims', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('compileWorkMachine (terminalBridgeMachine target)', 'target'),
    source.replaceAll('PipelineInputFramer.totalInputFramerRawTimeBound',
      'PipelineInputFramer.pairedInputFramerRawTimeBound'),
    source.replace('(.mul (.constant 18) targetBound)', '(.mul (.constant 17) targetBound)'),
    source.replace('inputSize + targetBound.eval inputSize + 1',
      'targetBound.eval inputSize'),
    source.replace('PipelineMachineSimulation.rawRunExact?_exists_le_run',
      'PipelineMachineSimulation.rawRunExact?_one_of_step'),
    source.replaceAll('startConfig_compileWorkMachine_blankEquivalent',
      'startConfig_compileWorkMachine_paired'),
    source.replaceAll('target.haltsWithin input', 'Verdict.noConfusion'),
    source.replace('pipeline_machineOutput_eq', 'pipeline_ignoresOutput'),
    source.replace('_hStuck : step? machine final = none',
      '_hStuck : True'),
    `${source}\naxiom hiddenPipelineOracle : True\n`,
    `${source}\ntheorem cnfSATInP : True := True.intro\n`,
    `${source}\ndef decoded := BitString.pair [] []\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('publication remains fail-closed after refinement composition', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcretePipelineCompilerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineCompilerAuditedDeclarationCount, 29);
  assert.equal(status.leanConcretePipelineAllInputCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineMalformedInputBehaviorFormalized, true);
  assert.equal(status.leanConcretePipelineExternalInputSizePolynomialFormalized, true);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, true);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
