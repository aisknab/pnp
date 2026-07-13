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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelinePairedCompiler.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelinePairedCompilerAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPConcretePipelinePairedCompiler.lean';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'outputWindowSize'],
  ['theorem', 'decodeOutputCells_length_le'],
  ['theorem', 'outputBits_length_le_outputWindowSize'],
  ['theorem', 'outputWindowSize_ofInput_le'],
  ['theorem', 'outputWindowSize_write'],
  ['theorem', 'outputWindowSize_moveLeft'],
  ['theorem', 'outputWindowSize_moveRight_le'],
  ['theorem', 'outputWindowSize_move_le'],
  ['def', 'pairedPipelineMachine'],
  ['def', 'pairedPipelineOutputSizeBound'],
  ['def', 'pairedPipelineRawTimeBound'],
  ['theorem', 'framedOutputHandoffRawTimeBound_exact'],
  ['theorem', 'suppliedTraceTerminalRawSteps_eq_components'],
  ['theorem', 'pairedPipelineOutputSizeBound_eval'],
  ['theorem', 'suppliedTraceTerminalRawSteps_le_pairedPipelineRawTimeBound'],
  ['theorem', 'outputWindowSize_applyRule_le'],
  ['theorem', 'outputWindowSize_step_le'],
  ['theorem', 'outputWindowSize_run_le'],
  ['theorem', 'machineOutput_length_le_input_add_fuel'],
  ['theorem', 'outputBits_length_le_pairedPipelineOutputSizeBound_of_rawRunExact'],
  ['theorem', 'suppliedTraceTerminalRawSteps_le_of_rawRunExact'],
  ['theorem', 'run_pairedPipeline_accept_at_bound_of_rawRunExact'],
  ['theorem', 'run_pairedPipeline_reject_at_bound_of_rawRunExact'],
  ['theorem', 'pairedPipeline_correct_on_pair'],
  ['theorem', 'pairedPipeline_boundedDecide_eq'],
  ['theorem', 'pairedPipeline_machineOutput_eq'],
  ['theorem', 'pairedPipeline_ne_timeout'],
  ['theorem', 'pairedPipeline_accepts_iff'],
]);

const EXPECTED_AXIOM_NAMES = Object.freeze(EXPECTED_HEADS.map(([, name], index) => (
  index < 8
    ? `PNP.Concrete.Tape.${name}`
    : `PNP.Concrete.PipelinePairedCompiler.${name}`
)));

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
    'PNP.Concrete.PipelineTerminalBridge',
  ]), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace Tape$/mu.test(stripped)
    && /^namespace PipelinePairedCompiler$/mu.test(stripped)
    && /end PipelinePairedCompiler\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespaces');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-proof-shortcut');
  require0(!/\b(?:referenceMinimum|minimization|certificate|oracle|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'forbidden-oracle-or-claim');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('only for canonical BitString.pair inputs')
    && prose.includes('does not yet provide malformed-input behavior')
    && prose.includes('all-bitstring RawRefinement')
    && prose.includes('CNF-SAT in P')
    && prose.includes('CNF-SAT NP-completeness')
    && prose.includes('P = NP.'), 'explicit-boundary');

  require0(compact.includes(
    'def pairedPipelineMachine (target : Machine) : Machine := compileWorkMachine (terminalBridgeMachine target)'),
  'literal-compiled-machine');
  require0(compact.includes(
    'def pairedPipelineOutputSizeBound (targetBound : NatPolynomial) : NatPolynomial := .add (.add .variable targetBound) (.constant 1)')
    && compact.includes(
      '(pairedPipelineOutputSizeBound targetBound).eval inputSize = inputSize + targetBound.eval inputSize + 1'),
  'external-output-polynomial');
  require0(compact.includes('PipelineInputFramer.pairedInputFramerRawTimeBound')
    && compact.includes('(.mul (.constant 18) targetBound)')
    && compact.includes('PipelineOutputHandoff.framedOutputHandoffRawTimeBound')
    && compact.includes('terminalBridgeRawTimeBound')
    && (compact.match(/NatPolynomial\.substitute/gu) ?? []).length >= 2,
  'complete-external-runtime-polynomial');
  require0(compact.includes(
    'theorem machineOutput_length_le_input_add_fuel (machine : Machine) (fuel : Nat) (input : BitString)')
    && compact.includes(
      '(machineOutput machine fuel input).length ≤ input.length + fuel + 1'),
  'uniform-output-growth');
  require0(compact.includes(
    'PipelineMachineSimulation.rawRunExact?_exists_le_run machine fuel (startConfig machine input)')
    && compact.includes('⟨steps, hSteps, hRaw⟩'),
  'internally-extracted-exact-prefix');
  require0(compact.includes(
    'theorem pairedPipeline_correct_on_pair (machine : Machine) (targetBound : NatPolynomial) (left right : BitString)')
    && compact.includes('hHalts : boundedDecide machine')
    && compact.includes('boundedDecide (pairedPipelineMachine machine)')
    && compact.includes('machineOutput (pairedPipelineMachine machine)'),
  'uniform-verdict-and-output-correctness');
  require0(compact.includes(
    'theorem pairedPipeline_boundedDecide_eq {language : BitString → Prop} (target : PolynomialTimeMachine language) (left right : BitString)')
    && compact.includes(
      'theorem pairedPipeline_machineOutput_eq {language : BitString → Prop} (target : PolynomialTimeMachine language) (left right : BitString)')
    && compact.includes(
      'theorem pairedPipeline_ne_timeout {language : BitString → Prop} (target : PolynomialTimeMachine language) (left right : BitString)')
    && compact.includes(
      'theorem pairedPipeline_accepts_iff {language : BitString → Prop} (target : PolynomialTimeMachine language) (left right : BitString)'),
  'proof-bearing-target-interface');
  require0(compact.includes('target.haltsWithin (BitString.pair left right)')
    && compact.includes('target.accepts_iff (BitString.pair left right)'),
  'compiled-target-evidence');
  require0(!/FunctionProgram\.RawRefinement|DecisionProgram\.RawRefinement/u.test(stripped),
    'no-general-refinement-claim');

  return failures;
}

test('paired compiler is literal, uniform on canonical pairs, polynomial, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('paired compiler axiom transcript covers all 28 public declarations', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  assert.equal(EXPECTED_HEADS.length, 28);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), EXPECTED_AXIOM_NAMES);
  assert.equal(new Set(printed0(audit)).size, 28);
});

test('root, regression, package, and workflow enforce the paired compiler audit', async () => {
  const [root, regression, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0(REGRESSION_PATH), text0('package.json'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelinePairedCompiler'), true);
  assert.match(regression, /pairedPipeline_boundedDecide_eq acceptAllPolynomialTime/u);
  assert.match(regression, /pairedPipeline_boundedDecide_eq rejectAllPolynomialTime/u);
  assert.match(regression, /pairedPipeline_machineOutput_eq acceptAllPolynomialTime/u);
  assert.match(packageText, /audits\/lean-concrete-pipeline-paired-compiler0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelinePairedCompilerAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcretePipelinePairedCompiler\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 28/u);
});

test('paired compiler audit rejects dropped stages, hidden evidence, weak bounds, and overclaims', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('compileWorkMachine (terminalBridgeMachine target)', 'target'),
    source.replace('(.mul (.constant 18) targetBound)', '(.mul (.constant 17) targetBound)'),
    source.replace('inputSize + targetBound.eval inputSize + 1', 'targetBound.eval inputSize'),
    source.replace('PipelineMachineSimulation.rawRunExact?_exists_le_run',
      'PipelineMachineSimulation.rawRunExact?_one_of_step'),
    source.replaceAll('target.haltsWithin (BitString.pair left right)',
      'Verdict.noConfusion'),
    source.replace('pairedPipeline_machineOutput_eq', 'pairedPipeline_ignoresOutput'),
    `${source}\naxiom hiddenPairedCompilerOracle : True\n`,
    `${source}\ntheorem cnfSATInP : True := True.intro\n`,
    source.replace('only for canonical', 'for every raw'),
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('paired compiler remains exact while its all-input successor stays fail-closed at refinement', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcretePipelinePairedCompilerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelinePairedCompilerAuditedDeclarationCount, 28);
  assert.equal(status.leanConcretePipelineCanonicalPairCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineCompilerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineCompilerAuditedDeclarationCount, 29);
  assert.equal(status.leanConcretePipelineAllInputCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineExternalInputSizePolynomialFormalized, true);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, false);
  assert.equal(status.leanConcretePipelineMalformedInputBehaviorFormalized, true);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
