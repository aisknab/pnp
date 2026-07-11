import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineMachineSimulation.lean';
const AUDIT_PATH =
  'lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'allWorkSymbols', 'PNP.Concrete.PipelineMachineSimulation.allWorkSymbols'],
  ['def', 'allDataSymbols', 'PNP.Concrete.PipelineMachineSimulation.allDataSymbols'],
  ['def', 'findIndexedRawRuleFrom', 'PNP.Concrete.PipelineMachineSimulation.findIndexedRawRuleFrom'],
  ['def', 'findIndexedRawRule', 'PNP.Concrete.PipelineMachineSimulation.findIndexedRawRule'],
  ['theorem', 'findIndexedRawRuleFrom_map_snd', 'PNP.Concrete.PipelineMachineSimulation.findIndexedRawRuleFrom_map_snd'],
  ['theorem', 'findIndexedRawRule_of_findRule_some', 'PNP.Concrete.PipelineMachineSimulation.findIndexedRawRule_of_findRule_some'],
  ['theorem', 'findIndexedRawRuleFrom_index_ge', 'PNP.Concrete.PipelineMachineSimulation.findIndexedRawRuleFrom_index_ge'],
  ['def', 'interiorRule', 'PNP.Concrete.PipelineMachineSimulation.interiorRule'],
  ['inductive', 'Phase', 'PNP.Concrete.PipelineMachineSimulation.Phase'],
  ['def', 'tagStep', 'PNP.Concrete.PipelineMachineSimulation.tagStep'],
  ['def', 'taggedState', 'PNP.Concrete.PipelineMachineSimulation.taggedState'],
  ['theorem', 'tagStep_injective', 'PNP.Concrete.PipelineMachineSimulation.tagStep_injective'],
  ['theorem', 'taggedState_zero_ne_succ', 'PNP.Concrete.PipelineMachineSimulation.taggedState_zero_ne_succ'],
  ['theorem', 'taggedState_injective', 'PNP.Concrete.PipelineMachineSimulation.taggedState_injective'],
  ['theorem', 'taggedState_ne_of_phase_ne', 'PNP.Concrete.PipelineMachineSimulation.taggedState_ne_of_phase_ne'],
  ['theorem', 'taggedState_ne_of_payload_ne', 'PNP.Concrete.PipelineMachineSimulation.taggedState_ne_of_payload_ne'],
  ['def', 'mainState', 'PNP.Concrete.PipelineMachineSimulation.mainState'],
  ['def', 'stayOneState', 'PNP.Concrete.PipelineMachineSimulation.stayOneState'],
  ['def', 'stayTwoState', 'PNP.Concrete.PipelineMachineSimulation.stayTwoState'],
  ['def', 'inspectLeftState', 'PNP.Concrete.PipelineMachineSimulation.inspectLeftState'],
  ['def', 'finishLeftState', 'PNP.Concrete.PipelineMachineSimulation.finishLeftState'],
  ['def', 'extendLeftState', 'PNP.Concrete.PipelineMachineSimulation.extendLeftState'],
  ['def', 'inspectRightState', 'PNP.Concrete.PipelineMachineSimulation.inspectRightState'],
  ['def', 'finishRightState', 'PNP.Concrete.PipelineMachineSimulation.finishRightState'],
  ['def', 'extendRightState', 'PNP.Concrete.PipelineMachineSimulation.extendRightState'],
  ['def', 'acceptSentinel', 'PNP.Concrete.PipelineMachineSimulation.acceptSentinel'],
  ['def', 'rejectSentinel', 'PNP.Concrete.PipelineMachineSimulation.rejectSentinel'],
  ['theorem', 'mainState_eq', 'PNP.Concrete.PipelineMachineSimulation.mainState_eq'],
  ['theorem', 'stayOneState_eq', 'PNP.Concrete.PipelineMachineSimulation.stayOneState_eq'],
  ['theorem', 'stayTwoState_eq', 'PNP.Concrete.PipelineMachineSimulation.stayTwoState_eq'],
  ['theorem', 'inspectLeftState_eq', 'PNP.Concrete.PipelineMachineSimulation.inspectLeftState_eq'],
  ['theorem', 'finishLeftState_eq', 'PNP.Concrete.PipelineMachineSimulation.finishLeftState_eq'],
  ['theorem', 'extendLeftState_eq', 'PNP.Concrete.PipelineMachineSimulation.extendLeftState_eq'],
  ['theorem', 'inspectRightState_eq', 'PNP.Concrete.PipelineMachineSimulation.inspectRightState_eq'],
  ['theorem', 'finishRightState_eq', 'PNP.Concrete.PipelineMachineSimulation.finishRightState_eq'],
  ['theorem', 'extendRightState_eq', 'PNP.Concrete.PipelineMachineSimulation.extendRightState_eq'],
  ['theorem', 'mainState_injective', 'PNP.Concrete.PipelineMachineSimulation.mainState_injective'],
  ['def', 'controlState', 'PNP.Concrete.PipelineMachineSimulation.controlState'],
  ['theorem', 'controlState_of_nonterminal', 'PNP.Concrete.PipelineMachineSimulation.controlState_of_nonterminal'],
  ['def', 'entryRule', 'PNP.Concrete.PipelineMachineSimulation.entryRule'],
  ['def', 'entryRulesFrom', 'PNP.Concrete.PipelineMachineSimulation.entryRulesFrom'],
  ['def', 'stayOneRule', 'PNP.Concrete.PipelineMachineSimulation.stayOneRule'],
  ['def', 'stayTwoRule', 'PNP.Concrete.PipelineMachineSimulation.stayTwoRule'],
  ['def', 'leftBoundaryRule', 'PNP.Concrete.PipelineMachineSimulation.leftBoundaryRule'],
  ['def', 'rightBoundaryRule', 'PNP.Concrete.PipelineMachineSimulation.rightBoundaryRule'],
  ['def', 'leftExtensionRule', 'PNP.Concrete.PipelineMachineSimulation.leftExtensionRule'],
  ['def', 'rightExtensionRule', 'PNP.Concrete.PipelineMachineSimulation.rightExtensionRule'],
  ['def', 'dataRules', 'PNP.Concrete.PipelineMachineSimulation.dataRules'],
  ['def', 'continuationRulesFor', 'PNP.Concrete.PipelineMachineSimulation.continuationRulesFor'],
  ['def', 'continuationRulesFrom', 'PNP.Concrete.PipelineMachineSimulation.continuationRulesFrom'],
  ['def', 'liftMachine', 'PNP.Concrete.PipelineMachineSimulation.liftMachine'],
  ['def', 'liftConfiguration', 'PNP.Concrete.PipelineMachineSimulation.liftConfiguration'],
  ['def', 'RepresentsConfiguration', 'PNP.Concrete.PipelineMachineSimulation.RepresentsConfiguration'],
  ['theorem', 'machine_not_halted_parts', 'PNP.Concrete.PipelineMachineSimulation.machine_not_halted_parts'],
  ['theorem', 'liftMachine_main_not_halted', 'PNP.Concrete.PipelineMachineSimulation.liftMachine_main_not_halted'],
  ['theorem', 'liftMachine_stage_not_halted', 'PNP.Concrete.PipelineMachineSimulation.liftMachine_stage_not_halted'],
  ['theorem', 'findEntryRulesFrom_of_findIndexedRawRuleFrom', 'PNP.Concrete.PipelineMachineSimulation.findEntryRulesFrom_of_findIndexedRawRuleFrom'],
  ['theorem', 'find_dataRules', 'PNP.Concrete.PipelineMachineSimulation.find_dataRules'],
  ['theorem', 'find_dataRules_none_of_source_ne', 'PNP.Concrete.PipelineMachineSimulation.find_dataRules_none_of_source_ne'],
  ['theorem', 'findWorkRule_append_none_exact', 'PNP.Concrete.PipelineMachineSimulation.findWorkRule_append_none_exact'],
  ['theorem', 'findWorkRule_map_none_of_source_ne', 'PNP.Concrete.PipelineMachineSimulation.findWorkRule_map_none_of_source_ne'],
  ['theorem', 'find_continuationRulesFor_none_of_index_ne', 'PNP.Concrete.PipelineMachineSimulation.find_continuationRulesFor_none_of_index_ne'],
  ['theorem', 'findContinuationRulesFrom_of_findIndexedRawRuleFrom', 'PNP.Concrete.PipelineMachineSimulation.findContinuationRulesFrom_of_findIndexedRawRuleFrom'],
  ['theorem', 'findEntryRulesFrom_none_of_nonmain_phase', 'PNP.Concrete.PipelineMachineSimulation.findEntryRulesFrom_none_of_nonmain_phase'],
  ['theorem', 'findLiftedContinuation_of_findIndexedRawRule', 'PNP.Concrete.PipelineMachineSimulation.findLiftedContinuation_of_findIndexedRawRule'],
  ['theorem', 'find_dataRules_none_of_symbol', 'PNP.Concrete.PipelineMachineSimulation.find_dataRules_none_of_symbol'],
  ['theorem', 'allWorkSymbols_mem', 'PNP.Concrete.PipelineMachineSimulation.allWorkSymbols_mem'],
  ['theorem', 'find_leftExtension_map_of_mem', 'PNP.Concrete.PipelineMachineSimulation.find_leftExtension_map_of_mem'],
  ['theorem', 'find_rightExtension_map_of_mem', 'PNP.Concrete.PipelineMachineSimulation.find_rightExtension_map_of_mem'],
  ['theorem', 'find_continuation_stayOne', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_stayOne'],
  ['theorem', 'find_continuation_stayTwo', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_stayTwo'],
  ['theorem', 'find_continuation_left_inspect', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_left_inspect'],
  ['theorem', 'find_continuation_left_finish', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_left_finish'],
  ['theorem', 'find_continuation_left_boundary', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_left_boundary'],
  ['theorem', 'find_continuation_left_extension', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_left_extension'],
  ['theorem', 'find_continuation_right_inspect', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_right_inspect'],
  ['theorem', 'find_continuation_right_finish', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_right_finish'],
  ['theorem', 'find_continuation_right_boundary', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_right_boundary'],
  ['theorem', 'find_continuation_right_extension', 'PNP.Concrete.PipelineMachineSimulation.find_continuation_right_extension'],
  ['theorem', 'find_liftMachine_entry', 'PNP.Concrete.PipelineMachineSimulation.find_liftMachine_entry'],
  ['theorem', 'workRunExact_three_of_steps', 'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_steps'],
  ['theorem', 'workRunExact_three_of_selected', 'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_selected'],
  ['theorem', 'step?_some_exists', 'PNP.Concrete.PipelineMachineSimulation.step?_some_exists'],
  ['theorem', 'workRunExact_three_of_step', 'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_of_step'],
  ['theorem', 'run_compileWorkMachine_eighteen_of_step', 'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_of_step'],
  ['def', 'rawRunExact?', 'PNP.Concrete.PipelineMachineSimulation.rawRunExact?'],
  ['theorem', 'rawRunExact?_one_of_step', 'PNP.Concrete.PipelineMachineSimulation.rawRunExact?_one_of_step'],
  ['theorem', 'rawRunExact?_compose', 'PNP.Concrete.PipelineMachineSimulation.rawRunExact?_compose'],
  ['theorem', 'run_eq_of_rawRunExact', 'PNP.Concrete.PipelineMachineSimulation.run_eq_of_rawRunExact'],
  ['theorem', 'workRunExact?_compose', 'PNP.Concrete.PipelineMachineSimulation.workRunExact?_compose'],
  ['theorem', 'workRunExact_three_mul_of_rawRunExact', 'PNP.Concrete.PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact'],
  ['theorem', 'run_compileWorkMachine_eighteen_mul_of_rawRunExact', 'PNP.Concrete.PipelineMachineSimulation.run_compileWorkMachine_eighteen_mul_of_rawRunExact'],
]);

const EXPECTED_IMPORTS = Object.freeze([
  'PNP.Concrete.PipelineTapeGeometry',
]);

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

function compactLean0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function headPairs0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ kind, name }) => [kind, name]);
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => {
    if (!condition) failures.push(label);
  };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compactLean0(source);
  const prose = source.replaceAll('\x60', '').replace(/\s+/gu, ' ');

  require0(JSON.stringify(imports0(source)) ===
    JSON.stringify(EXPECTED_IMPORTS), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) &&
    /^namespace PipelineMachineSimulation$/mu.test(stripped) &&
    /end PipelineMachineSimulation\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source),
    'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_HEADS.map(([kind, name]) => [kind, name])),
  'declaration-surface');

  require0(prose.includes(
    'This module does not construct a frame from raw input, prove arbitrary ' +
    'at-most-run or bounded-verdict preservation, decode or hand off output, ' +
    'provide a pipeline refinement or end-to-end input-size polynomial bound, ' +
    'establish a complexity-class equality, or prove P = NP.'),
  'explicit-nonclaims');
  require0(!/\b(?:RawRefinement|outputBits|handoffTarget|boundedDecide|NatPolynomial|PolynomialTimeMachine|PolynomialTimeDecider|FunctionProgram|DecisionProgram)\b/u
    .test(stripped), 'no-broader-pipeline-claim');

  require0(compact.includes(
    'def allWorkSymbols : List WorkSymbol := [WorkSymbol.blank, ' +
    'WorkSymbol.blankZero, WorkSymbol.blankOne, WorkSymbol.zeroBlank, ' +
    'WorkSymbol.zeroZero, WorkSymbol.zeroOne, WorkSymbol.oneBlank, ' +
    'WorkSymbol.oneZero, WorkSymbol.oneOne]'),
  'all-nine-work-symbols');
  require0(compact.includes(
    'allWorkSymbols.map (leftExtensionRule machine index rule)') &&
    compact.includes(
      'allWorkSymbols.map (rightExtensionRule machine index rule)'),
  'arbitrary-exterior-rules');
  require0(compact.includes(
    'if rule.sourceState == state && rule.readSymbol == symbol then ' +
    'some (index, rule) else findIndexedRawRuleFrom rest state symbol ' +
    '(index + 1)'),
  'indexed-first-match');
  require0(compact.includes(
    'Option.map Prod.snd (findIndexedRawRuleFrom rules state symbol index) = ' +
    'findRule rules state symbol'),
  'first-match-correspondence');
  require0(compact.includes(
    'if rule.sourceState = machine.acceptState ∨ rule.sourceState = ' +
    'machine.rejectState then entryRulesFrom machine rest (index + 1) else ' +
    'entryRule index rule :: entryRulesFrom machine rest (index + 1)'),
  'terminal-entry-suppression');
  require0(compact.includes(
    'rules := entryRulesFrom machine machine.rules 0 ++ ' +
    'continuationRulesFrom machine machine.rules 0'),
  'entry-before-continuation-order');
  require0(compact.includes(
    'findWorkRule (entryRulesFrom machine rules start) (mainState state) ' +
    '(dataSymbol symbol) = some (entryRule index rule)'),
  'entry-selection-proof');
  require0(compact.includes(
    'findContinuationRulesFrom_of_findIndexedRawRuleFrom') &&
    compact.includes('find_continuationRulesFor_none_of_index_ne'),
  'continuation-index-isolation');

  require0(compact.includes(
    'def acceptSentinel : Nat := taggedState 0 .accept') &&
    compact.includes(
      'def rejectSentinel : Nat := taggedState 0 .reject') &&
    compact.includes(
      'if state = machine.acceptState then acceptSentinel else if state = ' +
      'machine.rejectState then rejectSentinel else mainState state'),
  'fresh-terminal-sentinels');
  require0(compact.includes(
    'workRunExact? (liftMachine machine) 3 ' +
    '(liftConfiguration machine config workTape) = some final ∧ ' +
    'RepresentsConfiguration machine next final'),
  'exact-three-successful-step');
  require0(compact.includes(
    'run (compileWorkMachine (liftMachine machine)) 18 ' +
    '(encodeWorkConfiguration (liftConfiguration machine config workTape)) = ' +
    'encodeWorkConfiguration final ∧ RepresentsConfiguration machine next final'),
  'eighteen-fuel-compiled-step');
  require0(compact.includes(
    'run_compileWorkMachine_mul_of_workRunExact (liftMachine machine) 3'),
  'literal-compiler-composition');
  require0(compact.includes(
    '(hStep : step? machine config = some next)') &&
    compact.includes(
      '(hRepresents : Represents config.tape workTape)'),
  'successful-step-and-frame-premises');
  require0(compact.includes(
    'def rawRunExact? (machine : Machine) : Nat → Configuration → ' +
    'Option Configuration | 0, config => some config | steps + 1, config => ' +
    'match step? machine config with | none => none | some next => ' +
    'rawRunExact? machine steps next'),
  'exact-raw-run-stops-on-failure');
  require0(compact.includes(
    'theorem rawRunExact?_one_of_step (machine : Machine) ' +
    '(config next : Configuration) (hStep : step? machine config = ' +
    'some next) : rawRunExact? machine 1 config = some next := by'),
  'exact-raw-run-one-type');
  require0(compact.includes(
    'theorem rawRunExact?_compose (machine : Machine) ' +
    '(first second : Nat) (start middle final : Configuration) ' +
    '(hFirst : rawRunExact? machine first start = some middle) ' +
    '(hSecond : rawRunExact? machine second middle = some final) : ' +
    'rawRunExact? machine (first + second) start = some final := by'),
  'exact-raw-run-compose-type');
  require0(compact.includes(
    'theorem run_eq_of_rawRunExact (machine : Machine) (steps : Nat) ' +
    '(start final : Configuration) (hExact : rawRunExact? machine steps ' +
    'start = some final) : run machine steps start = final := by'),
  'exact-run-agreement-type');
  require0(compact.includes(
    'theorem workRunExact?_compose (machine : WorkMachine) ' +
    '(first second : Nat) (start middle final : WorkConfiguration) ' +
    '(hFirst : workRunExact? machine first start = some middle) ' +
    '(hSecond : workRunExact? machine second middle = some final) : ' +
    'workRunExact? machine (first + second) start = some final := by'),
  'exact-work-run-compose-type');
  require0(compact.includes(
    'workRunExact? (liftMachine machine) (3 * steps) ' +
    '(liftConfiguration machine config workTape) = some workFinal ∧ ' +
    'RepresentsConfiguration machine final workFinal'),
  'exact-three-mul-successful-run');
  require0(compact.includes(
    'run (compileWorkMachine (liftMachine machine)) (18 * steps) ' +
    '(encodeWorkConfiguration (liftConfiguration machine config workTape)) = ' +
    'encodeWorkConfiguration workFinal ∧ RepresentsConfiguration machine ' +
    'final workFinal'),
  'eighteen-mul-fuel-compiled-run');
  require0(compact.includes(
    'theorem workRunExact_three_mul_of_rawRunExact (machine : Machine) ' +
    '(steps : Nat) (config final : Configuration) (workTape : WorkTape) ' +
    '(hRaw : rawRunExact? machine steps config = some final) ' +
    '(hRepresents : Represents config.tape workTape) : ∃ workFinal,') &&
    compact.includes(
      'theorem run_compileWorkMachine_eighteen_mul_of_rawRunExact ' +
      '(machine : Machine) (steps : Nat) (config final : Configuration) ' +
      '(workTape : WorkTape) (hRaw : rawRunExact? machine steps config = ' +
      'some final) (hRepresents : Represents config.tape workTape) : ' +
      '∃ workFinal,') && compact.includes(
        'run_eq_of_rawRunExact (machine : Machine) (steps : Nat)'),
  'successful-exact-run-and-frame-premises');
  require0(!/rawRunExact\? machine steps config = none →/u.test(compact),
    'no-failed-run-promotion');

  for (const branch of [
    'find_continuation_stayOne',
    'find_continuation_stayTwo',
    'find_continuation_left_inspect',
    'find_continuation_left_finish',
    'find_continuation_left_boundary',
    'find_continuation_left_extension',
    'find_continuation_right_inspect',
    'find_continuation_right_finish',
    'find_continuation_right_boundary',
    'find_continuation_right_extension',
  ]) {
    require0((compact.match(new RegExp(branch, 'gu')) ?? []).length >= 2,
      'branch-used:' + branch);
  }

  return failures;
}

test('pipeline machine simulator is finite, exact, first-match, and shortcut-free',
    async () => {
      assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
    });

test('root, transcript, and workflow require all ninety-two axiom-free declarations',
    async () => {
      const [source, audit, root, workflow] = await Promise.all([
        text0(SOURCE_PATH),
        text0(AUDIT_PATH),
        text0('lean/PNP.lean'),
        text0('.github/workflows/lean-bridge.yml'),
      ]);
      assert.equal(EXPECTED_HEADS.length, 92);
      assert.deepEqual(headPairs0(source),
        EXPECTED_HEADS.map(([kind, name]) => [kind, name]));
      assert.deepEqual(imports0(audit), ['PNP']);
      assert.deepEqual(printed0(audit),
        EXPECTED_HEADS.map(([, , full]) => full));
      assert.equal(new Set(printed0(audit)).size, EXPECTED_HEADS.length);
      const rootImports = imports0(root);
      const importIndex =
        rootImports.indexOf('PNP.Concrete.PipelineMachineSimulation');
      assert.notEqual(importIndex, -1);
      assert.equal(rootImports.lastIndexOf(
        'PNP.Concrete.PipelineMachineSimulation'), importIndex);
      assert.equal(rootImports[importIndex - 1],
        'PNP.Concrete.PipelineTapeGeometry');
      assert.match(workflow,
        /PNPConcretePipelineMachineSimulationAxiomAudit\.lean[\s\S]{0,900}grep -F 'depends on axioms:'[\s\S]{0,400}exit 1[\s\S]{0,400}grep -Fc 'does not depend on any axioms'\)" -eq 92/u);
    });

test('hostile rule-order, terminal, alphabet, cost, namespace, and proof mutations fail',
    async () => {
      const source = await text0(SOURCE_PATH);
      const mutations = [
        source.replace('import PNP.Concrete.PipelineTapeGeometry',
          'import PNP.Concrete.PipelineTapeGeometry\n' +
          'import Lean.Elab.Tactic.Omega'),
        source.replace('PNP.Concrete.PipelineTapeGeometry',
          'PNP.Concrete.WorkMachine'),
        source.replace('rule.sourceState == state && rule.readSymbol == symbol',
          'rule.sourceState == state || rule.readSymbol == symbol'),
        source.replace(
          'findIndexedRawRuleFrom rest state symbol (index + 1)',
          'findIndexedRawRuleFrom rest state symbol index'),
        source.replace(
          'then\n        entryRulesFrom machine rest (index + 1)',
          'then\n        entryRule index rule :: ' +
          'entryRulesFrom machine rest (index + 1)'),
        source.replace('WorkSymbol.oneOne]', 'WorkSymbol.oneZero]'),
        source.replace('taggedState 0 .accept', 'mainState 0'),
        source.replaceAll(
          'workRunExact? (liftMachine machine) 3',
          'workRunExact? (liftMachine machine) 2'),
        source.replace(
          'run (compileWorkMachine (liftMachine machine)) 18',
          'run (compileWorkMachine (liftMachine machine)) 17'),
        source.replace(
          'workRunExact? (liftMachine machine) (3 * steps)',
          'workRunExact? (liftMachine machine) (2 * steps)'),
        source.replace(
          'run (compileWorkMachine (liftMachine machine)) (18 * steps)',
          'run (compileWorkMachine (liftMachine machine)) (17 * steps)'),
        source.replace(
          '| none => none\n      | some next => rawRunExact? machine steps next',
          '| none => some config\n      | some next => rawRunExact? machine steps next'),
        source.replace(
          'rawRunExact? machine 1 config = some next := by',
          'True := by'),
        source.replace(
          'rawRunExact? machine (first + second) start = some final := by',
          'True := by'),
        source.replace(
          'run machine steps start = final := by',
          'True := by'),
        source.replace(
          'workRunExact? machine (first + second) start = some final := by',
          'True := by'),
        source.replace(
          '(hRaw : rawRunExact? machine steps config = some final)\n' +
          '    (hRepresents : Represents config.tape workTape)',
          '(hRaw : run machine steps config = final)\n' +
          '    (_ : True)'),
        source.replace(
          'RepresentsConfiguration machine final workFinal := by\n' +
          '  induction steps',
          'RepresentsConfiguration machine config workFinal := by\n' +
          '  induction steps'),
        source.replace('at-most-run or bounded-verdict preservation, ', ''),
        source.replace(':= rfl', ':= by sorry'),
        source.replace(':= rfl', ':= by native_decide'),
        source + '\naxiom hiddenPipelineSimulation : True\n',
        source + '\nprivate theorem hiddenPipelineSimulation : True := True.intro\n',
        source + '\nunsafe def hiddenPipelineSimulation : Nat := 0\n',
        source + '\ndef extraPipelineSimulation : Nat := 0\n',
      ];
      for (const [index, mutated] of mutations.entries()) {
        assert.notEqual(mutated, source,
          'mutation ' + index + ' must change the source');
        assert.notDeepEqual(validate0(mutated), [],
          'mutation ' + index + ' must be rejected');
      }
    });

test('transcript deletion, duplication, and root displacement fail closed',
    async () => {
      const [audit, root] = await Promise.all([
        text0(AUDIT_PATH),
        text0('lean/PNP.lean'),
      ]);
      const expected = EXPECTED_HEADS.map(([, , full]) => full);
      assert.notDeepEqual(printed0(audit).slice(0, -1), expected);
      assert.notDeepEqual(printed0(audit + '\n' +
        '#print axioms ' + expected[0] + '\n'), expected);
      const displaced = root.replace(
        'import PNP.Concrete.PipelineTapeGeometry\n' +
        'import PNP.Concrete.PipelineMachineSimulation',
        'import PNP.Concrete.PipelineMachineSimulation\n' +
        'import PNP.Concrete.PipelineTapeGeometry');
      const displacedImports = imports0(displaced);
      const displacedIndex = displacedImports.indexOf(
        'PNP.Concrete.PipelineMachineSimulation');
      assert.notEqual(displacedImports[displacedIndex - 1],
        'PNP.Concrete.PipelineTapeGeometry');
    });
