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
const SOURCE = 'lean/PNP/Concrete/PipelineSequentialStateNamespace.lean';
const AUDIT = 'lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.PipelineSequentialStateNamespace.';

const HEADS = Object.freeze([
  ['def', 'firstPipelineState'],
  ['def', 'secondPipelineState'],
  ['theorem', 'firstPipelineState_injective'],
  ['theorem', 'secondPipelineState_injective'],
  ['theorem', 'firstPipelineState_ne_secondPipelineState'],
  ['def', 'renamedFirstPipeline'],
  ['def', 'renamedSecondPipeline'],
  ['def', 'firstAcceptLaunchRules'],
  ['def', 'firstRejectLaunchRules'],
  ['def', 'sequentialRules'],
  ['def', 'sequentialWorkMachine'],
  ['theorem', 'sequentialWorkMachine_acceptState_ne_rejectState'],
  ['theorem', 'state_ne_accept_of_isHalted_false'],
  ['theorem', 'state_ne_reject_of_isHalted_false'],
  ['theorem', 'nat_beq_false_of_ne'],
  ['theorem', 'sequentialWorkMachine_isHalted_first_false'],
  ['theorem', 'sequentialWorkMachine_isHalted_second_false_of_local'],
  ['theorem', 'findWorkRule_sequential_first_of_some'],
  ['theorem', 'findWorkRule_sequential_second_of_some'],
  ['theorem', 'first_workStep?_of_some'],
  ['theorem', 'second_workStep?_of_some'],
  ['theorem', 'workRunExact?_transport'],
  ['theorem', 'first_workRunExact_of_exact'],
  ['theorem', 'second_workRunExact_of_exact'],
  ['theorem', 'firstAcceptLaunch_workStep'],
  ['theorem', 'firstRejectLaunch_workStep'],
]);

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function heads0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) => [kind, name]);
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(JSON.stringify(imports0(source)) ===
    JSON.stringify(['PNP.Concrete.PipelineCompiler']), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) &&
    /^namespace PipelineSequentialStateNamespace$/mu.test(stripped) &&
    /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|funext|propext|SAT|CNFSAT|referenceMinimum)\b/u.test(stripped),
    'shortcut');
  require0(JSON.stringify(heads0(source)) === JSON.stringify(HEADS),
    'declaration-surface');
  require0(/def firstPipelineState \(state : Nat\) : Nat := inputState state/u.test(stripped) &&
    /def secondPipelineState \(state : Nat\) : Nat := simulationState state/u.test(stripped),
  'disjoint-outer-images');
  require0(/def sequentialRules[\s\S]*firstAcceptLaunchRules[\s\S]*firstRejectLaunchRules[\s\S]*\.rules\.map \(renameRule firstPipelineState\)[\s\S]*\.rules\.map[\s\S]*renameRule secondPipelineState/u.test(stripped),
    'literal-rule-table');
  require0(/def sequentialWorkMachine[\s\S]*acceptState := secondPipelineState[\s\S]*rejectState := secondPipelineState/u.test(stripped),
    'second-verdict-terminal');
  require0(/acceptState := secondPipelineState\s+\(terminalBridgeMachine second\)\.acceptState\s+rejectState := secondPipelineState\s+\(terminalBridgeMachine second\)\.rejectState/u.test(stripped),
    'distinct-second-terminals');
  require0(/def firstAcceptLaunchRules[\s\S]*def firstRejectLaunchRules/u.test(stripped) &&
    (stripped.match(/liftMachine second\)\.startState/gu) ?? []).length >= 2,
  'both-first-verdicts-launch-second');
  require0(/theorem findWorkRule_sequential_first_of_some/u.test(stripped) &&
    /theorem findWorkRule_sequential_second_of_some/u.test(stripped),
  'lookup-isolation');
  require0(/theorem first_workRunExact_of_exact/u.test(stripped) &&
    /theorem second_workRunExact_of_exact/u.test(stripped), 'trace-transport');
  require0(!/RawRefinement|PolynomialTimeDecider|NPComplete|p_eq_np/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('sequential component namespace is literal, isolated, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers every public declaration exactly once', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(heads0(source), HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), HEADS.map(([, name]) => `${PREFIX}${name}`));
  assert.equal(new Set(printed0(audit)).size, HEADS.length);
  assert.ok(imports0(root).includes('PNP.Concrete.PipelineSequentialStateNamespace'));
});

test('state collision, launch loss, timeout widening, and compiler overclaim mutations fail', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('def secondPipelineState (state : Nat) : Nat := simulationState state',
      'def secondPipelineState (state : Nat) : Nat := inputState state'),
    source.replace('firstRejectLaunchRules first second ++', '[] ++'),
    source.replace('rejectState := secondPipelineState\n      (terminalBridgeMachine second).rejectState',
      'rejectState := secondPipelineState\n      (terminalBridgeMachine second).acceptState'),
    `${source}\ntheorem pipelineRawRefinement := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('machine-link blocker is discharged while publication remains fail-closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), false);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, true);
  assert.equal(map.gate.standardComplexityModelEligible, true);
  assert.equal(map.gate.expectedSourceClosureSha256, null);
});
