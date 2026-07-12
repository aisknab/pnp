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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineStateNamespace.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.PipelineStateNamespace.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'renameRule'],
  ['def', 'renameConfiguration'],
  ['def', 'renameMachine'],
  ['theorem', 'findWorkRule_rename'],
  ['theorem', 'renameMachine_isHalted'],
  ['theorem', 'applyWorkRule_rename'],
  ['theorem', 'workStep?_rename'],
  ['theorem', 'workRun_rename'],
  ['theorem', 'workRunExact?_rename'],
  ['theorem', 'workStartConfiguration_rename'],
  ['theorem', 'workBoundedDecide_rename'],
  ['inductive', 'Stage'],
  ['def', 'stageStep'],
  ['def', 'stageState'],
  ['theorem', 'stageStep_injective'],
  ['theorem', 'stageState_zero_ne_succ'],
  ['theorem', 'stageState_injective'],
  ['theorem', 'stageState_ne_of_stage_ne'],
  ['def', 'inputState'],
  ['def', 'simulationState'],
  ['def', 'handoffState'],
  ['theorem', 'inputState_injective'],
  ['theorem', 'simulationState_injective'],
  ['theorem', 'handoffState_injective'],
  ['theorem', 'inputState_ne_simulationState'],
  ['theorem', 'inputState_ne_handoffState'],
  ['theorem', 'simulationState_ne_handoffState'],
  ['def', 'stageRules'],
  ['def', 'composedRules'],
  ['theorem', 'findWorkRule_stageRules_none_of_stage_ne'],
  ['theorem', 'findWorkRule_composedRules_input'],
  ['theorem', 'findWorkRule_composedRules_simulation'],
  ['theorem', 'findWorkRule_composedRules_handoff'],
  ['def', 'renamedInputFramer'],
  ['def', 'renamedLiftMachine'],
  ['def', 'renamedOutputHandoff'],
  ['theorem', 'renamedInputFramer_workRunExact'],
  ['theorem', 'renamedLiftMachine_workRunExact_of_rawRunExact'],
  ['theorem', 'renamedOutputHandoff_workRunExact_of_represents'],
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
    'PNP.Concrete.PipelineInputFramer',
    'PNP.Concrete.PipelineMachineSimulation',
    'PNP.Concrete.PipelineOutputHandoff',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineStateNamespace$/mu.test(stripped)
    && /end PipelineStateNamespace\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('This is a composition prerequisite, not an end-to-end pipeline compiler.')
    && prose.includes('does not connect a framer halt to a simulator start')
    && prose.includes('connect simulator halts to the handoff machine')
    && prose.includes('construct terminal raw output')
    && prose.includes('prove a pipeline RawRefinement')
    && prose.includes('establish an external input-size polynomial')
    && prose.includes('prove CNFSAT in P or NP-completeness')
    && prose.includes('establish P = NP.'),
  'explicit-nonclaims');
  require0(!/\b(?:bridgeRules|launchSimulator|terminalPacker|machineOutput|RawRefinement|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'no-stage-launch-output-or-class-claim');

  require0(compact.includes(
    'def renameRule (encode : Nat → Nat) (rule : WorkRule) : WorkRule := { sourceState := encode rule.sourceState readSymbol := rule.readSymbol targetState := encode rule.targetState writeSymbol := rule.writeSymbol move := rule.move }'),
  'rule-endpoint-renaming');
  require0(compact.includes(
    'def renameMachine (encode : Nat → Nat) (machine : WorkMachine) : WorkMachine := { rules := machine.rules.map (renameRule encode) startState := encode machine.startState acceptState := encode machine.acceptState rejectState := encode machine.rejectState }'),
  'machine-state-renaming');
  require0(compact.includes(
    'findWorkRule (rules.map (renameRule encode)) (encode state) symbol = Option.map (renameRule encode) (findWorkRule rules state symbol)'),
  'first-match-renaming');
  require0(compact.includes(
    'workStep? (renameMachine encode machine) (renameConfiguration encode config) = Option.map (renameConfiguration encode) (workStep? machine config)'),
  'step-renaming');
  require0(compact.includes(
    'workRunExact? (renameMachine encode machine) steps (renameConfiguration encode config) = Option.map (renameConfiguration encode) (workRunExact? machine steps config)'),
  'exact-run-renaming');
  require0(compact.includes(
    'workBoundedDecide (renameMachine encode machine) fuel tape = workBoundedDecide machine fuel tape'),
  'verdict-renaming');

  require0(compact.includes('inductive Stage where | input | simulation | handoff'),
    'three-stage-enumeration');
  require0(compact.includes(
    '| payload + 1, stage => stageStep (stageState payload stage)'),
  'recursive-stage-state');
  require0(compact.includes(
    'leftPayload = rightPayload ∧ leftStage = rightStage'),
  'stage-payload-injectivity');
  require0(compact.includes(
    'stageState leftPayload leftStage ≠ stageState rightPayload rightStage'),
  'stage-image-disjointness');
  require0(compact.includes(
    'def inputState (state : Nat) : Nat := stageState state .input')
    && compact.includes(
      'def simulationState (state : Nat) : Nat := stageState state .simulation')
    && compact.includes(
      'def handoffState (state : Nat) : Nat := stageState state .handoff'),
  'exact-stage-images');
  require0(compact.includes(
    'def composedRules (input simulation handoff : WorkMachine) : List WorkRule := stageRules .input input.rules ++ (stageRules .simulation simulation.rules ++ stageRules .handoff handoff.rules)'),
  'literal-rule-table-composition');
  require0(compact.includes('theorem findWorkRule_composedRules_input')
    && compact.includes('theorem findWorkRule_composedRules_simulation')
    && compact.includes('theorem findWorkRule_composedRules_handoff'),
  'three-way-lookup-isolation');
  require0(compact.includes(
    'def renamedInputFramer : WorkMachine := renameMachine inputState PipelineInputFramer.pairedInputFramer')
    && compact.includes(
      'def renamedLiftMachine (machine : Machine) : WorkMachine := renameMachine simulationState (PipelineMachineSimulation.liftMachine machine)')
    && compact.includes(
      'def renamedOutputHandoff : WorkMachine := renameMachine handoffState PipelineOutputHandoff.framedOutputHandoff'),
  'three-renamed-machines');
  require0(compact.includes('theorem renamedInputFramer_workRunExact')
    && compact.includes('theorem renamedLiftMachine_workRunExact_of_rawRunExact')
    && compact.includes('theorem renamedOutputHandoff_workRunExact_of_represents'),
  'existing-exact-traces-transported');

  return failures;
}

test('pipeline state namespace is closed, collision-free, exact, and shortcut-free', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validate0(source), []);
});

test('pipeline state namespace axiom transcript covers all 39 public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 39);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 39);
});

test('root, package, and workflow enforce the pipeline state namespace audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineStateNamespace'), true);
  assert.match(packageText, /audits\/lean-concrete-pipeline-state-namespace0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineStateNamespaceAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 39/u);
});

test('pipeline state namespace audit rejects collisions, dropped stages, broadened claims, and assumptions', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('targetState := encode rule.targetState',
      'targetState := rule.targetState'),
    source.replace('def simulationState (state : Nat) : Nat := stageState state .simulation',
      'def simulationState (state : Nat) : Nat := stageState state .input'),
    source.replace('stageRules .handoff handoff.rules)',
      '[])'),
    source.replace('stageRules .input input.rules ++\n    (stageRules .simulation simulation.rules ++',
      'stageRules .simulation simulation.rules ++\n    (stageRules .input input.rules ++'),
    `${source}\naxiom hiddenStateCollision : True\n`,
    source.replace(
      'This is a composition prerequisite, not an end-to-end pipeline compiler.',
      'This is an end-to-end pipeline compiler.'),
    `${source}\ntheorem cnfSATInP : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('namespace remains the prerequisite while the separate bridge milestone stays fail-closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.equal(status.leanConcretePipelineStateNamespaceFormalized, true);
  assert.equal(status.leanConcretePipelineStateNamespaceAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineStateNamespaceAuditedDeclarationCount, 39);
  assert.equal(status.leanConcretePipelineRuleTableCompositionFormalized, true);
  assert.equal(status.leanConcretePipelineStageLaunchFormalized, true);
  assert.equal(status.leanConcretePipelineStageBridgesFormalized, true);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), true);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const foundation = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  for (const name of [
    `${PREFIX}findWorkRule_rename`,
    `${PREFIX}workRunExact?_rename`,
    `${PREFIX}workBoundedDecide_rename`,
    `${PREFIX}stageState_injective`,
    `${PREFIX}findWorkRule_composedRules_input`,
    `${PREFIX}findWorkRule_composedRules_simulation`,
    `${PREFIX}findWorkRule_composedRules_handoff`,
    `${PREFIX}renamedInputFramer_workRunExact`,
    `${PREFIX}renamedLiftMachine_workRunExact_of_rawRunExact`,
    `${PREFIX}renamedOutputHandoff_workRunExact_of_represents`,
  ]) assert.equal(foundation.requiredTheorems.includes(name), true, name);
  assert.match(foundation.scope, /symbol-preserving one-step framer-to-simulator launch/u);
  assert.match(foundation.scope, /two disjoint verdict-indexed handoff copies/u);
  assert.match(foundation.scope, /first-match isolation/u);
  assert.match(foundation.nonClaim, /no terminal raw output packer/u);
  assert.match(foundation.nonClaim, /no complete FunctionProgram.RawRefinement/u);
  assert.equal(map.gate.standardComplexityModelEligible, false);
});
