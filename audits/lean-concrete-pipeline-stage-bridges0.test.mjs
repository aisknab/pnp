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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineStageBridges.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.PipelineStageBridges.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'acceptingHandoffState'],
  ['def', 'rejectingHandoffState'],
  ['theorem', 'acceptingHandoffState_injective'],
  ['theorem', 'rejectingHandoffState_injective'],
  ['theorem', 'acceptingHandoffState_ne_rejectingHandoffState'],
  ['def', 'launchRule'],
  ['def', 'launchRules'],
  ['theorem', 'findWorkRule_launchRules'],
  ['theorem', 'findWorkRule_launchRules_none_of_source_ne'],
  ['theorem', 'findWorkRule_renamedRules_none'],
  ['def', 'inputLaunchRules'],
  ['def', 'acceptingLaunchRules'],
  ['def', 'rejectingLaunchRules'],
  ['def', 'acceptingOutputHandoff'],
  ['def', 'rejectingOutputHandoff'],
  ['def', 'bridgedRules'],
  ['def', 'bridgedMachine'],
  ['def', 'simulationPrefixWorkSteps'],
  ['def', 'bridgedWorkSteps'],
  ['def', 'bridgedRawSteps'],
  ['theorem', 'workRunExact?_transport'],
  ['theorem', 'bridgedMachine_isHalted_input_false'],
  ['theorem', 'bridgedMachine_isHalted_simulation_false'],
  ['theorem', 'bridgedMachine_isHalted_accepting_false_of_local'],
  ['theorem', 'bridgedMachine_isHalted_rejecting_false_of_local'],
  ['theorem', 'findWorkRule_bridged_input_of_some'],
  ['theorem', 'findWorkRule_bridged_simulation_of_some'],
  ['theorem', 'findWorkRule_bridged_acceptingHandoff_of_some'],
  ['theorem', 'findWorkRule_bridged_rejectingHandoff_of_some'],
  ['theorem', 'input_workStep?_of_some'],
  ['theorem', 'simulation_workStep?_of_some'],
  ['theorem', 'acceptingHandoff_workStep?_of_some'],
  ['theorem', 'rejectingHandoff_workStep?_of_some'],
  ['theorem', 'simulationAcceptState_ne_simulationRejectState'],
  ['theorem', 'inputLaunch_workStep'],
  ['theorem', 'acceptingLaunch_workStep'],
  ['theorem', 'rejectingLaunch_workStep'],
  ['theorem', 'input_workRunExact_of_exact'],
  ['theorem', 'simulation_workRunExact_of_exact'],
  ['theorem', 'acceptingHandoff_workRunExact_of_exact'],
  ['theorem', 'rejectingHandoff_workRunExact_of_exact'],
  ['theorem', 'simulationPrefix_workRunExact_of_rawRunExact'],
  ['theorem', 'bridgedAccept_workRunExact_of_rawRunExact'],
  ['theorem', 'bridgedReject_workRunExact_of_rawRunExact'],
  ['theorem', 'acceptingHandoffFinal_state_eq_accept'],
  ['theorem', 'rejectingHandoffFinal_state_eq_reject'],
  ['theorem', 'acceptingHandoffFinal_isHalted'],
  ['theorem', 'rejectingHandoffFinal_isHalted'],
  ['theorem', 'bridgedMachine_acceptState_ne_rejectState'],
  ['theorem', 'bridgedWorkSteps_eq'],
  ['theorem', 'workBoundedDecide_bridged_accept_of_rawRunExact'],
  ['theorem', 'workBoundedDecide_bridged_reject_of_rawRunExact'],
  ['theorem', 'simulationPrefix_workBoundedDecide_timeout'],
  ['theorem', 'workBoundedDecide_bridged_timeout_of_stuck_rawRunExact'],
  ['theorem', 'run_compileBridgedMachine_accept_of_rawRunExact'],
  ['theorem', 'run_compileBridgedMachine_reject_of_rawRunExact'],
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
    'PNP.Concrete.PipelineStateNamespace',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineStageBridges$/mu.test(stripped)
    && /end PipelineStageBridges\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('literal one-step bridges')
    && prose.includes('two verdict-indexed copies')
    && prose.includes('does not pack the two-track work tape')
    && prose.includes('prove a pipeline RawRefinement')
    && prose.includes('supply an external-input-size polynomial')
    && prose.includes('establish CNFSAT in P or NP-completeness')
    && prose.includes('establish P = NP.'), 'explicit-nonclaims');
  require0(!/\b(?:machineOutput_compile|RawRefinement|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'no-output-refinement-or-class-claim');

  require0(compact.includes(
    'def acceptingHandoffState (state : Nat) : Nat := handoffState (inputState state)')
    && compact.includes(
      'def rejectingHandoffState (state : Nat) : Nat := handoffState (simulationState state)'),
  'verdict-indexed-handoff-images');
  require0(compact.includes(
    'writeSymbol := symbol move := .stay'), 'symbol-and-head-preserving-launch');
  require0(compact.includes(
    'def launchRules (source target : Nat) : List WorkRule := PipelineMachineSimulation.allWorkSymbols.map (launchRule source target)'),
  'nine-symbol-launch-table');
  require0(compact.includes(
    'inputLaunchRules machine ++ (acceptingLaunchRules ++ (rejectingLaunchRules ++'),
  'bridge-first-dispatch');
  require0(compact.includes(
    'acceptState := acceptingHandoffState PipelineOutputHandoff.framedOutputHandoff.acceptState')
    && compact.includes(
      'rejectState := rejectingHandoffState PipelineOutputHandoff.framedOutputHandoff.acceptState'),
  'verdict-preserving-global-halts');
  require0(compact.includes('theorem findWorkRule_bridged_input_of_some')
    && compact.includes('theorem findWorkRule_bridged_simulation_of_some')
    && compact.includes('theorem findWorkRule_bridged_acceptingHandoff_of_some')
    && compact.includes('theorem findWorkRule_bridged_rejectingHandoff_of_some'),
  'four-way-first-match-isolation');
  require0(compact.includes('theorem inputLaunch_workStep')
    && compact.includes('theorem acceptingLaunch_workStep')
    && compact.includes('theorem rejectingLaunch_workStep'),
  'three-exact-launches');
  require0(compact.includes(
    'PipelineInputFramer.inputFramerWorkSteps (PipelineInputFramer.packedPairCount left right) + 1 + 3 * sourceSteps + 1 + PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape'),
  'exact-cumulative-work-cost');
  require0(compact.includes(
    'def bridgedRawSteps (left right : BitString) (sourceSteps : Nat) (finalTape : Tape) : Nat := 6 * bridgedWorkSteps left right sourceSteps finalTape'),
  'exact-six-for-one-raw-cost');
  require0(compact.includes('theorem workBoundedDecide_bridged_accept_of_rawRunExact')
    && compact.includes('theorem workBoundedDecide_bridged_reject_of_rawRunExact')
    && compact.includes('theorem workBoundedDecide_bridged_timeout_of_stuck_rawRunExact'),
  'accept-reject-timeout-classification');
  require0(compact.includes('theorem run_compileBridgedMachine_accept_of_rawRunExact')
    && compact.includes('theorem run_compileBridgedMachine_reject_of_rawRunExact'),
  'compiled-canonical-input-traces');

  return failures;
}

test('pipeline stage bridges are finite, exact, verdict-safe, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('pipeline stage bridge axiom transcript covers all 56 public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 56);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 56);
});

test('root, package, and workflow enforce the pipeline stage bridge audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineStageBridges'), true);
  assert.match(packageText, /audits\/lean-concrete-pipeline-stage-bridges0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineStageBridgesAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 56/u);
});

test('bridge audit rejects verdict collapse, missing launches, cost drift, assumptions, and overclaim', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('handoffState (simulationState state)',
      'handoffState (inputState state)'),
    source.replace('writeSymbol := symbol', 'writeSymbol := WorkSymbol.blank'),
    source.replace('acceptingLaunchRules ++', 'rejectingLaunchRules ++'),
    source.replaceAll('1 + 3 * sourceSteps', '2 + 3 * sourceSteps'),
    source.replace('6 * bridgedWorkSteps', '5 * bridgedWorkSteps'),
    `${source}\naxiom hiddenBridgeOracle : True\n`,
    source.replace('pack the two-track work tape',
      'fully packs the two-track work tape'),
    `${source}\ntheorem cnfSATInP : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('bridge remains internal-output-only while the separate terminal stage stays fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcretePipelineStageBridgesFormalized, true);
  assert.equal(status.leanConcretePipelineStageBridgesAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineStageBridgesAuditedDeclarationCount, 56);
  assert.equal(status.leanConcretePipelineStageLaunchFormalized, true);
  assert.equal(status.leanConcretePipelineTerminalOutputPackingFormalized, true);
  assert.equal(status.leanConcretePipelineTerminalOutputPackerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
