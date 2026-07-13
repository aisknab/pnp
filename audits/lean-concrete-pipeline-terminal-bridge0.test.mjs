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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineTerminalBridge.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.PipelineTerminalBridge.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'acceptingPackerState'],
  ['def', 'rejectingPackerState'],
  ['theorem', 'acceptingPackerState_injective'],
  ['theorem', 'rejectingPackerState_injective'],
  ['theorem', 'acceptingPackerState_ne_rejectingPackerState'],
  ['theorem', 'acceptingHandoffState_ne_acceptingPackerState'],
  ['theorem', 'acceptingHandoffState_ne_rejectingPackerState'],
  ['theorem', 'rejectingHandoffState_ne_acceptingPackerState'],
  ['theorem', 'rejectingHandoffState_ne_rejectingPackerState'],
  ['def', 'acceptingPackerLaunchRules'],
  ['def', 'rejectingPackerLaunchRules'],
  ['def', 'terminalBridgeRules'],
  ['def', 'terminalBridgeMachine'],
  ['def', 'terminalBridgeWorkSteps'],
  ['def', 'terminalBridgeRawSteps'],
  ['def', 'terminalBridgeRawTimeBound'],
  ['theorem', 'terminalBridge_runtime_le'],
  ['theorem', 'findWorkRule_terminalBridge_acceptingPacker_of_some'],
  ['theorem', 'findWorkRule_terminalBridge_rejectingPacker_of_some'],
  ['theorem', 'terminalBridgeMachine_isHalted_acceptingHandoff_false'],
  ['theorem', 'terminalBridgeMachine_isHalted_rejectingHandoff_false'],
  ['theorem', 'terminalBridgeMachine_isHalted_acceptingPacker_false_of_local'],
  ['theorem', 'terminalBridgeMachine_isHalted_rejectingPacker_false_of_local'],
  ['theorem', 'acceptingPacker_workStep?_of_some'],
  ['theorem', 'rejectingPacker_workStep?_of_some'],
  ['theorem', 'acceptingPacker_workRunExact_of_exact'],
  ['theorem', 'rejectingPacker_workRunExact_of_exact'],
  ['theorem', 'acceptingPackerLaunch_workStep'],
  ['theorem', 'rejectingPackerLaunch_workStep'],
  ['theorem', 'acceptingTerminal_workRunExact_of_represents'],
  ['theorem', 'rejectingTerminal_workRunExact_of_represents'],
  ['theorem', 'acceptingTerminalFinal_state_eq_accept'],
  ['theorem', 'rejectingTerminalFinal_state_eq_reject'],
  ['theorem', 'terminalBridgeMachine_acceptState_ne_rejectState'],
  ['theorem', 'acceptingTerminalFinal_isHalted'],
  ['theorem', 'rejectingTerminalFinal_isHalted'],
  ['theorem', 'run_compileTerminalBridge_accepting_of_represents'],
  ['theorem', 'run_compileTerminalBridge_rejecting_of_represents'],
  ['theorem', 'run_compileTerminalBridge_accepting_of_represents_at_bound'],
  ['theorem', 'run_compileTerminalBridge_rejecting_of_represents_at_bound'],
  ['theorem', 'acceptingTerminal_output_eq'],
  ['theorem', 'rejectingTerminal_output_eq'],
  ['theorem', 'outputBits_compileTerminalBridge_accepting_of_represents'],
  ['theorem', 'outputBits_compileTerminalBridge_rejecting_of_represents'],
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
    'PNP.Concrete.PipelineStageBridges',
    'PNP.Concrete.TerminalOutputPacker',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineTerminalBridge$/mu.test(stripped)
    && /end PipelineTerminalBridge\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('does not yet transport the earlier framer/simulator/handoff trace')
    && prose.includes('ordinary paired input into the extended machine')
    && prose.includes('does not construct a complete pipeline RawRefinement')
    && prose.includes('prove target termination')
    && prose.includes('polynomial in external encoded input length')
    && prose.includes('prove CNFSAT in P or NP-completeness')
    && prose.includes('prove P = NP.'), 'explicit-nonclaims');
  require0(!/\b(?:cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u.test(stripped),
    'no-class-or-root-claim');

  require0(compact.includes(
    'def acceptingPackerState (state : Nat) : Nat := handoffState (acceptingHandoffState state)')
    && compact.includes(
      'def rejectingPackerState (state : Nat) : Nat := handoffState (rejectingHandoffState state)')
    && compact.includes(
      'theorem acceptingPackerState_ne_rejectingPackerState (left right : Nat) : acceptingPackerState left \u2260 rejectingPackerState right'),
  'verdict-indexed-disjoint-namespaces');
  require0(compact.includes(
    'def acceptingPackerLaunchRules : List WorkRule := launchRules (acceptingHandoffState PipelineOutputHandoff.framedOutputHandoff.acceptState) (acceptingPackerState TerminalOutputPacker.terminalOutputPacker.startState)')
    && compact.includes(
      'def rejectingPackerLaunchRules : List WorkRule := launchRules (rejectingHandoffState PipelineOutputHandoff.framedOutputHandoff.acceptState) (rejectingPackerState TerminalOutputPacker.terminalOutputPacker.startState)'),
  'literal-verdict-launch-tables');
  require0(compact.includes(
    'def terminalBridgeRules (machine : Machine) : List WorkRule := acceptingPackerLaunchRules ++ (rejectingPackerLaunchRules ++ (bridgedRules machine ++ (TerminalOutputPacker.terminalOutputPacker.rules.map (renameRule acceptingPackerState) ++ TerminalOutputPacker.terminalOutputPacker.rules.map (renameRule rejectingPackerState))))'),
  'literal-combined-rule-table');
  require0(compact.includes(
    'findWorkRule (terminalBridgeMachine machine).rules (acceptingPackerState state) symbol = some (renameRule acceptingPackerState rule)')
    && compact.includes(
      'findWorkRule (terminalBridgeMachine machine).rules (rejectingPackerState state) symbol = some (renameRule rejectingPackerState rule)'),
  'first-match-packer-isolation');
  require0(compact.includes(
    'theorem acceptingPackerLaunch_workStep (machine : Machine) (tape : WorkTape)')
    && compact.includes(
      'theorem rejectingPackerLaunch_workStep (machine : Machine) (tape : WorkTape)'),
  'exact-two-verdict-launches');

  require0(compact.includes(
    'def terminalBridgeWorkSteps (bits : BitString) : Nat := 1 + TerminalOutputPacker.terminalOutputPackerWorkSteps bits')
    && compact.includes(
      'def terminalBridgeRawSteps (bits : BitString) : Nat := 6 * terminalBridgeWorkSteps bits')
    && compact.includes(
      'def terminalBridgeRawTimeBound : NatPolynomial := .add TerminalOutputPacker.terminalOutputPackerRawTimeBound (.linear 0 6)')
    && compact.includes(
      'terminalBridgeRawSteps bits \u2264 terminalBridgeRawTimeBound.eval bits.length'),
  'exact-local-cost-and-polynomial');
  require0(compact.includes(
    'theorem acceptingTerminal_workRunExact_of_represents (machine : Machine) {raw : Tape} {work : WorkTape} (hRepresents : Represents raw.handoffTarget work)')
    && compact.includes(
      'theorem rejectingTerminal_workRunExact_of_represents (machine : Machine) {raw : Tape} {work : WorkTape} (hRepresents : Represents raw.handoffTarget work)')
    && compact.includes(
      'work = TerminalOutputPacker.terminalOutputPackerInputTape raw.outputBits outsideLeft outsideRight'),
  'represented-endpoint-exact-traces');
  require0(compact.includes(
    'theorem terminalBridgeMachine_acceptState_ne_rejectState (machine : Machine)')
    && compact.includes('theorem acceptingTerminalFinal_isHalted (machine : Machine)')
    && compact.includes('theorem rejectingTerminalFinal_isHalted (machine : Machine)'),
  'distinct-terminal-verdicts');
  require0(compact.includes(
    'theorem run_compileTerminalBridge_accepting_of_represents_at_bound')
    && compact.includes(
      'theorem run_compileTerminalBridge_rejecting_of_represents_at_bound')
    && compact.includes(
      'theorem outputBits_compileTerminalBridge_accepting_of_represents')
    && compact.includes(
      'theorem outputBits_compileTerminalBridge_rejecting_of_represents')
    && compact.match(/\)\)\.tape = raw\.outputBits := by/gu)?.length === 2,
  'compiled-bound-and-raw-output');

  return failures;
}

test('terminal bridge has literal launches, isolated packer copies, and no shortcuts', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('terminal bridge axiom transcript covers all 44 public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 44);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 44);
});

test('root, package, and workflow enforce the terminal bridge audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineTerminalBridge'), true);
  assert.match(packageText, /audits\/lean-concrete-pipeline-terminal-bridge0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineTerminalBridgeAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 44/u);
});

test('terminal bridge audit rejects namespace, dispatch, bound, output, assumption, and claim mutations', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('handoffState (acceptingHandoffState state)',
      'handoffState (rejectingHandoffState state)'),
    source.replace('bridgedRules machine ++', '[] ++'),
    source.replace('.linear 0 6', '.linear 0 5'),
    source.replaceAll(')).tape = raw.outputBits := by', ')).tape = [] := by'),
    `${source}\naxiom hiddenTerminalBridgeOracle : True\n`,
    source.replace('does not yet transport the earlier framer/simulator/handoff trace',
      'transports the earlier framer/simulator/handoff trace'),
    `${source}\ntheorem p_eq_np : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('handoff-to-packer launch is earned while the full compiler remains fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcretePipelineTerminalOutputPackingFormalized, true);
  assert.equal(status.leanConcretePipelineTerminalOutputPackerConnectedToBridgeEndpointFormalized, true);
  assert.equal(status.leanConcretePipelineTerminalBridgeAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineTerminalBridgeAuditedDeclarationCount, 44);
  assert.equal(status.leanConcretePipelinePriorTraceTransportToTerminalBridgeFormalized, false);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, false);
  assert.equal(status.leanConcretePipelineExternalInputSizePolynomialFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
