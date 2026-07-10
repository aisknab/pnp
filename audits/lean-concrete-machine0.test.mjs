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
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const BITSTRING_PATH = 'lean/PNP/Concrete/BitString.lean';
const MACHINE_PATH = 'lean/PNP/Concrete/Machine.lean';
const BITSTRING_AUDIT_PATH = 'lean-audit/PNPConcreteBitStringAxiomAudit.lean';
const MACHINE_AUDIT_PATH = 'lean-audit/PNPConcreteMachineAxiomAudit.lean';

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
}

function bitStringDeclarations0(source) {
  let polynomial = false;
  return explicitLeanDeclarationHeads0(source).map(({ name }) => {
    if (name === 'NatPolynomial') polynomial = true;
    if (name === 'BitString') return 'PNP.Concrete.BitString';
    if (name === 'NatPolynomial') return 'PNP.Concrete.NatPolynomial';
    return `PNP.Concrete.${polynomial ? 'NatPolynomial' : 'BitString'}.${name}`;
  });
}

const TAPE_METHODS = new Set(['blank', 'ofInput', 'write', 'moveLeft', 'moveRight', 'move']);
const WITNESS_METHODS = new Set(['verdict', 'verdict_ne_timeout', 'verdict_accepts_iff']);

function machineDeclarations0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => {
    if (name === 'ofBool') return 'PNP.Concrete.TapeSymbol.ofBool';
    if (TAPE_METHODS.has(name)) return `PNP.Concrete.Tape.${name}`;
    if (name.startsWith('Machine.')) return `PNP.Concrete.${name}`;
    if (WITNESS_METHODS.has(name)) return `PNP.Concrete.PolynomialTimeMachine.${name}`;
    return `PNP.Concrete.${name}`;
  });
}

function validateSource0(bitString, machine) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(imports0(bitString).length === 0, 'bitstring-closed-import');
  require0(JSON.stringify(imports0(machine)) === JSON.stringify(['PNP.Concrete.BitString']),
    'machine-closed-import');
  for (const [label, source] of [['bitstring', bitString], ['machine', machine]]) {
    require0(!hasLeanAssumptionDeclaration0(source), `${label}-assumption`);
    require0(!hasPrivateLeanDeclaration0(source), `${label}-private`);
    require0(!hasUnauditedLeanDeclarationForm0(source), `${label}-unaudited`);
    require0(!/\b(?:sorry|admit|unsafe|native_decide|String)\b/u.test(source), `${label}-shortcut`);
  }
  require0(/structure Machine where\s+rules : List Rule\s+startState : Nat\s+acceptState : Nat\s+rejectState : Nat\s+deriving/u.test(machine),
    'finite-rule-list');
  require0(/inductive NatPolynomial where\s+\| constant \(value : Nat\)\s+\| variable\s+\| add \(left right : NatPolynomial\)\s+\| mul \(left right : NatPolynomial\)\s+deriving/u.test(bitString),
    'closed-polynomial-syntax');
  require0(/structure PolynomialTimeMachine \(language : BitString → Prop\) where\s+machine : Machine\s+timeBound : NatPolynomial\s+haltsWithin : ∀ input,[\s\S]*accepts_iff : ∀ input,[\s\S]*language input/u.test(machine),
    'proof-bearing-runtime');
  require0(/def run[\s\S]*\| 0, config => config[\s\S]*\| fuel \+ 1, config =>[\s\S]*step\? machine config/u.test(machine),
    'fuel-semantics');
  require0(/def boundedDecide[\s\S]*let final := run machine fuel[\s\S]*final\.state == machine\.acceptState[\s\S]*final\.state == machine\.rejectState/u.test(machine),
    'post-run-verdict');
  for (const theorem of [
    'immediateAcceptMachine_accepts',
    'immediateRejectMachine_rejects',
    'stuckMachine_times_out',
    'acceptLeadingZeroMachine_zero_fuel_times_out',
    'acceptLeadingZeroMachine_one_fuel_accepts',
  ]) require0(machine.includes(`theorem ${theorem}`), `missing-regression:${theorem}`);
  require0(bitString.includes('theorem frame_prefix_free'), 'prefix-free-frame');
  require0(bitString.includes('theorem decodePair_trailing'), 'canonical-pair-trailing-rejection');
  return failures;
}

test('concrete bitstring and machine kernels are executable and assumption-free by construction', async () => {
  const [bitString, machine] = await Promise.all([text0(BITSTRING_PATH), text0(MACHINE_PATH)]);
  assert.deepEqual(validateSource0(bitString, machine), []);
});

test('axiom transcripts cover every explicit declaration exactly once', async () => {
  const [bitString, machine, bitAudit, machineAudit] = await Promise.all([
    text0(BITSTRING_PATH), text0(MACHINE_PATH), text0(BITSTRING_AUDIT_PATH), text0(MACHINE_AUDIT_PATH),
  ]);
  const bitExpected = bitStringDeclarations0(bitString);
  const machineExpected = machineDeclarations0(machine);
  assert.equal(bitExpected.length, 41);
  assert.equal(machineExpected.length, 38);
  assert.deepEqual(printed0(bitAudit), bitExpected);
  assert.deepEqual(printed0(machineAudit), machineExpected);
  assert.equal(new Set(printed0(bitAudit)).size, bitExpected.length);
  assert.equal(new Set(printed0(machineAudit)).size, machineExpected.length);
});

test('regression theorems pin zero-fuel, one-step, accept, reject, and timeout behavior', async () => {
  const machine = await text0(MACHINE_PATH);
  assert.match(machine, /boundedDecide immediateAcceptMachine 0 \[\] = \.accept := rfl/u);
  assert.match(machine, /boundedDecide immediateRejectMachine 0 \[true\] = \.reject := rfl/u);
  assert.match(machine, /boundedDecide stuckMachine 100 \[false, true\] = \.timeout := rfl/u);
  assert.match(machine, /boundedDecide acceptLeadingZeroMachine 0 \[false\] = \.timeout := rfl/u);
  assert.match(machine, /boundedDecide acceptLeadingZeroMachine 1 \[false\] = \.accept := rfl/u);
});

test('formal publication records only the concrete kernel milestone', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  const milestone = status.formalPublicationMilestones.find(({ id }) => id === 'concrete-machine-cost-kernel');
  assert.equal(milestone.status, 'formalized-foundation-only');
  assert.equal(milestone.earned, true);
  assert.equal(status.standardComplexityModelFormalized, false);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), true);
  assert.equal(status.projectSpecificAxiomInventory.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('workflow enforces both complete zero-axiom transcripts', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-concrete-machine0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteBitStringAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 41/u);
  assert.match(workflow, /PNPConcreteMachineAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 38/u);
});

test('static audit rejects hidden assumptions, arbitrary code functions, altered fuel semantics, and transcript drift', async () => {
  const [bitString, machine, machineAudit] = await Promise.all([
    text0(BITSTRING_PATH), text0(MACHINE_PATH), text0(MACHINE_AUDIT_PATH),
  ]);
  assert.equal(validateSource0(`${bitString}\naxiom hidden : True\n`, machine).includes('bitstring-assumption'), true);
  assert.equal(validateSource0(bitString, `${machine}\nprivate theorem hidden : True := True.intro\n`).includes('machine-private'), true);
  assert.equal(validateSource0(bitString, machine.replace('rules : List Rule', 'rules : List Rule\n  oracle : BitString → Bool')).includes('finite-rule-list'), true);
  assert.equal(validateSource0(bitString.replace('| variable', '| oracle (f : Nat → Nat)\n  | variable'), machine).includes('closed-polynomial-syntax'), true);
  assert.equal(validateSource0(bitString, machine.replace('| 0, config => config', '| 0, config => (step? machine config).getD config')).includes('fuel-semantics'), true);
  assert.equal(validateSource0(bitString, machine.replace('let final := run machine fuel', 'let final := startConfig machine input')).includes('post-run-verdict'), true);
  assert.notDeepEqual(printed0(machineAudit).slice(0, -1), machineDeclarations0(machine));
});
