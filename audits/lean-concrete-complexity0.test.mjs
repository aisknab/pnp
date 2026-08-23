import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
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
const COMPLEXITY_PATH = 'lean/PNP/Concrete/Complexity.lean';
const TARGET_PATH = 'lean/PNP/Concrete/Target.lean';
const COMPLEXITY_AUDIT_PATH = 'lean-audit/PNPConcreteComplexityAxiomAudit.lean';
const TARGET_AUDIT_PATH = 'lean-audit/PNPConcreteTargetAxiomAudit.lean';

const EXPECTED_AXIOMS = Object.freeze([
  'PNP.CheckPCCPackexp',
  'PNP.GeneratePCCPack',
  'PNP.ResidualBandExactMinimization',
]);

const EXPECTED_BLOCKERS = Object.freeze([
  'Formal.ConcreteSAT',
  'Formal.ResidualBandMinimizer',
  'Formal.ZeroSlack',
  'Formal.PolynomialRuntimeAndCertificateBounds',
  'Formal.RootTheoremAndAxiomAudit',
]);

const EXPECTED_COMPLEXITY_HEADS = Object.freeze([
  ['def', 'toBool', 'PNP.Concrete.TapeSymbol.toBool'],
  ['theorem', 'toBool_ofBool', 'PNP.Concrete.TapeSymbol.toBool_ofBool'],
  ['theorem', 'map_toBool_ofBool', 'PNP.Concrete.Tape.map_toBool_ofBool'],
  ['def', 'machineOutput', 'PNP.Concrete.machineOutput'],
  ['theorem', 'machineOutput_immediateAccept_zero', 'PNP.Concrete.machineOutput_immediateAccept_zero'],
  ['def', 'substitute', 'PNP.Concrete.NatPolynomial.substitute'],
  ['theorem', 'eval_substitute', 'PNP.Concrete.NatPolynomial.eval_substitute'],
  ['inductive', 'FunctionProgram', 'PNP.Concrete.FunctionProgram'],
  ['def', 'eval', 'PNP.Concrete.FunctionProgram.eval'],
  ['def', 'chargedSteps', 'PNP.Concrete.FunctionProgram.chargedSteps'],
  ['def', 'Halts', 'PNP.Concrete.FunctionProgram.Halts'],
  ['structure', 'PolynomialTimeFunction', 'PNP.Concrete.PolynomialTimeFunction'],
  ['def', 'output', 'PNP.Concrete.PolynomialTimeFunction.output'],
  ['def', 'identity', 'PNP.Concrete.PolynomialTimeFunction.identity'],
  ['theorem', 'identity_output', 'PNP.Concrete.PolynomialTimeFunction.identity_output'],
  ['def', 'compose', 'PNP.Concrete.PolynomialTimeFunction.compose'],
  ['theorem', 'compose_output', 'PNP.Concrete.PolynomialTimeFunction.compose_output'],
  ['inductive', 'DecisionProgram', 'PNP.Concrete.DecisionProgram'],
  ['def', 'verdict', 'PNP.Concrete.DecisionProgram.verdict'],
  ['def', 'chargedSteps', 'PNP.Concrete.DecisionProgram.chargedSteps'],
  ['def', 'Halts', 'PNP.Concrete.DecisionProgram.Halts'],
  ['abbrev', 'Language', 'PNP.Concrete.Language'],
  ['structure', 'PolynomialTimeDecider', 'PNP.Concrete.PolynomialTimeDecider'],
  ['def', 'ofMachine', 'PNP.Concrete.PolynomialTimeDecider.ofMachine'],
  ['def', 'relabel', 'PNP.Concrete.PolynomialTimeDecider.relabel'],
  ['def', 'precompose', 'PNP.Concrete.PolynomialTimeDecider.precompose'],
  ['inductive', 'VerifierInputMode', 'PNP.Concrete.VerifierInputMode'],
  ['def', 'encode', 'PNP.Concrete.VerifierInputMode.encode'],
  ['theorem', 'encode_paired', 'PNP.Concrete.VerifierInputMode.encode_paired'],
  ['structure', 'VerifierProgram', 'PNP.Concrete.VerifierProgram'],
  ['def', 'verdict', 'PNP.Concrete.VerifierProgram.verdict'],
  ['def', 'chargedSteps', 'PNP.Concrete.VerifierProgram.chargedSteps'],
  ['def', 'Halts', 'PNP.Concrete.VerifierProgram.Halts'],
  ['structure', 'PolynomialTimeVerifier', 'PNP.Concrete.PolynomialTimeVerifier'],
  ['def', 'InP', 'PNP.Concrete.InP'],
  ['def', 'InNP', 'PNP.Concrete.InNP'],
  ['def', 'PEqualsNP', 'PNP.Concrete.PEqualsNP'],
  ['def', 'verifierFromDecider', 'PNP.Concrete.verifierFromDecider'],
  ['theorem', 'p_subset_np', 'PNP.Concrete.p_subset_np'],
  ['structure', 'PolynomialReduction', 'PNP.Concrete.PolynomialReduction'],
  ['def', 'ReducesTo', 'PNP.Concrete.ReducesTo'],
  ['def', 'identity', 'PNP.Concrete.PolynomialReduction.identity'],
  ['def', 'compose', 'PNP.Concrete.PolynomialReduction.compose'],
  ['theorem', 'reduction_refl', 'PNP.Concrete.reduction_refl'],
  ['theorem', 'reduction_comp', 'PNP.Concrete.reduction_comp'],
  ['theorem', 'reduction_transports_p', 'PNP.Concrete.reduction_transports_p'],
  ['structure', 'NPComplete', 'PNP.Concrete.NPComplete'],
  ['theorem', 'np_complete_in_p_implies_p_eq_np', 'PNP.Concrete.np_complete_in_p_implies_p_eq_np'],
]);

const EXPECTED_TARGET_HEADS = Object.freeze([
  ['def', 'ConcretePEqualsNP', 'PNP.Main.ConcretePEqualsNP'],
  ['theorem', 'concretePEqualsNP_iff', 'PNP.Main.concretePEqualsNP_iff'],
]);

const EXPECTED_STRUCTURE_FIELDS = Object.freeze({
  PolynomialTimeFunction: ['program', 'runtimeBound', 'outputSizeBound', 'haltsWithin', 'runtime_le', 'output_size_le'],
  PolynomialTimeDecider: ['program', 'runtimeBound', 'haltsWithin', 'runtime_le', 'accepts_iff'],
  VerifierProgram: ['inputMode', 'decision'],
  PolynomialTimeVerifier: ['program', 'certificateBound', 'runtimeBound', 'haltsWithin', 'runtime_le', 'accepts_iff'],
  PolynomialReduction: ['function', 'correctness'],
  NPComplete: ['inNP', 'hard'],
});

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
}

function compactLean0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function headPairs0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) => [kind, name]);
}

function structureFields0(source) {
  const lines = stripLeanCommentsAndStrings0(source).split('\n');
  const structures = {};
  for (let index = 0; index < lines.length; index += 1) {
    const header = /^structure\s+([A-Za-z_][\w]*)\b.*\bwhere\s*$/u.exec(lines[index]);
    if (header === null) continue;
    const fields = [];
    for (let cursor = index + 1; cursor < lines.length; cursor += 1) {
      if (/^\S/u.test(lines[cursor])) break;
      const field = /^\s+([A-Za-z_][\w]*)\s*:/u.exec(lines[cursor]);
      if (field !== null) fields.push(field[1]);
    }
    structures[header[1]] = fields;
  }
  return structures;
}

function validateComplexity0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compactLean0(source);
  const fields = structureFields0(source);

  require0(JSON.stringify(imports0(source)) === JSON.stringify(['PNP.Concrete.TapeHandoff']), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|funext|propext|String)\b/u.test(stripped), 'forbidden-shortcut');
  require0(!source.includes('"'), 'string-literal');
  require0(!/\b(?:code|oracle|map|verifier|transport|pSubsetNP)\s*:/u.test(stripped), 'hidden-executable-field');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_COMPLEXITY_HEADS.map(([kind, name]) => [kind, name])), 'declaration-surface');
  require0(JSON.stringify(fields) === JSON.stringify(EXPECTED_STRUCTURE_FIELDS), 'exact-structure-fields');

  require0(compact.includes('def machineOutput (machine : Machine) (steps : Nat) (input : BitString) : BitString := (run machine steps (startConfig machine input)).tape.outputBits'), 'machine-output-interpreter');
  require0(compact.includes('inductive FunctionProgram where | machine (program : Machine) (stepBound : NatPolynomial) | compose (first second : FunctionProgram) deriving DecidableEq, Repr'), 'finite-function-syntax');
  require0(compact.includes('| .compose first second, input => eval second (eval first input)'), 'function-composition-order');
  require0(compact.includes('| .compose first second, input => chargedSteps first input + BitString.size (eval first input) + chargedSteps second (eval first input)'), 'function-copy-charge');
  require0(compact.includes('boundedDecide program (stepBound.eval (BitString.size input)) input ≠ .timeout'), 'timeout-excluded');
  require0(compact.includes('structure PolynomialTimeFunction where program : FunctionProgram runtimeBound : NatPolynomial outputSizeBound : NatPolynomial haltsWithin : ∀ input, program.Halts input runtime_le : ∀ input, program.chargedSteps input ≤ runtimeBound.eval (BitString.size input) output_size_le : ∀ input, BitString.size (program.eval input) ≤ outputSizeBound.eval (BitString.size input)'), 'function-proof-fields');
  require0(compact.includes('runtimeBound := .add (.add first.runtimeBound first.outputSizeBound) (NatPolynomial.substitute second.runtimeBound first.outputSizeBound)'), 'function-runtime-substitution-bound');
  require0(compact.includes('outputSizeBound := NatPolynomial.substitute second.outputSizeBound first.outputSizeBound'), 'function-output-substitution-bound');
  require0(compact.includes('(Nat.add_le_add (first.runtime_le input) (first.output_size_le input))'), 'function-first-stage-and-copy-proof');
  require0(compact.includes('(second.runtime_le (first.output input))'), 'function-second-stage-proof');

  require0(compact.includes('inductive DecisionProgram where | machine (program : Machine) (stepBound : NatPolynomial) | precompose (preprocessor : FunctionProgram) (decision : DecisionProgram) deriving DecidableEq, Repr'), 'finite-decision-syntax');
  require0(compact.includes('| .precompose preprocessor decision, input => verdict decision (preprocessor.eval input)'), 'decision-precomposition-order');
  require0(compact.includes('preprocessor.chargedSteps input + BitString.size (preprocessor.eval input) + chargedSteps decision (preprocessor.eval input)'), 'decision-copy-charge');
  require0(compact.includes('structure PolynomialTimeDecider (language : Language) where program : DecisionProgram runtimeBound : NatPolynomial haltsWithin : ∀ input, program.Halts input runtime_le : ∀ input, program.chargedSteps input ≤ runtimeBound.eval (BitString.size input) accepts_iff : ∀ input, program.verdict input = .accept ↔ language input'), 'decider-proof-fields');
  require0(compact.includes('runtimeBound := .add (.add function.runtimeBound function.outputSizeBound) (NatPolynomial.substitute decision.runtimeBound function.outputSizeBound)'), 'decision-runtime-substitution-bound');

  require0(compact.includes('inductive VerifierInputMode where | inputOnly | paired deriving DecidableEq, Repr'), 'finite-verifier-input-mode');
  require0(compact.includes('| .inputOnly, input, _ => input | .paired, input, certificate => BitString.pair input certificate'), 'canonical-pairing');
  require0(compact.includes('structure VerifierProgram where inputMode : VerifierInputMode decision : DecisionProgram deriving DecidableEq, Repr'), 'finite-verifier-program');
  require0(compact.includes('structure PolynomialTimeVerifier (language : Language) where program : VerifierProgram certificateBound : NatPolynomial runtimeBound : NatPolynomial'), 'verifier-polynomial-fields');
  require0(compact.includes('BitString.size certificate ≤ certificateBound.eval (BitString.size input) → program.Halts input certificate'), 'verifier-bounded-halting');
  require0(compact.includes('BitString.size certificate ≤ certificateBound.eval (BitString.size input) → program.chargedSteps input certificate ≤ runtimeBound.eval (BitString.size input)'), 'verifier-bounded-runtime');
  require0(compact.includes('∃ certificate, BitString.size certificate ≤ certificateBound.eval (BitString.size input) ∧ program.verdict input certificate = .accept'), 'bounded-certificate-semantics');
  require0(compact.includes('{ program := { inputMode := .inputOnly, decision := decision.program } certificateBound := .constant 0 runtimeBound := decision.runtimeBound'), 'input-only-p-embedding');
  require0(compact.includes('exact ⟨[], Nat.le_refl 0, (decision.accepts_iff input).mpr member⟩'), 'empty-certificate-witness');
  require0(compact.includes('theorem p_subset_np {language : Language} : InP language → InNP language := by'), 'p-subset-np-theorem');

  require0(compact.includes('structure PolynomialReduction (source target : Language) where function : PolynomialTimeFunction correctness : ∀ input, source input ↔ target (function.output input)'), 'reduction-proof-fields');
  require0(compact.includes('{ function := PolynomialTimeFunction.compose left.function right.function'), 'reduction-composition-function-order');
  require0(compact.includes('last (right.function.output (left.function.output input))'), 'reduction-composition-semantic-order');
  require0(compact.includes('theorem reduction_refl (language : Language) : ReducesTo language language :='), 'reduction-refl-theorem');
  require0(compact.includes('theorem reduction_comp {first middle last : Language} : ReducesTo first middle → ReducesTo middle last → ReducesTo first last := by'), 'reduction-comp-theorem');
  require0(compact.includes('theorem reduction_transports_p {source target : Language} : ReducesTo source target → InP target → InP source := by'), 'reduction-transport-theorem');
  require0(compact.includes('PolynomialTimeDecider.precompose reduction.function targetDecision'), 'reduction-transport-construction');
  require0(compact.includes('theorem np_complete_in_p_implies_p_eq_np'), 'np-complete-in-p-theorem');
  require0(compact.includes('exact p_subset_np languageInP'), 'np-complete-forward-inclusion');
  require0(compact.includes('exact reduction_transports_p (complete.hard language languageInNP) completeInP'), 'np-complete-reverse-inclusion');
  require0(!compact.includes('.timeout => .reject'), 'timeout-not-rejection');
  return failures;
}

function validateTarget0(source) {
  const failures = [];
  const compact = compactLean0(source);
  const stripped = stripLeanCommentsAndStrings0(source);
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(JSON.stringify(imports0(source)) === JSON.stringify(['PNP.Concrete.Complexity']), 'target-closed-import');
  require0(/^namespace PNP\.Main$/mu.test(stripped) && /end PNP\.Main\s*$/u.test(stripped), 'target-namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'target-assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'target-private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'target-unaudited');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_TARGET_HEADS.map(([kind, name]) => [kind, name])), 'target-declaration-surface');
  require0(compact.includes('def ConcretePEqualsNP : Prop := PNP.Concrete.PEqualsNP'), 'exact-inactive-target');
  require0(compact.includes('theorem concretePEqualsNP_iff : ConcretePEqualsNP ↔ PNP.Concrete.PEqualsNP := Iff.rfl'), 'exact-target-pin');
  require0(!/\b(?:def|theorem|axiom|constant|opaque)\s+p_eq_np\b/u.test(stripped), 'no-compatibility-root');
  return failures;
}

function replaceRequired0(source, before, after) {
  const mutated = source.replace(before, after);
  assert.notEqual(mutated, source, `mutation source not found: ${before}`);
  return mutated;
}

async function filesBelow0(directory) {
  const entries = await readdir(directory, { withFileTypes: true });
  const nested = await Promise.all(entries.map((entry) => {
    const child = path.join(directory, entry.name);
    return entry.isDirectory() ? filesBelow0(child) : [child];
  }));
  return nested.flat();
}

test('concrete complexity source is closed, finite, proof-bearing, and shortcut-free', async () => {
  assert.deepEqual(validateComplexity0(await text0(COMPLEXITY_PATH)), []);
  assert.deepEqual(validateTarget0(await text0(TARGET_PATH)), []);
});

test('complexity and target transcripts cover exactly 48 and 2 explicit heads once', async () => {
  const [complexity, target, complexityAudit, targetAudit] = await Promise.all([
    text0(COMPLEXITY_PATH),
    text0(TARGET_PATH),
    text0(COMPLEXITY_AUDIT_PATH),
    text0(TARGET_AUDIT_PATH),
  ]);
  assert.equal(EXPECTED_COMPLEXITY_HEADS.length, 48);
  assert.equal(EXPECTED_TARGET_HEADS.length, 2);
  assert.deepEqual(headPairs0(complexity), EXPECTED_COMPLEXITY_HEADS.map(([kind, name]) => [kind, name]));
  assert.deepEqual(headPairs0(target), EXPECTED_TARGET_HEADS.map(([kind, name]) => [kind, name]));
  assert.deepEqual(imports0(complexityAudit), ['PNP']);
  assert.deepEqual(imports0(targetAudit), ['PNP']);
  assert.deepEqual(printed0(complexityAudit), EXPECTED_COMPLEXITY_HEADS.map(([, , full]) => full));
  assert.deepEqual(printed0(targetAudit), EXPECTED_TARGET_HEADS.map(([, , full]) => full));
  assert.equal(new Set(printed0(complexityAudit)).size, 48);
  assert.equal(new Set(printed0(targetAudit)).size, 2);
});

test('finite interpreters charge both stages, output handoff, and polynomial substitution', async () => {
  const source = await text0(COMPLEXITY_PATH);
  const failures = validateComplexity0(source);
  for (const label of [
    'function-copy-charge',
    'function-runtime-substitution-bound',
    'function-output-substitution-bound',
    'function-first-stage-and-copy-proof',
    'function-second-stage-proof',
    'decision-copy-charge',
    'decision-runtime-substitution-bound',
  ]) assert.equal(failures.includes(label), false, label);
});

test('NP uses bounded certificates, canonical pairing, and an explicit input-only P embedding', async () => {
  const source = await text0(COMPLEXITY_PATH);
  const failures = validateComplexity0(source);
  for (const label of [
    'canonical-pairing',
    'verifier-polynomial-fields',
    'verifier-bounded-halting',
    'verifier-bounded-runtime',
    'bounded-certificate-semantics',
    'input-only-p-embedding',
    'empty-certificate-witness',
    'p-subset-np-theorem',
  ]) assert.equal(failures.includes(label), false, label);
});

test('reduction identity, composition, transport, and NP-complete-in-P are constructions', async () => {
  const source = await text0(COMPLEXITY_PATH);
  const failures = validateComplexity0(source);
  for (const label of [
    'reduction-proof-fields',
    'reduction-composition-function-order',
    'reduction-composition-semantic-order',
    'reduction-refl-theorem',
    'reduction-comp-theorem',
    'reduction-transport-theorem',
    'reduction-transport-construction',
    'np-complete-in-p-theorem',
    'np-complete-forward-inclusion',
    'np-complete-reverse-inclusion',
  ]) assert.equal(failures.includes(label), false, label);
});

test('target remains an inactive definition after the raw-machine link closes, and the gate stays false', async () => {
  const [status, publicationMap] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.deepEqual(status.remainingBlockers, EXPECTED_BLOCKERS);
  assert.deepEqual(status.projectSpecificAxiomInventory, EXPECTED_AXIOMS);
  assert.equal(status.standardComplexityModelFormalized, true);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.equal(status.concretePublicationGate.subchecks.standardComplexityModelEligible, true);
  assert.equal(status.concretePublicationGate.subchecks.concreteTargetPresent, true);
  assert.equal(status.concretePublicationGate.subchecks.concreteTargetIsDefinition, true);
  assert.equal(status.concretePublicationGate.subchecks.compatibilityRootPresent, false);
  assert.equal(publicationMap.gate.standardComplexityModelEligible, true);
  for (const field of [
    'expectedConcreteTargetKernelTypeSha256',
    'expectedConcreteTargetKernelValueSha256',
    'expectedRootKernelTypeSha256',
    'expectedAxiomClosureSha256',
    'expectedSourceClosureSha256',
  ]) assert.equal(publicationMap.gate[field], null, field);

  const leanFiles = (await filesBelow0(path.join(ROOT, 'lean'))).filter((file) => file.endsWith('.lean'));
  const allLean = stripLeanCommentsAndStrings0((await Promise.all(leanFiles.map((file) => readFile(file, 'utf8')))).join('\n'));
  assert.doesNotMatch(allLean, /\b(?:def|theorem|axiom|constant|opaque)\s+p_eq_np\b/u);
});

test('workflow executes both exact zero-axiom transcripts', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-concrete-complexity0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteComplexityAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 48/u);
  assert.match(workflow, /PNPConcreteTargetAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 2/u);
});

test('static audit rejects assumptions, hidden executables, import growth, and transcript drift', async () => {
  const [source, target, complexityAudit, targetAudit] = await Promise.all([
    text0(COMPLEXITY_PATH), text0(TARGET_PATH),
    text0(COMPLEXITY_AUDIT_PATH), text0(TARGET_AUDIT_PATH),
  ]);
  assert.equal(validateComplexity0(`import PNP.Complexity\n${source}`).includes('closed-import'), true);
  assert.equal(validateComplexity0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateComplexity0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-declaration'), true);
  assert.equal(validateComplexity0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateComplexity0(`${source}\ndef code : String := "oracle"\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    '  outputSizeBound : NatPolynomial',
    '  outputSizeBound : NatPolynomial\n  map : BitString → BitString')).includes('hidden-executable-field'), true);
  assert.notDeepEqual(printed0(complexityAudit).slice(0, -1), EXPECTED_COMPLEXITY_HEADS.map(([, , full]) => full));
  assert.notDeepEqual([...printed0(targetAudit), 'PNP.Main.p_eq_np'], EXPECTED_TARGET_HEADS.map(([, , full]) => full));
  assert.equal(validateComplexity0(`${source}\ntheorem extra : True := True.intro\n`).includes('declaration-surface'), true);
  assert.equal(validateTarget0(`import PNP.Main\n${target}`).includes('target-closed-import'), true);
});

test('static audit rejects verifier, timeout, reduction-order, and cost-accounting mutations', async () => {
  const source = await text0(COMPLEXITY_PATH);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'BitString.pair input certificate',
    'BitString.pair certificate input')).includes('canonical-pairing'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    '  certificateBound : NatPolynomial',
    '  certificateBound : Nat')).includes('verifier-polynomial-fields'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'program.Halts input certificate',
    'program.verdict input certificate = .reject')).includes('verifier-bounded-halting'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    '{ program := { inputMode := .inputOnly, decision := decision.program }',
    '{ program := { inputMode := .paired, decision := decision.program }')).includes('input-only-p-embedding'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'exact ⟨[], Nat.le_refl 0, (decision.accepts_iff input).mpr member⟩',
    'exact ⟨[false], Nat.le_refl 0, (decision.accepts_iff input).mpr member⟩')).includes('empty-certificate-witness'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'chargedSteps first input + BitString.size (eval first input) +',
    'chargedSteps first input +')).includes('function-copy-charge'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    '.add (.add first.runtimeBound first.outputSizeBound)',
    '.add first.runtimeBound')).includes('function-runtime-substitution-bound'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'NatPolynomial.substitute second.runtimeBound first.outputSizeBound',
    'second.runtimeBound')).includes('function-runtime-substitution-bound'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'PolynomialTimeFunction.compose left.function right.function',
    'PolynomialTimeFunction.compose right.function left.function')).includes('reduction-composition-function-order'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'last (right.function.output (left.function.output input))',
    'last (left.function.output (right.function.output input))')).includes('reduction-composition-semantic-order'), true);
  assert.equal(validateComplexity0(replaceRequired0(source,
    'theorem reduction_transports_p',
    'def reduction_transports_p')).includes('reduction-transport-theorem'), true);
});

test('static audit rejects target activation, target forgery, and a compatibility root', async () => {
  const target = await text0(TARGET_PATH);
  assert.equal(validateTarget0(replaceRequired0(target,
    'PNP.Concrete.PEqualsNP', 'True')).includes('exact-inactive-target'), true);
  assert.equal(validateTarget0(replaceRequired0(target,
    'def ConcretePEqualsNP : Prop := PNP.Concrete.PEqualsNP',
    'def ConcretePEqualsNP : Prop := PNP.PEqualsNP')).includes('exact-inactive-target'), true);
  assert.equal(validateTarget0(`${target}\ntheorem p_eq_np : ConcretePEqualsNP := by sorry\n`).includes('no-compatibility-root'), true);
});
