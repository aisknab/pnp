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
const SOURCE_PATH = 'lean/PNP/Concrete/TapeBlankEquivalence.lean';
const AUDIT_PATH = 'lean-audit/PNPConcreteTapeBlankEquivalenceAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPConcreteTapeBlankEquivalence.lean';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'blankCellAt', 'PNP.Concrete.Tape.blankCellAt'],
  ['theorem', 'blankCellAt_nil', 'PNP.Concrete.Tape.blankCellAt_nil'],
  ['theorem', 'blankCellAt_cons_zero', 'PNP.Concrete.Tape.blankCellAt_cons_zero'],
  ['theorem', 'blankCellAt_cons_succ', 'PNP.Concrete.Tape.blankCellAt_cons_succ'],
  ['def', 'BlankEquivalent', 'PNP.Concrete.Tape.BlankEquivalent'],
  ['theorem', 'blankEquivalent_refl', 'PNP.Concrete.Tape.blankEquivalent_refl'],
  ['theorem', 'blankEquivalent_symm', 'PNP.Concrete.Tape.blankEquivalent_symm'],
  ['theorem', 'blankEquivalent_trans', 'PNP.Concrete.Tape.blankEquivalent_trans'],
  ['theorem', 'blankEquivalent_write', 'PNP.Concrete.Tape.blankEquivalent_write'],
  ['theorem', 'blankEquivalent_moveLeft', 'PNP.Concrete.Tape.blankEquivalent_moveLeft'],
  ['theorem', 'blankEquivalent_moveRight', 'PNP.Concrete.Tape.blankEquivalent_moveRight'],
  ['theorem', 'blankEquivalent_move', 'PNP.Concrete.Tape.blankEquivalent_move'],
  ['theorem', 'outputBits_eq_of_blankEquivalent', 'PNP.Concrete.Tape.outputBits_eq_of_blankEquivalent'],
  ['def', 'BlankEquivalent', 'PNP.Concrete.Configuration.BlankEquivalent'],
  ['theorem', 'blankEquivalent_refl', 'PNP.Concrete.Configuration.blankEquivalent_refl'],
  ['theorem', 'blankEquivalent_symm', 'PNP.Concrete.Configuration.blankEquivalent_symm'],
  ['theorem', 'blankEquivalent_trans', 'PNP.Concrete.Configuration.blankEquivalent_trans'],
  ['theorem', 'run_blankEquivalent', 'PNP.Concrete.run_blankEquivalent'],
  ['def', 'rawInputWorkTape', 'PNP.Concrete.rawInputWorkTape'],
  ['theorem', 'encodeWorkTape_rawInputWorkTape_blankEquivalent',
    'PNP.Concrete.encodeWorkTape_rawInputWorkTape_blankEquivalent'],
  ['theorem', 'startConfig_compileWorkMachine_blankEquivalent',
    'PNP.Concrete.startConfig_compileWorkMachine_blankEquivalent'],
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

function headPairs0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) => [kind, name]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const prose = source.replaceAll('\x60', '').replace(/\s+/gu, ' ');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.TapeHandoff',
    'PNP.Concrete.WorkInput',
  ]), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace Tape$/mu.test(stripped)
    && /^namespace Configuration$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(compact), 'namespaces');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-proof-shortcut');
  require0(!/\b(?:oracle|referenceMinimum|minimization|RawRefinement|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'forbidden-oracle-or-claim');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_HEADS.map(([kind, name]) => [kind, name])),
  'declaration-surface');

  require0(compact.includes(
    'def blankCellAt : List TapeSymbol → Nat → TapeSymbol | [], _ => .blank'),
  'blank-extension');
  require0(compact.includes(
    'def BlankEquivalent (first second : Tape) : Prop := first.head = second.head ∧ (∀ index, blankCellAt first.left index = blankCellAt second.left index) ∧ (∀ index, blankCellAt first.right index = blankCellAt second.right index)'),
  'exact-tape-relation');
  require0(compact.includes(
    'theorem run_blankEquivalent (machine : Machine) (fuel : Nat)')
    && compact.includes('exact ih hNext'),
  'run-preservation');
  require0(compact.includes(
    'def rawInputWorkTape (input : BitString) : WorkTape := WorkTape.ofSymbols (packWorkSymbols (input.map TapeSymbol.ofBool))'),
  'literal-input-packing');
  require0(compact.includes(
    'theorem startConfig_compileWorkMachine_blankEquivalent (machine : WorkMachine) (input : BitString)'),
  'ordinary-start-bridge');
  require0(prose.includes('does not construct a pipeline stage, a RawRefinement, or any complexity-class result.'),
    'explicit-boundary');

  return failures;
}

test('blank-materialization equivalence is constructive, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every public blank-equivalence declaration', async () => {
  const [source, audit, regression, root] = await Promise.all([
    text0(SOURCE_PATH),
    text0(AUDIT_PATH),
    text0(REGRESSION_PATH),
    text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(printed0(audit), EXPECTED_HEADS.map(([, , full]) => full));
  assert.equal(new Set(printed0(audit)).size, EXPECTED_HEADS.length);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(imports0(regression), ['PNP']);
  assert.ok(imports0(root).includes('PNP.Concrete.TapeBlankEquivalence'));
  assert.deepEqual(headPairs0(source), EXPECTED_HEADS.map(([kind, name]) => [kind, name]));
});

test('relation mutations and compiler overclaims fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('| [], _ => .blank', '| [], _ => .zero'),
    source.replace('first.head = second.head ∧', 'True ∧'),
    source.replace('(∀ index, blankCellAt first.right index = blankCellAt second.right index)', 'True'),
    source.replace('exact ih hNext', 'exact Configuration.blankEquivalent_refl _'),
    source.replace('packWorkSymbols (input.map TapeSymbol.ofBool)', 'packWorkSymbols []'),
    `${source}\naxiom blankOracle : Tape → Tape\n`,
    `${source}\ntheorem pipelineRawRefinement := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('the machine-link and publication gate remain fail closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'));
  assert.equal(map.gate.standardComplexityModelEligible, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
