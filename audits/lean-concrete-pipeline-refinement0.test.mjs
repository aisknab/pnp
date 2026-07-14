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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineRefinement.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPConcretePipelineRefinementRecursive.lean';

const EXPECTED_HEADS = Object.freeze([
  ['structure', 'RawRefinement', 'PNP.Concrete.FunctionProgram.RawRefinement'],
  ['def', 'ofMachine', 'PNP.Concrete.FunctionProgram.RawRefinement.ofMachine'],
  ['def', 'compose', 'PNP.Concrete.FunctionProgram.RawRefinement.compose'],
  ['def', 'compile', 'PNP.Concrete.FunctionProgram.RawRefinement.compile'],
  ['theorem', 'compile_haltsWithin', 'PNP.Concrete.FunctionProgram.RawRefinement.compile_haltsWithin'],
  ['theorem', 'compile_output_eq', 'PNP.Concrete.FunctionProgram.RawRefinement.compile_output_eq'],
  ['theorem', 'output_size_le', 'PNP.Concrete.FunctionProgram.RawRefinement.output_size_le'],
  ['structure', 'RawRefinement', 'PNP.Concrete.DecisionProgram.RawRefinement'],
  ['def', 'ofMachine', 'PNP.Concrete.DecisionProgram.RawRefinement.ofMachine'],
  ['def', 'precompose', 'PNP.Concrete.DecisionProgram.RawRefinement.precompose'],
  ['def', 'compile', 'PNP.Concrete.DecisionProgram.RawRefinement.compile'],
  ['theorem', 'compile_haltsWithin', 'PNP.Concrete.DecisionProgram.RawRefinement.compile_haltsWithin'],
  ['theorem', 'compile_verdict_eq', 'PNP.Concrete.DecisionProgram.RawRefinement.compile_verdict_eq'],
  ['def', 'toMachine', 'PNP.Concrete.PolynomialTimeDecider.toMachine'],
  ['def', 'compileToMachine', 'PNP.Concrete.PolynomialTimeDecider.compileToMachine'],
  ['theorem', 'compileToMachine_accepts_iff', 'PNP.Concrete.PolynomialTimeDecider.compileToMachine_accepts_iff'],
]);

const EXPECTED_STRUCTURE_FIELDS = Object.freeze([
  ['RawRefinement', ['machine', 'timeBound', 'haltsWithin', 'output_eq']],
  ['RawRefinement', ['machine', 'timeBound', 'haltsWithin', 'verdict_eq']],
]);

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
  const structures = [];
  for (let index = 0; index < lines.length; index += 1) {
    const header = /^structure\s+([A-Za-z_][\w]*)\b.*\bwhere\s*$/u.exec(lines[index]);
    if (header === null) continue;
    const fields = [];
    for (let cursor = index + 1; cursor < lines.length; cursor += 1) {
      if (/^\S/u.test(lines[cursor])) break;
      const field = /^\s+([A-Za-z_][\w]*)\s*:/u.exec(lines[cursor]);
      if (field !== null) fields.push(field[1]);
    }
    structures.push([header[1], fields]);
  }
  return structures;
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compactLean0(source);

  require0(JSON.stringify(imports0(source)) ===
    JSON.stringify(['PNP.Concrete.PipelineSequentialCompiler']), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) &&
    /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|funext|propext|String)\b/u.test(stripped),
    'forbidden-shortcut');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_HEADS.map(([kind, name]) => [kind, name])),
  'declaration-surface');
  require0(JSON.stringify(structureFields0(source)) ===
    JSON.stringify(EXPECTED_STRUCTURE_FIELDS), 'exact-structure-fields');

  require0(compact.includes('structure RawRefinement (source : FunctionProgram) where machine : Machine timeBound : NatPolynomial haltsWithin : ∀ input, source.Halts input → boundedDecide machine (timeBound.eval (BitString.size input)) input ≠ .timeout output_eq : ∀ input, source.Halts input → machineOutput machine (timeBound.eval (BitString.size input)) input = source.eval input'),
    'function-refinement-contract');
  require0(compact.includes('def ofMachine (machine : Machine) (stepBound : NatPolynomial) : RawRefinement (.machine machine stepBound) := { machine := machine timeBound := stepBound'),
    'function-leaf-exact-budget');
  require0(compact.includes('rw [refinement.output_eq input (function.haltsWithin input)] exact function.output_size_le input'),
    'function-output-bound-transport');
  require0(compact.includes('structure RawRefinement (source : DecisionProgram) where machine : Machine timeBound : NatPolynomial haltsWithin : ∀ input, source.Halts input → boundedDecide machine (timeBound.eval (BitString.size input)) input ≠ .timeout verdict_eq : ∀ input, source.Halts input → boundedDecide machine (timeBound.eval (BitString.size input)) input = source.verdict input'),
    'decision-refinement-contract');
  require0((compact.match(/timeBound := stepBound/g) ?? []).length === 2,
    'both-leaves-preserve-budget');
  require0((compact.match(/PipelineSequentialCompiler\.sequentialMachine/g) ?? []).length === 2
    && (compact.match(/PipelineSequentialCompiler\.sequentialRawTimeBound/g) ?? []).length === 2,
  'literal-sequential-machine-and-polynomial');
  require0((compact.match(/PipelineSequentialCompiler\.sequential_correct/g) ?? []).length === 4,
    'exact-sequential-correctness');
  require0(compact.includes('def compile : (source : FunctionProgram) → RawRefinement source | .machine machine stepBound => ofMachine machine stepBound | .compose first second => compose (compile first) (compile second)'),
    'recursive-function-compiler');
  require0(compact.includes('def compile : (source : DecisionProgram) → RawRefinement source | .machine machine stepBound => ofMachine machine stepBound | .precompose preprocessor decision => precompose (FunctionProgram.RawRefinement.compile preprocessor) (compile decision)'),
    'recursive-decision-compiler');
  require0(compact.includes('rw [hFirstOutput] exact secondRefinement.haltsWithin')
    && compact.includes('rw [hPreprocessorOutput] exact decisionRefinement.haltsWithin'),
  'intermediate-output-transport');
  require0(compact.includes('exact refinement.haltsWithin input (decision.haltsWithin input)'),
    'decider-halting-transport');
  require0(compact.includes('rw [refinement.verdict_eq input (decision.haltsWithin input)] exact decision.accepts_iff input'),
    'decider-acceptance-transport');
  require0(compact.includes('def compileToMachine {language : Language} (decision : PolynomialTimeDecider language) : PolynomialTimeMachine language := toMachine decision (DecisionProgram.RawRefinement.compile decision.program)'),
    'complete-decider-compiler');

  for (const forbidden of [
    'functionProgram_rawCompilable',
    'decisionProgram_rawCompilable',
    'PolynomialTimeVerifier.toRawPairedVerifier',
    'pipelineClasses_equivalent_rawClasses',
  ]) require0(!stripped.includes(forbidden), `unproved-${forbidden}`);

  return failures;
}

test('raw-pipeline contracts are closed, finite, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript, regression, root, and workflow cover the recursive compiler', async () => {
  const [source, audit, regression, root, workflow] = await Promise.all([
    text0(SOURCE_PATH),
    text0(AUDIT_PATH),
    text0(REGRESSION_PATH),
    text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.deepEqual(headPairs0(source), EXPECTED_HEADS.map(([kind, name]) => [kind, name]));
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), EXPECTED_HEADS.map(([, , full]) => full));
  assert.equal(new Set(printed0(audit)).size, EXPECTED_HEADS.length);
  assert.ok(imports0(root).includes('PNP.Concrete.PipelineRefinement'));
  assert.match(regression, /compile_output_eq identityThrice/u);
  assert.match(regression, /compile_verdict_eq nestedReject/u);
  assert.match(regression, /compileToMachine_accepts_iff/u);
  assert.match(workflow, /PNPConcretePipelineRefinementRecursive\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 16/u);
});

test('contracts fail closed under halting, budget, output, verdict, and compiler overclaims', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('source.Halts input →\n    boundedDecide machine', 'True →\n    boundedDecide machine'),
    source.replace('timeBound := stepBound', 'timeBound := .constant 0'),
    source.replace('source.eval input\n', '[]\n'),
    source.replace('source.verdict input\n', '.reject\n'),
    source.replaceAll('PipelineSequentialCompiler.sequentialMachine',
      'PipelineCompiler.pipelineMachine'),
    source.replaceAll('PipelineSequentialCompiler.sequentialRawTimeBound',
      'PipelineCompiler.pipelineRawTimeBound'),
    source.replaceAll('rw [hFirstOutput]\n        exact secondRefinement.haltsWithin',
      'exact secondRefinement.haltsWithin'),
    source.replace('| .compose first second => compose (compile first) (compile second)',
      '| .compose first second => compose (ofMachine immediateAcceptMachine (.constant 0)) (compile second)'),
    source.replace('= source.eval input\n\nnamespace RawRefinement',
      '= source.eval input\n  oracle : BitString → BitString\n\nnamespace RawRefinement'),
    `${source}\naxiom hiddenRefinementOracle : True\n`,
    `${source}\ndef pipelineClasses_equivalent_rawClasses := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('the recursive machine link is earned while the publication gate remains fail-closed', async () => {
  const [statusSource, status, map] = await Promise.all([
    text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.doesNotMatch(statusSource, /'Formal\.ConcreteComplexityMachineLink'/);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), false);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, true);
  assert.equal(map.gate.standardComplexityModelEligible, true);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.equal(map.gate.expectedSourceClosureSha256, null);
});
