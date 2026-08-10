import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH =
  'lean/PNP/LockedNANDGlobalUnsatisfiableFinalZero.lean';
const AUDIT_PATH =
  'lean-audit/PNPLockedNANDGlobalUnsatisfiableFinalZeroAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPLockedNANDGlobalUnsatisfiableFinalZero.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH =
  'docs/lean_locked_nand_global_unsatisfiable_final_zero.md';
const NAMESPACE = 'PNP.DirectWire.LockedNANDGlobalCandidates';
const REQUIRED_THEOREMS = Object.freeze([
  `${NAMESPACE}.fullCandidate_final_eq_false_of_unsatisfiable`,
  `${NAMESPACE}.fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `${NAMESPACE}.${head.name}`);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  for (const name of REQUIRED_THEOREMS.map((entry) => entry.split('.').at(-1))) {
    if (!new RegExp(`theorem ${name}\\b`, 'u').test(stripped)) {
      failures.push(`missing:${name}`);
    }
  }
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|sorry|admit)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) {
    failures.push('assumption-declaration');
  }
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/(?:def|theorem)\s+(?:lockedNANDThreshold|p_eq_np|polynomialBuilder)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateTheoremShape0(source) {
  const failures = [];
  const finalZero = declarationBlock0(
    source, 'fullCandidate_final_eq_false_of_unsatisfiable',
  );
  const exactMinimum = declarationBlock0(
    source,
    'fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable',
  );
  if (!/\(notSatisfiable\s*:\s*¬ circuit\.Satisfiable\)[\s\S]*∀ input,[\s\S]*\(fullCandidate circuit\)\.semantics input[\s\S]*conditionalFinalOutput[\s\S]*lockedBaselineCount circuit\.program[\s\S]*=\s*false\s*:=/u.test(finalZero)) {
    failures.push('whole-carrier-final-zero-shape');
  }
  if (!/referenceMinimum[\s\S]*Implementation\.mk[\s\S]*lockedBaselineCount circuit\.program \+ 4[\s\S]*fullCandidate circuit[\s\S]*=\s*lockedBaselineCount circuit\.program\s*:=/u.test(exactMinimum)) {
    failures.push('unsatisfiable-minimum-shape');
  }
  if (!/\(notSatisfiable\s*:\s*¬ circuit\.Satisfiable\)/u.test(exactMinimum)) {
    failures.push('minimum-unsatisfiable-premise');
  }
  return failures;
}

test('unsatisfiable final-zero source has the exact whole-carrier public shape', async () => {
  const source = await text0(SOURCE_PATH);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, ['PNP.LockedNANDGlobalCandidates']);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateTheoremShape0(source), []);
  assert.match(source, /private theorem projectedFullCandidate_equivalent_baseline/u);
  assert.match(source, /private theorem projectedFullCandidate_conditions/u);
  assert.match(
    source,
    /private theorem appendZeroFinalOutput_equivalent_fullCandidate_of_unsatisfiable/u,
  );
  assert.doesNotMatch(
    source,
    /if\s+(?:h\s*:?\s*)?circuit\.Satisfiable/u,
  );
});

test('axiom transcript covers exactly the two public milestone theorems', async () => {
  const sourceDeclarations = declarations0(await text0(SOURCE_PATH));
  assert.deepEqual(sourceDeclarations, REQUIRED_THEOREMS);
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(
    [...audit.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
      .map((match) => match[1]),
    ['PNP.LockedNANDGlobalUnsatisfiableFinalZero'],
  );
  const printed = printed0(audit);
  assert.deepEqual(printed, REQUIRED_THEOREMS);
  assert.equal(new Set(printed).size, 2);
  assert.match(
    await text0('lean/PNP.lean'),
    /^import PNP\.LockedNANDGlobalUnsatisfiableFinalZero$/mu,
  );
});

test('compiled closure of both milestone theorems excludes choice and project axioms', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(
    inventory.declarations.map((entry) => [entry.name, entry]),
  );
  for (const name of REQUIRED_THEOREMS) {
    const row = rows.get(name);
    assert.notEqual(row, undefined, name);
    assert.deepEqual(row.axioms, ['Quot.sound', 'propext'], name);
  }
});

test('regression covers unsatisfiable circuits, hostile carriers, exact minimum, and satisfiable separation', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'constantFalseCircuit_not_satisfiable',
    'contradictionCircuit_not_satisfiable',
    'allFalseCarrier',
    'allTrueCarrier',
    'setFinalLockValue input true',
    'fullCandidate_final_eq_false_of_unsatisfiable',
    'fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable',
    'constantTrueCircuit_satisfiable',
    'coherentExtension constantTrueProgram zeroInput',
    '= true',
  ]) {
    assert.match(
      regression,
      new RegExp(token.replaceAll(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'),
    );
  }
  assert.doesNotMatch(regression, /\b(?:native_decide|sorry|admit)\b/u);
});

test('status credits only the unsatisfiable branch and leaves downstream claims fail-closed', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  assert.equal(status.leanLockedNANDUnsatisfiableFinalZeroFormalized, true);
  assert.equal(
    status.leanLockedNANDUnsatisfiableFinalZeroAxiomAuditPassed,
    true,
  );
  assert.equal(
    status.leanLockedNANDUnsatisfiableFinalZeroAuditedDeclarationCount,
    2,
  );
  assert.deepEqual(
    status.leanLockedNANDThresholdMissingInstantiationInventory,
    [],
  );
  for (const field of [
    'leanLockedNANDThresholdBoundaryPremisesInstantiated',
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDGlobalSemanticThresholdFormalized',
  ]) assert.equal(status[field], true, field);
  for (const field of [
    'leanLockedNANDPolynomialBuilderFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'locked-nand-global-unsatisfiable-final-zero',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone.requiredTheorems, REQUIRED_THEOREMS);
});

test('milestone documentation records mechanically generated release evidence', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  for (const token of [
    inventory.coordinate,
    status.coordinate,
    'whole carrier',
    'satisfiableFinalConditions',
    'Classical.choice',
    'Quot.sound',
    'propext',
    '63-page',
    '402,956-byte',
    '9d0743f86dd9da269d6244a543a1c4a21a2ede2b7cfdc5508875b17c7ae8f4ad',
  ]) assert.equal(docs.includes(token), true, token);
});

test('hostile mutations revoke whole-carrier, closure, transcript, and overclaim credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(source.replace(
    'theorem fullCandidate_final_eq_false_of_unsatisfiable',
    'theorem removed_fullCandidate_final_eq_false_of_unsatisfiable',
  )).includes('missing:fullCandidate_final_eq_false_of_unsatisfiable'), true);
  assert.equal(validateSource0(`${source}\naxiom hidden : True\n`)
    .includes('assumption-declaration'), true);
  assert.equal(validateSource0(`${source}\nexample : True := True.intro\n`)
    .includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(`${source}\ntheorem hidden : True := by native_decide\n`)
    .includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(`${source}\n#eval 1 + 1\n`)
    .includes('host-evaluation'), true);
  assert.equal(validateSource0(`${source}\ndef callerCertificate := true\n`)
    .includes('caller-or-host-certificate'), true);
  assert.equal(validateSource0(`${source}\ntheorem lockedNANDThreshold : True := True.intro\n`)
    .includes('overclaim'), true);

  const finalBlock = declarationBlock0(
    source, 'fullCandidate_final_eq_false_of_unsatisfiable',
  );
  assert.equal(validateTheoremShape0(source.replace(
    finalBlock,
    finalBlock.replace('∀ input,', '∃ input,'),
  )).includes('whole-carrier-final-zero-shape'), true);
  assert.equal(validateTheoremShape0(source.replace(
    finalBlock,
    finalBlock.replace(/=\s*false\s*:=/u, '= true :='),
  )).includes('whole-carrier-final-zero-shape'), true);
  assert.equal(validateTheoremShape0(source.replace(
    finalBlock,
    finalBlock.replace(
      '(notSatisfiable : ¬ circuit.Satisfiable)',
      '(notSatisfiable : circuit.Satisfiable)',
    ),
  )).includes('whole-carrier-final-zero-shape'), true);

  const minimumBlock = declarationBlock0(
    source,
    'fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable',
  );
  assert.equal(validateTheoremShape0(source.replace(
    minimumBlock,
    minimumBlock.replace(
      'lockedBaselineCount circuit.program := by',
      'lockedBaselineCount circuit.program + 1 := by',
    ),
  )).includes('unsatisfiable-minimum-shape'), true);
  assert.notDeepEqual(
    declarations0(`${source}\ntheorem extra : True := True.intro\n`),
    REQUIRED_THEOREMS,
  );
  assert.notDeepEqual(
    printed0(await text0(AUDIT_PATH)).slice(0, -1),
    REQUIRED_THEOREMS,
  );
});
