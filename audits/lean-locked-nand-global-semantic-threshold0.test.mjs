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
  'lean/PNP/LockedNANDGlobalSemanticThreshold.lean';
const AUDIT_PATH =
  'lean-audit/PNPLockedNANDGlobalSemanticThresholdAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPLockedNANDGlobalSemanticThreshold.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH =
  'docs/lean_locked_nand_global_semantic_threshold.md';
const NAMESPACE = 'PNP.DirectWire.LockedNANDGlobalCandidates';
const SOURCE_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.fullCandidate_final_nonconstant_of_satisfiable`,
  `${NAMESPACE}.fullCandidate_final_notPositiveProjection_of_satisfiable`,
  `${NAMESPACE}.fullCandidate_final_distinctFromBaseline_of_satisfiable`,
  `${NAMESPACE}.fullCandidate_satisfiableFinalConditions`,
  `${NAMESPACE}.fullCandidateThresholdPremises`,
  `${NAMESPACE}.fullCandidate_referenceMinimum_bounds_of_satisfiable`,
  `${NAMESPACE}.fullCandidate_residualSlack_le_four`,
  `${NAMESPACE}.fullCandidate_satisfiable_iff_referenceMinimum_ge_succ`,
]);
const REQUIRED_NEW_THEOREMS = Object.freeze(
  SOURCE_DECLARATIONS.filter((name) => !name.endsWith(
    '.fullCandidateThresholdPremises',
  )),
);
const MILESTONE_THEOREMS = Object.freeze([
  ...REQUIRED_NEW_THEOREMS,
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
  for (const qualified of SOURCE_DECLARATIONS) {
    const name = qualified.split('.').at(-1);
    const kind = name === 'fullCandidateThresholdPremises'
      ? 'def'
      : 'theorem';
    if (!new RegExp(`${kind} ${name}\\b`, 'u').test(stripped)) {
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
  if (/\bif\s+(?:checked\s*:\s*)?circuit\.Satisfiable\b/u.test(stripped)) {
    failures.push('answer-dependent-candidate');
  }
  return failures;
}

function validateTheoremShape0(source) {
  const failures = [];
  const nonconstant = declarationBlock0(
    source, 'fullCandidate_final_nonconstant_of_satisfiable',
  );
  const notProjection = declarationBlock0(
    source, 'fullCandidate_final_notPositiveProjection_of_satisfiable',
  );
  const distinct = declarationBlock0(
    source, 'fullCandidate_final_distinctFromBaseline_of_satisfiable',
  );
  const conditions = declarationBlock0(
    source, 'fullCandidate_satisfiableFinalConditions',
  );
  const premises = declarationBlock0(
    source, 'fullCandidateThresholdPremises',
  );
  const bounds = declarationBlock0(
    source, 'fullCandidate_referenceMinimum_bounds_of_satisfiable',
  );
  const residual = declarationBlock0(
    source, 'fullCandidate_residualSlack_le_four',
  );
  const threshold = declarationBlock0(
    source, 'fullCandidate_satisfiable_iff_referenceMinimum_ge_succ',
  );
  if (!/\(isSatisfiable\s*:\s*circuit\.Satisfiable\)[\s\S]*OutputNonconstant \(fullCandidate circuit\)[\s\S]*conditionalFinalOutput/u.test(nonconstant)) {
    failures.push('nonconstant-shape');
  }
  if (!/\(isSatisfiable\s*:\s*circuit\.Satisfiable\)[\s\S]*OutputNotPositiveProjection \(fullCandidate circuit\)[\s\S]*conditionalFinalOutput/u.test(notProjection)) {
    failures.push('nonprojection-shape');
  }
  if (!/\(isSatisfiable\s*:\s*circuit\.Satisfiable\)[\s\S]*\(output\s*:\s*Fin \(lockedBaselineCount circuit\.program\)\)[\s\S]*baselineOutputEmbedding output[\s\S]*conditionalFinalOutput/u.test(distinct)) {
    failures.push('baseline-separation-shape');
  }
  if (!/ConditionalFinalOutputSatConditions[\s\S]*\(fullCandidate circuit\)[\s\S]*nonconstant\s*:=[\s\S]*notPositiveProjection\s*:=[\s\S]*distinctFromBaseline\s*:=/u.test(conditions)) {
    failures.push('conditions-package-shape');
  }
  for (const field of [
    'baselineCandidate',
    'fullCandidate',
    'baselineConditions',
    'initialOutputsPreserved',
    'unsatisfiableFinalZero',
    'satisfiableFinalConditions',
  ]) {
    if (!new RegExp(`${field}\\s*:=`, 'u').test(premises)) {
      failures.push(`premises-field:${field}`);
    }
  }
  if (!/ConditionalThresholdBoundaryPremises[\s\S]*circuit\.Satisfiable[\s\S]*carrierWidth inputs circuit\.gateCount[\s\S]*lockedBaselineCount circuit\.program/u.test(premises)) {
    failures.push('premises-type-shape');
  }
  if (!/lockedBaselineCount circuit\.program \+ 1 ≤[\s\S]*referenceMinimum[\s\S]*Implementation\.mk[\s\S]*lockedBaselineCount circuit\.program \+ 4[\s\S]*fullCandidate circuit[\s\S]*∧[\s\S]*referenceMinimum[\s\S]*≤[\s\S]*lockedBaselineCount circuit\.program \+ 4/u.test(bounds)) {
    failures.push('satisfiable-bounds-shape');
  }
  if (!/residualSlack[\s\S]*Implementation\.mk[\s\S]*lockedBaselineCount circuit\.program \+ 4[\s\S]*fullCandidate circuit[\s\S]*≤[\s\S]*4\s*:=/u.test(residual)) {
    failures.push('residual-four-shape');
  }
  if (!/circuit\.Satisfiable\s*↔[\s\S]*lockedBaselineCount circuit\.program \+ 1 ≤[\s\S]*referenceMinimum[\s\S]*Implementation\.mk[\s\S]*lockedBaselineCount circuit\.program \+ 4[\s\S]*fullCandidate circuit/u.test(threshold)) {
    failures.push('threshold-iff-shape');
  }
  return failures;
}

test('semantic-threshold source has the exact answer-independent public surface', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(
    [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
      .map((match) => match[1]),
    ['PNP.LockedNANDGlobalUnsatisfiableFinalZero'],
  );
  assert.deepEqual(declarations0(source), SOURCE_DECLARATIONS);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateTheoremShape0(source), []);
  assert.match(source, /private def withFinalLock/u);
  assert.match(source, /private theorem tracePredicate_withFinalLock/u);
  assert.match(source, /private theorem flattenCarrier_withFinalLock/u);
  assert.match(source, /private def anyTrue/u);
  assert.match(source, /private def circuitSatisfiableBool/u);
  assert.match(source, /allBoolTuples inputs/u);
  assert.match(source, /private def circuitSatisfiableDecidable/u);
  assert.doesNotMatch(source, /if\s+(?:h\s*:\s*)?circuit\.Satisfiable/u);
});

test('axiom transcript covers exactly all eight public declarations', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(
    [...audit.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
      .map((match) => match[1]),
    ['PNP.LockedNANDGlobalSemanticThreshold'],
  );
  assert.deepEqual(printed0(audit), SOURCE_DECLARATIONS);
  assert.equal(new Set(printed0(audit)).size, 8);
  assert.match(
    await text0('lean/PNP.lean'),
    /^import PNP\.LockedNANDGlobalSemanticThreshold$/mu,
  );
});

test('compiled closure of all eight declarations is Lean-standard only', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(
    inventory.declarations.map((entry) => [entry.name, entry]),
  );
  for (const name of SOURCE_DECLARATIONS) {
    const row = rows.get(name);
    assert.notEqual(row, undefined, name);
    assert.deepEqual(row.axioms, ['Quot.sound', 'propext'], name);
  }
});

test('regression covers both semantic branches and every public result', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'constantTrueCircuit_satisfiable',
    'negationCircuit_satisfiable',
    'constantFalseCircuit_not_satisfiable',
    'fullCandidate_final_nonconstant_of_satisfiable',
    'fullCandidate_final_notPositiveProjection_of_satisfiable',
    'finalLockSlot',
    'primarySlot',
    'fullCandidate_final_distinctFromBaseline_of_satisfiable',
    'fullCandidate_satisfiableFinalConditions',
    'fullCandidateThresholdPremises',
    'fullCandidate_referenceMinimum_bounds_of_satisfiable',
    'fullCandidate_residualSlack_le_four',
    'fullCandidate_satisfiable_iff_referenceMinimum_ge_succ',
    'fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable',
  ]) {
    assert.match(
      regression,
      new RegExp(token.replaceAll(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'),
    );
  }
  assert.doesNotMatch(
    regression,
    /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u,
  );
});

test('status earns the typed semantic threshold without widening the project claim', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  for (const field of [
    'leanLockedNANDThresholdBoundaryPremisesInstantiated',
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDSatisfiableFinalConditionsFormalized',
    'leanLockedNANDGlobalSemanticThresholdFormalized',
    'leanLockedNANDGlobalSemanticThresholdAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanLockedNANDGlobalSemanticThresholdAuditedDeclarationCount,
    8,
  );
  assert.equal(
    status.leanLockedNANDGlobalSemanticThresholdScope,
    'arbitrary-finite-topological-nand-circuits-complete-six-field-premises-and-typed-semantic-threshold',
  );
  assert.deepEqual(
    status.leanLockedNANDThresholdMissingInstantiationInventory,
    [],
  );
  for (const field of [
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
  ]) assert.equal(status[field], false, field);
  for (const field of [
    'leanLockedNANDPolynomialBuilderFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'locked-nand-global-semantic-threshold',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
});

test('milestone documentation records mechanically generated release evidence', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    'canonical inventory',
    'publication map',
    'status payload',
    'report artifacts',
    'seven new theorem types',
    'exact unsatisfiable-minimum theorem',
    'answer-independent',
    'all six',
    'Classical.choice',
    'Quot.sound',
    'propext',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('hostile mutations revoke semantic, closure, transcript, and overclaim credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(source.replace(
    'theorem fullCandidate_satisfiableFinalConditions',
    'theorem removed_fullCandidate_satisfiableFinalConditions',
  )).includes('missing:fullCandidate_satisfiableFinalConditions'), true);
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
  assert.equal(validateSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`)
    .includes('overclaim'), true);
  assert.equal(validateSource0(`${source}\ndef answerDependent (circuit : Circuit 0) := if circuit.Satisfiable then true else false\n`)
    .includes('answer-dependent-candidate'), true);

  assert.equal(validateTheoremShape0(source.replace(
    'OutputNonconstant (fullCandidate circuit)',
    'OutputNonconstant (baselineCandidate circuit)',
  )).includes('nonconstant-shape'), true);
  assert.equal(validateTheoremShape0(source.replace(
    'OutputNotPositiveProjection (fullCandidate circuit)',
    'OutputNotPositiveProjection (baselineCandidate circuit)',
  )).includes('nonprojection-shape'), true);
  const conditions = declarationBlock0(
    source, 'fullCandidate_satisfiableFinalConditions',
  );
  assert.equal(validateTheoremShape0(source.replace(
    conditions,
    conditions.replace('distinctFromBaseline :=', 'removedField :='),
  )).includes('conditions-package-shape'), true);
  const premises = declarationBlock0(
    source, 'fullCandidateThresholdPremises',
  );
  assert.equal(validateTheoremShape0(source.replace(
    premises,
    premises.replace('satisfiableFinalConditions :=', 'removedField :='),
  )).includes('premises-field:satisfiableFinalConditions'), true);
  const threshold = declarationBlock0(
    source, 'fullCandidate_satisfiable_iff_referenceMinimum_ge_succ',
  );
  assert.equal(validateTheoremShape0(source.replace(
    threshold,
    threshold.replace(
      'lockedBaselineCount circuit.program + 1 ≤',
      'lockedBaselineCount circuit.program + 2 ≤',
    ),
  )).includes('threshold-iff-shape'), true);
  assert.notDeepEqual(
    declarations0(`${source}\ntheorem extra : True := True.intro\n`),
    SOURCE_DECLARATIONS,
  );
  assert.notDeepEqual(
    printed0(await text0(AUDIT_PATH)).slice(0, -1),
    SOURCE_DECLARATIONS,
  );
});
