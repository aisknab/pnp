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
const SOURCE_PATH = 'lean/PNP/LockedNANDThresholdBoundary.lean';
const AUDIT_PATH = 'lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean';
const IMPORTS = Object.freeze(['PNP.DirectWireBaseline', 'PNP.NANDSlack']);
const REQUIRED = Object.freeze([
  'def baselineOutputEmbedding',
  'def conditionalFinalOutput',
  'def projectBaselineOutputs',
  'def appendZeroFinalOutput',
  'structure ConditionalFinalOutputSatConditions',
  'structure ConditionalThresholdBoundaryPremises',
  'theorem ConditionalThresholdBoundaryPremises.projectedEquivalentBaseline',
  'theorem ConditionalThresholdBoundaryPremises.projectedBaselineConditions',
  'theorem baselineConditions_with_final',
  'theorem outputCount_le_referenceMinimum',
  'theorem projectedOutputCount_le_referenceMinimum',
  'theorem ConditionalThresholdBoundaryPremises.fullMinimum_ge_baseline',
  'theorem ConditionalThresholdBoundaryPremises.fullResidualSlack_le_four',
  'theorem ConditionalThresholdBoundaryPremises.appendZeroEquivalentFull_of_unsatisfiable',
  'theorem ConditionalThresholdBoundaryPremises.fullMinimum_eq_baseline_of_unsatisfiable',
  'theorem ConditionalThresholdBoundaryPremises.fullMinimum_bounds_of_satisfiable',
  'theorem ConditionalThresholdBoundaryPremises.satisfiable_iff_minimum_ge_succ',
]);
const HOSTILE_REVIEW_LEMMAS = Object.freeze([
  'DirectWireOutputLowerBound',
  'MacroDistinct',
  'TraceEquivalence',
  'ZeroOutputConvention',
  'FinalLockSeparation',
]);
const PREMISE_FIELDS = Object.freeze([
  'baselineCandidate',
  'fullCandidate',
  'baselineConditions',
  'initialOutputsPreserved',
  'unsatisfiableFinalZero',
  'satisfiableFinalConditions',
]);
const MISSING_FIELDS = Object.freeze([]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `PNP.DirectWire.${head.name}`);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function validateSource0(source) {
  const failures = [];
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(IMPORTS)) failures.push('closed-import');
  if (!/namespace PNP\s+[\s\S]*namespace DirectWire/u.test(source)) failures.push('namespace');
  for (const required of REQUIRED) {
    if (!source.includes(required)) failures.push(`missing:${required}`);
  }
  if (/\b(?:Classical|funext|propext|native_decide|sorry|admit)\b/u.test(source)) failures.push('forbidden-shortcut');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasPrivateLeanDeclaration0(source)) failures.push('private-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  return failures;
}

test('conditional threshold boundary source is closed, constructive, and narrowly imported', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('threshold-boundary axiom transcript covers all 32 explicit declarations exactly once', async () => {
  const expected = declarations0(await text0(SOURCE_PATH));
  const printed = printed0(await text0(AUDIT_PATH));
  assert.equal(expected.length, 32);
  assert.deepEqual(printed, expected);
  assert.equal(new Set(printed).size, 32);
});

test('boundary premises store actual typed candidates and semantic proofs', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /structure ConditionalThresholdBoundaryPremises[\s\S]*baselineCandidate : Candidate inputs baseline baseline[\s\S]*fullCandidate : Candidate inputs \(baseline \+ 4\) \(baseline \+ 1\)/u);
  assert.match(source, /baselineConditions : BaselineOutputConditions baselineCandidate/u);
  assert.match(source, /initialOutputsPreserved : ∀ input output,[\s\S]*fullCandidate\.semantics[\s\S]*baselineCandidate\.semantics/u);
  assert.match(source, /unsatisfiableFinalZero : ¬ satisfiable → ∀ input,[\s\S]*= false/u);
  assert.match(source, /satisfiableFinalConditions : satisfiable →[\s\S]*ConditionalFinalOutputSatConditions fullCandidate/u);
  for (const field of PREMISE_FIELDS) assert.match(source, new RegExp(`\\b${field}\\b`, 'u'));
  assert.doesNotMatch(source, /(?:digest|certificateId|proofRef|metadata|trustFlag)\s*:/u);
});

test('semantic branch theorems are conditional on the proof-bearing premises', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /fullMinimum_eq_baseline_of_unsatisfiable[\s\S]*\(notSatisfiable : ¬ satisfiable\)[\s\S]*referenceMinimum premises\.fullImplementation = baseline/u);
  assert.match(source, /fullMinimum_bounds_of_satisfiable[\s\S]*\(isSatisfiable : satisfiable\)[\s\S]*baseline \+ 1 ≤ referenceMinimum premises\.fullImplementation[\s\S]*referenceMinimum premises\.fullImplementation ≤ baseline \+ 4/u);
  assert.match(source, /satisfiable_iff_minimum_ge_succ[\s\S]*\(premises : ConditionalThresholdBoundaryPremises[\s\S]*satisfiable ↔ baseline \+ 1 ≤ referenceMinimum premises\.fullImplementation/u);
  assert.match(source, /appendZeroEquivalentFull_of_unsatisfiable[\s\S]*appendZeroFinalOutput premises\.baselineCandidate/u);
  assert.doesNotMatch(source, /(?:def|theorem)\s+(?:lockedNANDBuilder|lockedNANDThreshold|satReducesToLockedNAND)\b/u);
});

test('residual slack at most four is earned only under the same premises', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /fullMinimum_ge_baseline[\s\S]*baseline ≤ referenceMinimum premises\.fullImplementation/u);
  assert.match(source, /fullResidualSlack_le_four[\s\S]*\(premises : ConditionalThresholdBoundaryPremises[\s\S]*residualSlack premises\.fullImplementation ≤ 4/u);
  assert.doesNotMatch(source, /theorem\s+(?:lockedNANDResidualSlack|allLockedNANDResidualSlack|globalResidualSlack)/u);
});

test('documentation preserves the hostile-review inventory and exact missing instantiations', async () => {
  const docs = `${await text0('docs/lean_locked_nand_threshold_boundary.md')}\n${await text0('docs/FORMAL_RECONSTRUCTION.md')}`;
  for (const lemma of HOSTILE_REVIEW_LEMMAS) assert.match(docs, new RegExp(`\\b${lemma}\\b`, 'u'));
  for (const field of PREMISE_FIELDS) assert.match(docs, new RegExp(`\\b${field}\\b`, 'u'));
  assert.match(docs, /not the report(?:'s)? (?:locked-NAND )?threshold theorem/iu);
  assert.match(docs, /global [`']?BaselineDistinct[\s\S]*(?:formalized|discharged|closes)/iu);
  assert.match(docs, /TraceEquivalence[\s\S]*(?:formalized|discharged)/iu);
  assert.match(docs, /satisfiable final-output (?:law|conditions)[\s\S]*(?:formalized|discharged|closed)/iu);
});

test('status credits the conditional boundary while every global threshold claim stays false', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanLockedNANDConditionalThresholdBoundaryFormalized',
    'leanLockedNANDConditionalResidualSlackAtMostFourFormalized',
    'leanLockedNANDThresholdBoundaryAxiomAuditPassed',
    'leanLockedNANDCarrierLayoutFormalized',
    'leanLockedNANDTraceEquivalenceFormalized',
    'leanLockedNANDCarrierTraceAxiomAuditPassed',
    'leanLockedNANDGlobalCandidateAssemblyFormalized',
    'leanLockedNANDGlobalBaselineCandidateFormalized',
    'leanLockedNANDFullCandidateFormalized',
    'leanLockedNANDGlobalCandidateAxiomAuditPassed',
    'leanLockedNANDGlobalBaselineDistinctFormalized',
    'leanLockedNANDGlobalBaselineDistinctAxiomAuditPassed',
    'leanLockedNANDUnsatisfiableFinalZeroFormalized',
    'leanLockedNANDUnsatisfiableFinalZeroAxiomAuditPassed',
    'leanLockedNANDThresholdBoundaryPremisesInstantiated',
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDSatisfiableFinalConditionsFormalized',
    'leanLockedNANDGlobalSemanticThresholdFormalized',
    'leanLockedNANDGlobalSemanticThresholdAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanLockedNANDCarrierTraceAuditedDeclarationCount, 71);
  assert.equal(status.leanLockedNANDGlobalCandidateAuditedDeclarationCount, 71);
  assert.equal(status.leanLockedNANDThresholdBoundaryScope, 'proof-bearing-typed-candidate-and-semantic-premises-only');
  assert.deepEqual(status.lockedNANDThresholdHostileReviewLemmaInventory, HOSTILE_REVIEW_LEMMAS);
  assert.deepEqual(status.leanLockedNANDThresholdPremiseInventory, PREMISE_FIELDS);
  assert.deepEqual(status.leanLockedNANDThresholdMissingInstantiationInventory, MISSING_FIELDS);
  for (const field of [
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
    'leanLockedNANDPolynomialBuilderFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.satInPConclusionAccepted, false);
  assert.equal(status.pEqualsNPConclusionAccepted, false);
});

test('static audit rejects assumptions, shortcuts, import growth, and transcript drift', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(`import PNP.LockedNAND\n${source}`).includes('closed-import'), true);
  assert.equal(validateSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateSource0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-declaration'), true);
  assert.equal(validateSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(`${source}\ntheorem hidden_propext (a b : Prop) (h : a ↔ b) : a = b := propext h\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(source.replace('structure ConditionalThresholdBoundaryPremises', 'structure RemovedThresholdBoundaryPremises')).some((failure) => failure.includes('ConditionalThresholdBoundaryPremises')), true);
  const printed = printed0(await text0(AUDIT_PATH));
  assert.notDeepEqual(declarations0(`${source}\ntheorem extra : True := True.intro\n`), printed);
  assert.notDeepEqual(printed.slice(0, -1), declarations0(source));
});
