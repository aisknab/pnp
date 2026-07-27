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
const SOURCE_PATH = 'lean/PNP/LockedNANDGlobalCandidates.lean';
const AUDIT_PATH = 'lean-audit/PNPLockedNANDGlobalCandidatesAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPLockedNANDGlobalCandidates.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const NAMESPACE = 'PNP.DirectWire.LockedNANDGlobalCandidates';
const IMPORTS = Object.freeze([
  'PNP.LockedNANDCarrierTrace',
  'PNP.LockedNANDThresholdBoundary',
  'PNP.NANDComposition',
]);
const REQUIRED = Object.freeze([
  'def flattenCarrier',
  'def unflattenCarrier',
  'theorem unflatten_flatten',
  'theorem flatten_unflatten',
  'def restrictCarrier',
  'theorem restrictCarrier_snoc_restrict',
  'def sourceMacroGateCount',
  'theorem sourceMacroGateCount_eq_weighted_occurrenceCounts',
  'def macroGateCount',
  'theorem macroGateCount_report_formula',
  'def nonemptyPrefixCandidate',
  'theorem nonemptyPrefixCandidate_semantics',
  'def circuitPrefixCandidate',
  'theorem circuitPrefixCandidate_semantics',
  'def rawBaselineGateCount',
  'theorem rawBaselineGateCount_eq_lockedBaselineCount',
  'def baselineCandidate',
  'theorem baselineCandidate_size',
  'theorem baselinePrefixSource_semantics',
  'def fullCandidate',
  'theorem fullCandidate_size',
  'theorem fullCandidate_initial_semantics',
  'theorem fullCandidate_final_semantics',
  'theorem fullCandidate_final_semantics_flatten',
  'theorem baselineCandidate_no_internal_constants',
  'theorem fullCandidate_no_internal_constants',
  'def setFinalLockValue',
  'theorem baselineCandidate_finalLock_irrelevant',
]);
const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.macroGateCount_report_formula`,
  `${NAMESPACE}.nonemptyPrefixCandidate_semantics`,
  `${NAMESPACE}.rawBaselineGateCount_eq_lockedBaselineCount`,
  `${NAMESPACE}.baselineCandidate_size`,
  `${NAMESPACE}.baselinePrefixSource_semantics`,
  `${NAMESPACE}.fullCandidate_size`,
  `${NAMESPACE}.fullCandidate_initial_semantics`,
  `${NAMESPACE}.fullCandidate_final_semantics`,
  `${NAMESPACE}.baselineCandidate_no_internal_constants`,
  `${NAMESPACE}.fullCandidate_no_internal_constants`,
  `${NAMESPACE}.baselineCandidate_finalLock_irrelevant`,
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

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(IMPORTS)) failures.push('closed-import');
  if (!/namespace PNP\s+[\s\S]*namespace DirectWire\s+[\s\S]*namespace LockedNANDGlobalCandidates/u.test(source)) {
    failures.push('namespace');
  }
  for (const required of REQUIRED) {
    if (!source.includes(required)) failures.push(`missing:${required}`);
  }
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|sorry|admit)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/(?:def|theorem)\s+(?:lockedNANDThreshold|p_eq_np|polynomialBuilder)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function validateAssembly0(source) {
  const failures = [];
  const baseline = declarationBlock0(source, 'baselineCandidate');
  const full = declarationBlock0(source, 'fullCandidate');
  const finalSemantics = declarationBlock0(source, 'fullCandidate_final_semantics');
  const isolation = declarationBlock0(source, 'baselineCandidate_finalLock_irrelevant');
  if (!/def baselineCandidate[\s\S]*Candidate \(carrierWidth inputs circuit\.gateCount\)[\s\S]*\(lockedBaselineCount circuit\.program\)[\s\S]*\(lockedBaselineCount circuit\.program\)/u.test(baseline)) {
    failures.push('baseline-dimensions');
  }
  if (!/def fullCandidate[\s\S]*lockedBaselineCount circuit\.program \+ 4[\s\S]*lockedBaselineCount circuit\.program \+ 1/u.test(full)) {
    failures.push('full-dimensions');
  }
  if (!/theorem fullCandidate_final_semantics[\s\S]*finalConjunction4[\s\S]*finalLockSlot[\s\S]*tracePredicate[\s\S]*traceSlot/u.test(finalSemantics)) {
    failures.push('final-semantics');
  }
  if (!/theorem baselineCandidate_finalLock_irrelevant[\s\S]*setFinalLockValue input leftValue[\s\S]*setFinalLockValue input rightValue/u.test(isolation)) {
    failures.push('final-lock-isolation');
  }
  return failures;
}

test('global candidate source is closed, constructive, and narrowly imported', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateAssembly0(source), []);
});

test('axiom transcript covers all 64 public declarations exactly once', async () => {
  const expected = declarations0(await text0(SOURCE_PATH));
  const printed = printed0(await text0(AUDIT_PATH));
  assert.equal(expected.length, 64);
  assert.deepEqual(printed, expected);
  assert.equal(new Set(printed).size, 64);
});

test('compiled closure of every audited declaration excludes project axioms and Classical.choice', async () => {
  const sourceNames = declarations0(await text0(SOURCE_PATH));
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  for (const name of sourceNames) {
    const row = rows.get(name);
    assert.notEqual(row, undefined, name);
    assert.equal(row.axioms.every((axiom) => ['propext', 'Quot.sound'].includes(axiom)),
      true, `${name}: ${row.axioms.join(', ')}`);
  }
});

test('carrier flattening and restriction are exact typed transports', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /def flattenCarrier[\s\S]*match decodeCarrierSlot slot with/u);
  assert.match(source, /theorem unflatten_flatten[\s\S]*unflattenCarrier \(flattenCarrier valuation\) = valuation/u);
  assert.match(source, /theorem flatten_unflatten[\s\S]*flattenCarrier \(unflattenCarrier valuation\) = valuation/u);
  assert.match(source, /def restrictCarrier[\s\S]*smaller ≤ larger[\s\S]*CarrierValuation inputs smaller/u);
  assert.match(source, /theorem restrictCarrier_snoc_restrict/u);
  assert.doesNotMatch(source, /(?:flatten|restrict)(?:Certificate|Digest|Claim|Flag)\s*:/u);
});

test('source macros and the nonempty prefix are assembled with exact report counts', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /def sourceMacroGateCount[\s\S]*\.input _ => 10[\s\S]*\.constant false => 3[\s\S]*\.constant true => 2[\s\S]*\.gate _ => 10/u);
  assert.match(source, /theorem macroGateCount_report_formula[\s\S]*18 \* gates[\s\S]*10 \* program\.sourceCounts\.equality[\s\S]*3 \* program\.sourceCounts\.zero[\s\S]*2 \* program\.sourceCounts\.one/u);
  assert.match(source, /def nonemptyPrefixCandidate \(tailChecks : Nat\)[\s\S]*Candidate \(tailChecks \+ 1\) \(2 \* tailChecks\) 1/u);
  assert.match(source, /theorem nonemptyPrefixCandidate_semantics[\s\S]*prefixConjunction \(List\.ofFn input\)/u);
  assert.match(source, /def checkTailCount[\s\S]*3 \* circuit\.gateCount - 1/u);
});

test('baseline and full candidates have exact square and plus-four/plus-one dimensions', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /def baselineCandidate[\s\S]*Candidate \(carrierWidth inputs circuit\.gateCount\)[\s\S]*\(lockedBaselineCount circuit\.program\)[\s\S]*\(lockedBaselineCount circuit\.program\)/u);
  assert.match(source, /theorem rawBaselineGateCount_eq_lockedBaselineCount[\s\S]*rawBaselineGateCount circuit =[\s\S]*lockedBaselineCount circuit\.program/u);
  assert.match(source, /def fullCandidate[\s\S]*lockedBaselineCount circuit\.program \+ 4[\s\S]*lockedBaselineCount circuit\.program \+ 1/u);
  assert.match(source, /theorem fullCandidate_initial_semantics[\s\S]*baselineOutputEmbedding output[\s\S]*baselineCandidate circuit/u);
  assert.doesNotMatch(source, /Candidate [^\n]*\(lockedBaselineCount circuit\.program \+ [^4\n]\)/u);
});

test('final semantics are the manuscript conjunction while the baseline excludes z', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /theorem fullCandidate_final_semantics[\s\S]*finalConjunction4[\s\S]*finalLockSlot[\s\S]*tracePredicate[\s\S]*traceSlot/u);
  assert.match(source, /theorem fullCandidate_final_semantics_conjunction[\s\S]*finalLockSlot[\s\S]*&&[\s\S]*tracePredicate[\s\S]*&&[\s\S]*traceSlot/u);
  assert.match(source, /theorem baselineCandidate_finalLock_irrelevant[\s\S]*setFinalLockValue input leftValue[\s\S]*setFinalLockValue input rightValue/u);
  assert.match(source, /theorem baselineCandidate_no_internal_constants[\s\S]*hasNoConstant = true/u);
  assert.match(source, /theorem fullCandidate_no_internal_constants[\s\S]*hasNoConstant = true/u);
});

test('regression exercises constants, multiple circuit sizes, both final branches, and z isolation', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'unflatten_flatten',
    'flatten_unflatten',
    'sourceMacroGateCount',
    'macroGateCount negationProgram = 38',
    'macroGateCount constantTrueProgram = 24',
    'rawBaselineGateCount negationCircuit = 42',
    'rawBaselineGateCount constantTrueCircuit = 28',
    'nonemptyPrefixCandidate_semantics',
    'circuitPrefixCandidate_size',
    'baselineCandidate_size',
    'fullCandidate_size',
    'fullCandidate_initial_semantics',
    'fullCandidate_final_semantics_flatten',
    '= true',
    '= false',
    'baselineCandidate_no_internal_constants',
    'fullCandidate_no_internal_constants',
    'baselineCandidate_finalLock_irrelevant',
  ]) assert.match(regression, new RegExp(token.replaceAll(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'));
  assert.doesNotMatch(regression, /\b(?:native_decide|sorry|admit)\b/u);
});

test('documentation and status credit assembly without claiming the missing boundary premises', async () => {
  const docs = `${await text0('docs/lean_locked_nand_global_candidates.md')}\n${await text0('docs/FORMAL_RECONSTRUCTION.md')}`;
  assert.match(docs, /Section 17/iu);
  assert.match(docs, /legacy manuscript/iu);
  assert.match(docs, /B\s*\+\s*4/iu);
  assert.match(docs, /B\s*\+\s*1/iu);
  assert.match(docs, /BaselineDistinct/iu);
  assert.match(docs, /polynomial builder/iu);

  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanLockedNANDGlobalCandidateAssemblyFormalized',
    'leanLockedNANDGlobalBaselineCandidateFormalized',
    'leanLockedNANDFullCandidateFormalized',
    'leanLockedNANDGlobalCandidateAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanLockedNANDGlobalCandidateAuditedDeclarationCount, 64);
  assert.equal(status.leanLockedNANDGlobalCandidateScope,
    'arbitrary-finite-topological-nand-circuits-exact-baseline-and-four-gate-extension');
  for (const field of [
    'leanLockedNANDThresholdBoundaryPremisesInstantiated',
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDPolynomialBuilderFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);

  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'locked-nand-global-candidate-assembly',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
});

test('hostile mutations revoke source, transcript, count, isolation, and theorem-shape credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(`import PNP.LockedNAND\n${source}`).includes('closed-import'), true);
  assert.equal(validateSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(`${source}\n#eval 1 + 1\n`).includes('host-evaluation'), true);
  assert.equal(validateSource0(`${source}\ndef hostLookup := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateSource0(`${source}\ntheorem lockedNANDThreshold : True := True.intro\n`).includes('overclaim'), true);
  assert.equal(validateAssembly0(source.replaceAll(
    'lockedBaselineCount circuit.program + 4',
    'lockedBaselineCount circuit.program + 5',
  )).includes('full-dimensions'), true);
  assert.equal(validateAssembly0(source.replace(
    'lockedBaselineCount circuit.program + 1',
    'lockedBaselineCount circuit.program + 2',
  )).includes('full-dimensions'), true);
  assert.equal(validateAssembly0(source.replace(
    'theorem fullCandidate_final_semantics {inputs : Nat}',
    'theorem removedFinalSemantics {inputs : Nat}',
  )).includes('final-semantics'), true);
  assert.equal(validateAssembly0(source.replace(
    'theorem baselineCandidate_finalLock_irrelevant',
    'theorem removedFinalLockIrrelevance',
  )).includes('final-lock-isolation'), true);
  const printed = printed0(await text0(AUDIT_PATH));
  assert.notDeepEqual(declarations0(`${source}\ntheorem extra : True := True.intro\n`), printed);
  assert.notDeepEqual(printed.slice(0, -1), declarations0(source));
});
