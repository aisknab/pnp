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
const COMPLETE_AUDIT_PATH =
  'lean-audit/PNPLockedNANDGlobalCandidatesAxiomAudit.lean';
const MILESTONE_AUDIT_PATH =
  'lean-audit/PNPLockedNANDGlobalBaselineDistinctAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPLockedNANDGlobalBaselineDistinct.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const NAMESPACE = 'PNP.DirectWire.LockedNANDGlobalCandidates';
const REQUIRED_THEOREMS = Object.freeze([
  `${NAMESPACE}.baselineCandidate_outputNonconstant`,
  `${NAMESPACE}.baselineCandidate_outputNotPositiveProjection`,
  `${NAMESPACE}.baselineCandidate_outputPairwiseDistinct`,
  `${NAMESPACE}.baselineCandidate_outputConditions`,
  `${NAMESPACE}.baselineCandidate_referenceMinimum`,
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
  const nonconstant = declarationBlock0(
    source, 'baselineCandidate_outputNonconstant',
  );
  const notProjection = declarationBlock0(
    source, 'baselineCandidate_outputNotPositiveProjection',
  );
  const distinct = declarationBlock0(
    source, 'baselineCandidate_outputPairwiseDistinct',
  );
  const conditions = declarationBlock0(
    source, 'baselineCandidate_outputConditions',
  );
  const minimum = declarationBlock0(
    source, 'baselineCandidate_referenceMinimum',
  );
  if (!/OutputNonconstant \(baselineCandidate circuit\)/u.test(nonconstant)) {
    failures.push('nonconstant-shape');
  }
  if (!/OutputNotPositiveProjection \(baselineCandidate circuit\)/u.test(notProjection)) {
    failures.push('nonprojection-shape');
  }
  if (!/OutputPairwiseDistinct \(baselineCandidate circuit\)/u.test(distinct)) {
    failures.push('pairwise-shape');
  }
  if (!/BaselineOutputConditions \(baselineCandidate circuit\)/u.test(conditions)) {
    failures.push('conditions-shape');
  }
  if (!/referenceMinimum[\s\S]*Implementation\.mk[\s\S]*lockedBaselineCount circuit\.program[\s\S]*baselineCandidate circuit[\s\S]*=\s*lockedBaselineCount circuit\.program\s*:=/u.test(minimum)) {
    failures.push('minimum-shape');
  }
  return failures;
}

test('global baseline conditions are constructive and have the exact public shape', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateTheoremShape0(source), []);
  assert.match(source, /private theorem rawBaseline_conditions/u);
  assert.match(source, /private theorem rawBaselineMacro_anchorIrrelevant/u);
  assert.match(source, /private theorem rawBaselinePrefix_anchorEssential/u);
  assert.match(source, /private theorem essential_irrelevant_distinct/u);
});

test('complete and milestone axiom transcripts cover the reviewed declarations exactly', async () => {
  const sourceDeclarations = declarations0(await text0(SOURCE_PATH));
  const completePrinted = printed0(await text0(COMPLETE_AUDIT_PATH));
  const milestonePrinted = printed0(await text0(MILESTONE_AUDIT_PATH));
  assert.equal(sourceDeclarations.length, 71);
  assert.deepEqual(completePrinted, sourceDeclarations);
  assert.equal(new Set(completePrinted).size, 71);
  assert.deepEqual(milestonePrinted, REQUIRED_THEOREMS);
});

test('compiled closure of all five milestone theorems excludes choice and project axioms', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  for (const name of REQUIRED_THEOREMS) {
    const row = rows.get(name);
    assert.notEqual(row, undefined, name);
    assert.deepEqual(row.axioms, ['Quot.sound', 'propext'], name);
  }
});

test('regression covers semantic conditions and exact minima on distinct source forms', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'baselineCandidate_outputNonconstant',
    'baselineCandidate_outputNotPositiveProjection',
    'baselineCandidate_outputPairwiseDistinct',
    'baselineCandidate_outputConditions',
    'baselineCandidate_referenceMinimum',
    'Implementation.mk 42',
    'Implementation.mk 28',
    '.input',
    '.constant false',
  ]) assert.match(regression,
    new RegExp(token.replaceAll(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'));
  assert.doesNotMatch(regression, /\b(?:native_decide|sorry|admit)\b/u);
});

test('status and publication credit only BaselineDistinct and retain the remaining boundary', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  assert.equal(status.leanLockedNANDGlobalBaselineDistinctFormalized, true);
  assert.equal(
    status.leanLockedNANDGlobalBaselineDistinctAxiomAuditPassed, true,
  );
  assert.equal(
    status.leanLockedNANDGlobalBaselineDistinctAuditedDeclarationCount, 5,
  );
  assert.deepEqual(status.leanLockedNANDThresholdMissingInstantiationInventory, []);
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
  assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'locked-nand-global-baseline-distinct',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone.requiredTheorems, REQUIRED_THEOREMS);
});

test('milestone documentation records the mechanically generated release evidence', async () => {
  const docs = (await text0(
    'docs/lean_locked_nand_global_baseline_distinct.md',
  )).replaceAll(/\s+/gu, ' ');
  for (const token of [
    'PNP-LEAN-THEOREM-INVENTORY-2026-07-27-86',
    '12,245 declarations',
    '7,158 theorems',
    '3,676 assumption-free theorems',
    '4,997 excluded private declarations',
    '1,968 reviewed milestone candidates',
    '33ceee3aa55116581d0c6b9790a35c046832076b168e77116e71bb8573ec3ea1',
    '01b522a560680c69c52c988a0c08c25483d12f5e53de72ff1d8106ae4313a738',
    'PNP-FORMAL-PUBLICATION-MAP-2026-07-27-86',
    '66 milestones',
    '63 are earned',
    '4f8e3bfd7f028ae17d2d84eef1876ad2e3fc68faf9ca383940c35bd6f0a0a529',
    'abf11a2bfcc536c0ba5a509575bed8f6d0cc7ecb1df01f9a079d37e3dc7d8200',
    'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-27-86',
    '06d77025ac41dda41d748f43080ffcf9ebd56b606e0d1a1d0a0c4d7c32df9569',
    'PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-27-86',
    '63-page',
    '9991dd5fcc9fc8da5ba1161434af216b23735b6f379fee9fa6cdd28c2227d4f3',
  ]) assert.equal(docs.includes(token), true, token);
});

test('hostile mutations revoke theorem, closure, transcript, and overclaim credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(source.replace(
    'theorem baselineCandidate_outputConditions',
    'theorem removedBaselineCandidate_outputConditions',
  )).includes('missing:baselineCandidate_outputConditions'), true);
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
  assert.equal(validateTheoremShape0(source.replace(
    'OutputPairwiseDistinct (baselineCandidate circuit)',
    'OutputPairwiseDistinct equalityDirect',
  )).includes('pairwise-shape'), true);
  const minimumBlock = declarationBlock0(
    source, 'baselineCandidate_referenceMinimum',
  );
  assert.equal(validateTheoremShape0(source.replace(
    minimumBlock,
    minimumBlock.replace(
      'lockedBaselineCount circuit.program := by',
      'lockedBaselineCount circuit.program + 1 := by',
    ),
  )).includes('minimum-shape'), true);
  const completePrinted = printed0(await text0(COMPLETE_AUDIT_PATH));
  assert.notDeepEqual(
    declarations0(`${source}\ntheorem extra : True := True.intro\n`),
    completePrinted,
  );
  assert.notDeepEqual(
    printed0(await text0(MILESTONE_AUDIT_PATH)).slice(0, -1),
    REQUIRED_THEOREMS,
  );
});
