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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketChargeSurplus.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketChargeSurplusAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketChargeSurplus.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_packet_charge_surplus.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketChargeSurplus.matchedWeight_eq`,
  `${NAMESPACE}.TerminalPacketChargeSurplus.supportWeight_eq_matched_add_unmatched`,
  `${NAMESPACE}.TerminalPacketChargeSurplus.replacementWeight_eq_matched`,
  `${NAMESPACE}.TerminalPacketChargeSurplus.unmatchedWeight_pos`,
  `${NAMESPACE}.TerminalPacketChargeSurplus.replacementLength_lt_supportLength`,
  `${NAMESPACE}.TerminalPacketChargeSurplus.replacementWeight_lt_supportWeight`,
  `${NAMESPACE}.TerminalPacketChargeSurplusRealization.strictEquivalentGain`,
  `${NAMESPACE}.TerminalPacketChargeSurplusRealization.strictResidualDescent`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
}

function auditedDeclarations0(source) {
  return declarationNames0(source).map((name) => `${NAMESPACE}.${name}`);
}

function semanticText0(source) {
  return source.replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function requireTokens0(failures, block, category, tokens) {
  for (const token of tokens) {
    if (!block.includes(token)) failures.push(category);
  }
}

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|chargeSurplusComplete|unconditionalZeroSlack)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketSelectorGainCoverage',
  ]);

  const surplus = declarationBlock0(source, 'TerminalPacketChargeSurplus');
  requireTokens0(failures, surplus, 'exact-occurrence-injection', [
    'pairing : List (SupportCharge × ReplacementCharge)',
    'unmatched : List SupportCharge',
    'supportExact : support.Perm (pairing.map Prod.fst ++ unmatched)',
    'replacementExact : replacement.Perm (pairing.map Prod.snd)',
    'weightPreserved : ∀ entry, entry ∈ pairing ->',
    'replacementWeight entry.2 = supportWeight entry.1',
    'positiveUnmatched : ∃ charge, charge ∈ unmatched ∧ 0 < supportWeight charge',
  ]);

  const matched = declarationBlock0(source,
    'TerminalPacketChargeSurplus.matchedWeight_eq');
  requireTokens0(failures, matched, 'weight-preserving-pairing', [
    'terminalV53_sum_congr surplus.pairing',
    'surplus.weightPreserved',
  ]);

  const unmatched = declarationBlock0(source,
    'TerminalPacketChargeSurplus.unmatchedWeight_pos');
  requireTokens0(failures, unmatched, 'positive-unmatched-weight', [
    'surplus.positiveUnmatched',
    'terminalV53_term_le_sum surplus.unmatched supportWeight charge member',
  ]);

  const lengthStrict = declarationBlock0(source,
    'TerminalPacketChargeSurplus.replacementLength_lt_supportLength');
  requireTokens0(failures, lengthStrict, 'strict-occurrence-injection', [
    'surplus.replacementExact.length_eq',
    'surplus.supportExact.length_eq',
    'Nat.lt_add_of_pos_right unmatchedLengthPositive',
    'replacement.length < support.length',
  ]);

  const weightStrict = declarationBlock0(source,
    'TerminalPacketChargeSurplus.replacementWeight_lt_supportWeight');
  requireTokens0(failures, weightStrict, 'strict-charge-surplus', [
    'surplus.replacementWeight_eq_matched',
    'surplus.matchedWeight_eq',
    'Nat.lt_add_of_pos_right surplus.unmatchedWeight_pos',
    'surplus.supportWeight_eq_matched_add_unmatched.symm',
    '(replacement.map replacementWeight).sum <',
    '(support.map supportWeight).sum',
  ]);

  const realization = declarationBlock0(source,
    'TerminalPacketChargeSurplusRealization');
  requireTokens0(failures, realization, 'exact-gate-and-semantic-realization', [
    'surplus : TerminalPacketChargeSurplus support replacement',
    '(support.map supportWeight).sum = current.gateCount',
    '(replacement.map replacementWeight).sum = next.gateCount',
    'semanticsPreserved : Equivalent next.candidate.program',
  ]);
  if (/\b(?:smaller|StrictEquivalentGain)\b/u.test(
    stripLeanCommentsAndStrings0(realization))) {
    failures.push('assumed-strictness');
  }

  const gain = declarationBlock0(source,
    'TerminalPacketChargeSurplusRealization.strictEquivalentGain');
  requireTokens0(failures, gain, 'derived-strict-equivalent-gain', [
    'StrictEquivalentGain current next',
    'realization.semanticsPreserved',
    'realization.supportAccountsCurrent',
    'realization.replacementAccountsNext',
    'realization.surplus.replacementWeight_lt_supportWeight',
  ]);

  const descent = declarationBlock0(source,
    'TerminalPacketChargeSurplusRealization.strictResidualDescent');
  requireTokens0(failures, descent, 'derived-residual-descent', [
    'residualSlack next < residualSlack current',
    'realization.strictEquivalentGain.strictResidualDescent',
  ]);

  return [...new Set(failures)];
}

test('Packet charge surplus derives strict gain from exact occurrence accounting', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its exact declaration surface from the source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.ok(expected.length > MILESTONE_THEOREMS.length);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketChargeSurplus\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketChargeSurplus$/mu);
});

test('compiled inventory pins every reviewed charge-surplus theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of MILESTONE_THEOREMS) {
    const row = rows.get(name);
    assert.equal(row?.kind, 'theorem', name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
    assert.ok(inventory.milestoneCandidates.some(
      (entry) => entry.name === name && typeof entry.kernelType === 'string'));
  }
});

test('regression covers strict weight, gain, descent, and occurrence attacks', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalPacketChargeSurplusExample',
    '.replacementLength_lt_supportLength',
    '.replacementWeight_lt_supportWeight',
    'terminalPacketChargeSurplus_requires_unmatchedOccurrence',
    'terminalPacketChargeSurplus_rejects_duplicateSupportReuse',
    '¬Nonempty (TerminalPacketChargeSurplus [1] [1]',
    '¬Nonempty (TerminalPacketChargeSurplus [1] [1, 1]',
    'realization.strictEquivalentGain',
    'realization.strictResidualDescent',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite charge-surplus realizer kernel', async () => {
  const [publication, status, docs, readme, reconstruction, report, pipeline,
    auditQuestions] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'),
    text0('docs/audit_questions.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-charge-surplus');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-charge-surplus');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite support and replacement charge ledgers/u);
  assert.match(milestone.scope, /unmatched positive support charge/u);
  assert.match(milestone.nonClaim, /does not construct a replacement/u);
  assert.match(milestone.nonClaim, /not unconditional ZeroSlack/u);
  assert.equal(status.leanResidualTerminalPacketChargeSurplusFormalized, true);
  assert.equal(status.leanResidualTerminalPacketChargeSurplusAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketChargeSurplusScope,
    /arbitrary-finite-occurrence-ledgers/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /R-ChargeSurplus/u);
  assert.match(docs, /duplicate support\s+occurrence/u);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /unmatched positive support charge/iu);
    assert.match(surface, /not unconditional ZeroSlack/iu);
  }
});

test('durable workflow derives transcript count and runs regression and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketChargeSurplusAxiomAudit\.lean[\s\S]{0,3000}?run: node --test audits\/lean-residual-terminal-packet-charge-surplus0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketChargeSurplusAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketChargeSurplus\.lean/u);
});

test('hostile charge-surplus mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'supportExact : support.Perm (pairing.map Prod.fst ++ unmatched)',
      'supportExact : True'), 'exact-occurrence-injection'],
    [source.replace(
      'replacementExact : replacement.Perm (pairing.map Prod.snd)',
      'replacementExact : True'), 'exact-occurrence-injection'],
    [source.replace(
      'replacementWeight entry.2 = supportWeight entry.1', 'True'),
    'exact-occurrence-injection'],
    [source.replace(
      'positiveUnmatched : ∃ charge, charge ∈ unmatched ∧ 0 < supportWeight charge',
      'positiveUnmatched : True'), 'exact-occurrence-injection'],
    [source.replace('Nat.lt_add_of_pos_right surplus.unmatchedWeight_pos',
      'Nat.lt_add_of_pos_right (by decide)'), 'strict-charge-surplus'],
    [source.replace(
      'semanticsPreserved : Equivalent next.candidate.program',
      'smaller : next.gateCount < current.gateCount\n  semanticsPreserved : Equivalent next.candidate.program'),
    'assumed-strictness'],
    [source.replace('StrictEquivalentGain current next := by', 'True := by'),
      'derived-strict-equivalent-gain'],
    [`${source}\naxiom chargeShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef fixedChargeLedger : Type := Fin 4\n`, 'fixed-bound'],
    [`${source}\ntheorem unconditionalZeroSlack : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
