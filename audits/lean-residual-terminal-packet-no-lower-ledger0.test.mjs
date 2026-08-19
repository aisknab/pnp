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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketNoLowerLedger.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketNoLowerLedgerAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketNoLowerLedger.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_packet_no_lower_ledger.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.checkPacketNoLowerLedger_eq_true_iff`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.checkPacketNoLowerLedger_eq_false`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.not_packetConclusion_of_checkedPacketNoLowerLedger`,
  `${NAMESPACE}.terminalBN6_packet_no_lower_ledger_excludes_positive_packet`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|packet_no_lower_ledger_complete|no_lower_ledger_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketDescentNoLowerBinding',
  ]);

  const proposition = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.PacketNoLowerLedgerAccepted');
  requireTokens0(failures, proposition, 'ledger-proposition', [
    'checkPacketSemanticHNActivityBinding = true',
    'checkPacketBudgetHBActivityBinding = true',
    'checkSelectorSilent = true',
    'checkNoOutcomeActiveClosure computed.environment = true',
    'checkPacketDescentNoLower table.environment.rankOf',
    'beforeRank afterRank = true',
  ]);

  const checker = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkPacketNoLowerLedger');
  requireTokens0(failures, checker, 'ledger-checker', [
    'checkPacketSemanticHNActivityBinding &&',
    'checkPacketBudgetHBActivityBinding &&',
    'checkSelectorSilent &&',
    'checkNoOutcomeActiveClosure computed.environment &&',
    'checkPacketDescentNoLower table.environment.rankOf',
  ]);
  if (/ledger(?:Checked|Valid|Accepted)\s*:/u.test(checker)) {
    failures.push('caller-success-flag');
  }

  const reflection = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkPacketNoLowerLedger_eq_true_iff');
  requireTokens0(failures, reflection, 'ledger-reflection', [
    'checkPacketNoLowerLedger dependencyTable beforeRank afterRank = true ↔',
    'PacketNoLowerLedgerAccepted dependencyTable beforeRank afterRank',
    'Bool.and_eq_true',
    'semantic, budget, silence, closure, noLower',
  ]);

  const rejection = declarationBlock0(source,
    'TerminalBN6PacketConclusion.checkPacketNoLowerLedger_eq_false');
  requireTokens0(failures, rejection, 'positive-packet-rejection', [
    'checkPacketNoLowerLedger dependencyTable beforeRank afterRank = false',
    'Bool.eq_false_iff.mpr',
    'checkPacketNoLowerLedger_eq_true_iff',
    'false_of_checkedPacketDescentNoLower_and_selectorSilence',
    'semanticBindingAccepted', 'budgetBindingAccepted', 'silenceAccepted',
    'closureAccepted', 'noLowerAccepted',
  ]);
  if (/\b(?:ledgerRejected|packetImpossible)\s*:/u.test(rejection)) {
    failures.push('caller-rejection-premise');
  }

  const exclusion = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.not_packetConclusion_of_checkedPacketNoLowerLedger');
  requireTokens0(failures, exclusion, 'accepted-ledger-exclusion', [
    'ledgerAccepted : table.checkPacketNoLowerLedger',
    '¬TerminalBN6PacketConclusion family',
    'conclusion.checkPacketNoLowerLedger_eq_false',
    'rw [rejected] at ledgerAccepted',
  ]);

  const named = declarationBlock0(source,
    'terminalBN6_packet_no_lower_ledger_excludes_positive_packet');
  requireTokens0(failures, named, 'named-endpoint', [
    'ledgerAccepted : table.checkPacketNoLowerLedger',
    '¬TerminalBN6PacketConclusion family :=',
    'not_packetConclusion_of_checkedPacketNoLowerLedger',
  ]);

  return [...new Set(failures)];
}

test('Packet no-lower ledger recomputes all five exact rows', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 6);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketNoLowerLedger\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketNoLowerLedger$/mu);
});

test('compiled inventory pins every reviewed Packet ledger theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const candidates = new Map(inventory.milestoneCandidates
    .map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of MILESTONE_THEOREMS) {
    const row = rows.get(name);
    assert.equal(row?.kind, 'theorem', name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
    assert.equal(typeof candidates.get(name)?.kernelType, 'string', name);
  }
});

test('regression covers acceptance, independent rejection, reflection, and exclusion', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'emptyFamily', 'agreeingPayload', 'frontierMismatchPayload',
    'checkPacketNoLowerLedger', '= true', '= false',
    'PacketNoLowerLedgerAccepted',
    'checkPacketNoLowerLedger_eq_false',
    'terminalBN6_packet_no_lower_ledger_excludes_positive_packet',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns the Packet ledger branch without a global ZeroSlack overclaim', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/audit_questions.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-no-lower-ledger');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-no-lower-ledger');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /five.*checked.*Packet.*ledger|Packet.*ledger.*positive Packet/iu);
  assert.match(milestone.scope, /exclude|rules out/iu);
  assert.match(milestone.nonClaim,
    /Packet branch|not.*complete.*no-lower ledger/iu);
  assert.match(milestone.nonClaim,
    /terminal data|HResolve|BudgetResolve|normalization|saturation/iu);
  assert.equal(status.leanResidualTerminalPacketNoLowerLedgerFormalized, true);
  assert.equal(status.leanResidualTerminalPacketNoLowerLedgerAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketNoLowerLedgerScope,
    /arbitrary-finite.*Packet.*no-lower.*positive-Packet-exclusion/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text),
      /Packet.*no-lower.*ledger|no-lower.*ledger.*Packet/iu, name);
    assert.match(semanticText0(text),
      /Packet branch|complete ledger|not.*ZeroSlack|ZeroSlack.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketNoLowerLedgerAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-no-lower-ledger0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketNoLowerLedgerAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketNoLowerLedger\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile Packet no-lower ledger mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'computed.checkPacketSemanticHNActivityBinding &&',
      'true &&'), 'ledger-checker'],
    [source.replace(
      'computed.checkPacketBudgetHBActivityBinding &&',
      'true &&'), 'ledger-checker'],
    [source.replace(
      'computed.checkSelectorSilent &&',
      'true &&'), 'ledger-checker'],
    [source.replace(
      'computed.checkSelectorSilent &&\n    dependencyTable.checkNoOutcomeActiveClosure computed.environment &&',
      'computed.checkSelectorSilent &&\n    true &&'), 'ledger-checker'],
    [source.replace(
      'dependencyTable.checkNoOutcomeActiveClosure computed.environment &&\n    family.checkPacketDescentNoLower table.environment.rankOf\n      beforeRank afterRank',
      'dependencyTable.checkNoOutcomeActiveClosure computed.environment &&\n    true'), 'ledger-checker'],
    [source.replace(
      'false_of_checkedPacketDescentNoLower_and_selectorSilence',
      'checkPacketDescentNoLower_eq_false_of_selectorSilence'),
    'positive-packet-rejection'],
    [source.replaceAll(
      'conclusion.checkPacketNoLowerLedger_eq_false',
      'by assumption'), 'accepted-ledger-exclusion'],
    [`${source}\naxiom ledgerShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedLedger : Type := Fin 5\n`,
      'fixed-bound'],
    [`${source}\ntheorem packet_no_lower_ledger_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
