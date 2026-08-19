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
  'lean/PNP/ResidualTerminalPacketDescentNoLowerBinding.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketDescentNoLowerBindingAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketDescentNoLowerBinding.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_descent_no_lower_binding.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.checkPacketDescentNoLower_eq_true_iff`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.false_of_checkedPacketDescentNoLower_and_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_descent_no_lower_rejected`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|packet_no_lower_complete|no_lower_ledger_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketSemanticHNActivityBinding',
  ]);

  const proposition = declarationBlock0(source,
    'TerminalBN6GroupedFamily.PacketDescentNoLower');
  requireTokens0(failures, proposition, 'no-lower-proposition', [
    '∀ handle : family.PacketSelectorHandle',
    'packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes',
    'rankOf beforeRank afterRank handle ≠ some .descent',
  ]);

  const checker = declarationBlock0(source,
    'TerminalBN6GroupedFamily.checkPacketDescentNoLower');
  requireTokens0(failures, checker, 'no-lower-checker', [
    'family.packetSelectorHandles.all fun handle =>',
    'decide',
    'packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes',
    'rankOf beforeRank afterRank handle ≠ some .descent',
  ]);
  if (/noLower(?:Checked|Valid|Accepted)\s*:/u.test(checker)) {
    failures.push('caller-success-flag');
  }

  const reflection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.checkPacketDescentNoLower_eq_true_iff');
  requireTokens0(failures, reflection, 'no-lower-reflection', [
    'checkPacketDescentNoLower rankOf beforeRank afterRank = true ↔',
    'family.PacketDescentNoLower rankOf beforeRank afterRank',
    'List.all_eq_true.mp', 'mem_packetSelectorHandles',
    'List.all_eq_true.mpr', 'decide_eq_true_eq',
  ]);

  const rejection = declarationBlock0(source,
    'TerminalBN6PacketConclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence');
  requireTokens0(failures, rejection, 'forced-rejection', [
    ').checkPacketSemanticHNActivityBinding = true',
    ').checkPacketBudgetHBActivityBinding = true',
    ').checkSelectorSilent = true',
    'checkNoOutcomeActiveClosure',
    'checkPacketDescentNoLower table.environment.rankOf',
    'beforeRank afterRank = false := by',
    'Bool.eq_false_iff.mpr',
    'checkPacketDescentNoLower_eq_true_iff',
    'existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence',
    'noLower handle found',
  ]);
  if (/\b(?:descentFound|noLowerFalse|routeFailure)\s*:/u.test(rejection)) {
    failures.push('caller-rejection-premise');
  }

  const contradiction = declarationBlock0(source,
    'TerminalBN6PacketConclusion.false_of_checkedPacketDescentNoLower_and_selectorSilence');
  requireTokens0(failures, contradiction, 'accepted-row-contradiction', [
    'noLowerAccepted : family.checkPacketDescentNoLower',
    '= true) : False := by',
    'checkPacketDescentNoLower_eq_false_of_selectorSilence',
    'rw [rejected] at noLowerAccepted',
  ]);

  const named = declarationBlock0(source,
    'terminalBN6_packet_descent_no_lower_rejected');
  requireTokens0(failures, named, 'named-endpoint', [
    'checkPacketDescentNoLower table.environment.rankOf',
    'beforeRank afterRank = false :=',
    'conclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence',
  ]);

  return [...new Set(failures)];
}

test('Packet descent no-lower checker is exhaustive and exact', async () => {
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
    'import PNP.ResidualTerminalPacketDescentNoLowerBinding\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketDescentNoLowerBinding$/mu);
});

test('compiled inventory pins every reviewed Packet no-lower theorem', async () => {
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

test('regression covers acceptance, forced descent rejection, reflection, and contradiction', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'frontierMismatchPayload', 'agreeingPayload',
    'checkPacketDescentNoLower', '= true', '= false',
    'PacketDescentNoLower',
    'terminalBN6_packet_descent_no_lower_rejected',
    'false_of_checkedPacketDescentNoLower_and_selectorSilence',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns one local no-lower row without a global ZeroSlack overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-descent-no-lower-binding');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-descent-no-lower-binding');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /Packet descent no-lower.*every canonical|exhaustive.*no-lower/iu);
  assert.match(milestone.scope, /reject|false/iu);
  assert.match(milestone.nonClaim,
    /one local.*row|not.*complete.*no-lower ledger/iu);
  assert.match(milestone.nonClaim,
    /terminal data|HResolve|BudgetResolve|normalization|saturation/iu);
  assert.equal(status.leanResidualTerminalPacketDescentNoLowerBindingFormalized,
    true);
  assert.equal(status.leanResidualTerminalPacketDescentNoLowerBindingAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketDescentNoLowerBindingScope,
    /arbitrary-finite.*local.*no-lower.*rejected/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /Packet.*no-lower|no-lower.*Packet/iu, name);
    assert.match(semanticText0(text),
      /one local|complete ledger|not.*ZeroSlack|ZeroSlack.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketDescentNoLowerBindingAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-descent-no-lower-binding0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketDescentNoLowerBindingAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketDescentNoLowerBinding\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile Packet descent no-lower mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'family.packetSelectorHandles.all fun handle =>',
      '[].all fun handle =>'), 'no-lower-checker'],
    [source.replaceAll(
      'rankOf beforeRank afterRank handle ≠ some .descent)',
      'rankOf beforeRank afterRank handle ≠ some .frontier)'),
    'no-lower-checker'],
    [source.replace(
      'existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence',
      'existsBudgetHBBoundFirstRouteFailure_of_selectorSilence'),
    'forced-rejection'],
    [source.replace('Bool.eq_false_iff.mpr', 'by_cases'),
      'forced-rejection'],
    [source.replaceAll(
      'conclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence',
      'by assumption'), 'named-endpoint'],
    [`${source}\naxiom noLowerShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedNoLower : Type := Fin 5\n`,
      'fixed-bound'],
    [`${source}\ntheorem no_lower_ledger_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
