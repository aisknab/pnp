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
  'lean/PNP/ResidualTerminalPacketSemanticHNActivityBinding.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSemanticHNActivityBindingAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSemanticHNActivityBinding.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_semantic_hn_activity_binding.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.checkPacketSemanticHNActivityBinding_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.packetSemanticFieldsAgree_of_checkedHNActivityBinding`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_semantic_hn_activity_bound_descent_failure`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|packet_routes_complete|hn_semantics_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketBudgetHBActivityBinding',
  ]);

  const agreement = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.PacketSemanticFieldsAgree');
  requireTokens0(failures, agreement, 'semantic-agreement', [
    'sourceCoordinate.frontier =',
    'selectorCoordinate.frontier ∧',
    'sourceCoordinate.obligation =',
    'selectorCoordinate.obligation ∧',
    'sourceCoordinate.key.atom =',
    'selectorCoordinate.key.atom ∧',
    'sourceDirection = payload.checks.selectorDirection',
  ]);

  const proposition = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.PacketSemanticHNActivityBound');
  requireTokens0(failures, proposition, 'binding-proposition', [
    '∀ handle : family.PacketSelectorHandle',
    '¬table.PacketSemanticFieldsAgree handle →',
    'table.environment.hnActive',
    'table.environment.rankOf handle', '= true',
  ]);

  const checker = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkPacketSemanticHNActivityBinding');
  requireTokens0(failures, checker, 'binding-checker', [
    'family.packetSelectorHandles.all fun handle =>',
    'sourceCoordinate.frontier =',
    'sourceCoordinate.obligation =',
    'sourceCoordinate.key.atom =',
    'sourceDirection =',
    'table.environment.hnActive (table.environment.rankOf handle)',
  ]);
  if (/binding(?:Checked|Valid|Accepted)\s*:/u.test(checker)) {
    failures.push('caller-success-flag');
  }

  const reflection = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkPacketSemanticHNActivityBinding_eq_true_iff');
  requireTokens0(failures, reflection, 'binding-reflection', [
    'checkPacketSemanticHNActivityBinding = true ↔',
    'table.PacketSemanticHNActivityBound',
    'List.all_eq_true.mp', 'mem_packetSelectorHandles',
    'List.all_eq_true.mpr',
  ]);

  const equality = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.packetSemanticFieldsAgree_of_checkedHNActivityBinding');
  requireTokens0(failures, equality, 'closure-agreement', [
    'bindingAccepted : table.checkPacketSemanticHNActivityBinding = true',
    'closureAccepted : dependencyTable.checkNoOutcomeActiveClosure',
    'table.PacketSemanticFieldsAgree handle := by',
    'checkPacketSemanticHNActivityBinding_eq_true_iff',
    'dependencyTable.hnActive_eq_false',
  ]);

  const exclusion = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding');
  requireTokens0(failures, exclusion, 'semantic-route-exclusion', [
    '≠ some .frontier ∧',
    '≠ some .obligation ∧',
    '≠ some .activation ∧',
    '≠ some .direction := by',
    'packetSemanticFieldsAgree_of_checkedHNActivityBinding',
    'eq_some_frontier_iff', 'eq_some_obligation_iff',
    'eq_some_activation_iff', 'eq_some_direction_iff',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'packet-hn-endpoint', [
    ').checkPacketSemanticHNActivityBinding = true',
    ').checkPacketBudgetHBActivityBinding = true',
    ').checkSelectorSilent = true',
    'checkNoOutcomeActiveClosure',
    '= some .descent ∧',
    'handle .descent ∧',
    '¬(afterRank handle).LexLT (beforeRank handle)',
    'existsBudgetHBBoundFirstRouteFailure_of_selectorSilence',
    'packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding',
  ]);
  if (/\b(?:routesClear|rankBinding|descentBinding|exactRouteBinding)\b/u.test(endpoint)) {
    failures.push('hidden-route-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_semantic_hn_activity_bound_descent_failure');
  requireTokens0(failures, named, 'named-endpoint', [
    'conclusion.existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence',
    '= some .descent', '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);

  return [...new Set(failures)];
}

test('Packet semantic/HN binding is exhaustive and exact', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 8);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSemanticHNActivityBinding\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSemanticHNActivityBinding$/mu);
});

test('compiled inventory pins every reviewed semantic/HN theorem', async () => {
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

test('regression covers agreement, every active mismatch, inactive rejection, and HB closure', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'agreeingPayload',
    'frontierMismatchPayload', 'obligationMismatchPayload',
    'activationMismatchPayload', 'directionMismatchPayload',
    'checkPacketSemanticHNActivityBinding = true',
    'checkPacketSemanticHNActivityBinding = false',
    'checkNoOutcomeActiveClosure', '= false',
    'PacketSemanticHNActivityBound',
    'packetSemanticFieldsAgree_of_checkedHNActivityBinding',
    '≠ some .frontier ∧',
    'terminalBN6_packet_semantic_hn_activity_bound_descent_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns the local binding without an HN or global semantics overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-semantic-hn-activity-binding');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-semantic-hn-activity-binding');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /frontier.*obligation.*activation.*direction.*HN/iu);
  assert.match(milestone.scope, /sole.*descent|exact residual[- ]nondecrease/iu);
  assert.match(milestone.nonClaim,
    /binding.*explicit|not.*construct.*binding.*terminal/iu);
  assert.match(milestone.nonClaim,
    /HN.*semantic|semantic completeness|decreasing transition/iu);
  assert.equal(status.leanResidualTerminalPacketSemanticHNActivityBindingFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSemanticHNActivityBindingAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketSemanticHNActivityBindingScope,
    /arbitrary-finite.*HN.*descent/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /semantic.*HN|HN.*semantic/iu, name);
    assert.match(semanticText0(text),
      /terminal data|HN blocker semantics|semantic completeness/iu, name);
    assert.match(semanticText0(text), /nondecrease|ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSemanticHNActivityBindingAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-semantic-hn-activity-binding0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSemanticHNActivityBindingAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSemanticHNActivityBinding\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile Packet semantic/HN binding mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'family.packetSelectorHandles.all fun handle =>',
      '[].all fun handle =>'), 'binding-checker'],
    [source.replace(
      /\|\|\n\s+table\.environment\.hnActive \(table\.environment\.rankOf handle\)/u,
      '||\n      true'), 'binding-checker'],
    [source.replace(
      'decide (payload.checks.sourceDirection =\n              payload.checks.selectorDirection)',
      'true'), 'binding-checker'],
    [source.replace(
      'dependencyTable.hnActive_eq_false',
      'dependencyTable.budgetActive_eq_false'), 'closure-agreement'],
    [source.replace('= some .descent ∧', '= some .frontier ∧'),
      'packet-hn-endpoint'],
    [`${source}\naxiom semanticHNShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedSemanticHNBinding : Type := Fin 5\n`,
      'fixed-bound'],
    [`${source}\ntheorem hn_semantics_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
