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
  'lean/PNP/ResidualTerminalPacketBudgetRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketBudgetRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketBudgetRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_budget_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorBN5BudgetPayload.budgetCheck_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5BudgetPayload.budgetCheck_eq_false_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_fields`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_valid_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_colour_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_activation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_direction_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_budget_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_activation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_direction_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_budget_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_descent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness_preserves`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness_faithful`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsBudgetReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_budget_reflected_hb_first_route_failure`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|packet_routes_complete|budget_semantics_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketDirectionRouteReflection',
  ]);

  const payload = declarationBlock0(source,
    'TerminalPacketSelectorBN5BudgetPayload');
  requireTokens0(failures, payload, 'typed-budget-payload', [
    'checks : TerminalPacketSelectorBN5DirectionPayload',
    'sourceBudget : Budget', 'selectorBudget : Budget',
  ]);

  const checker = declarationBlock0(source,
    'TerminalPacketSelectorBN5BudgetPayload.budgetCheck');
  requireTokens0(failures, checker, 'typed-budget-check', [
    '[DecidableEq Budget]', 'decide',
    'payload.sourceBudget = payload.selectorBudget',
  ]);
  if (checker.includes('payload.checks.checks.checks.budgetChecked')) {
    failures.push('caller-budget-restored');
  }

  for (const [name, category, operator] of [
    ['budgetCheck_eq_true_iff', 'budget-true-reflection', '='],
    ['budgetCheck_eq_false_iff', 'budget-false-reflection', '≠'],
  ]) {
    requireTokens0(failures, declarationBlock0(source,
      `TerminalPacketSelectorBN5BudgetPayload.${name}`), category, [
      `payload.budgetCheck = ${name.includes('true') ? 'true' : 'false'} ↔`,
      `payload.sourceBudget ${operator} payload.selectorBudget`,
    ]);
  }

  const projection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes');
  requireTokens0(failures, projection, 'computed-budget-projection', [
    'source.checks.checks.checks.withComputedColourChargeExactRouteRankDescent',
    'frontierChecked := source.checks.checks.frontierCheck',
    'obligationChecked := source.checks.checks.obligationCheck',
    'activationChecked := source.checks.checks.activationCheck',
    'directionChecked := source.checks.directionCheck',
    'budgetChecked := source.budgetCheck',
  ]);
  if (projection.includes('source.checks.checks.checks.budgetChecked')) {
    failures.push('caller-budget-restored');
  }

  const valid = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-budget', [
    ').Valid (rankOf handle) ↔',
    'source.checks.checks.sourceCoordinate.frontier =',
    'source.checks.checks.sourceCoordinate.obligation =',
    'source.checks.checks.sourceCoordinate.key.atom =',
    'source.checks.sourceDirection = source.checks.selectorDirection',
    'source.sourceBudget = source.selectorBudget',
    '(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (valid.includes('source.checks.checks.checks.budgetChecked = true')) {
    failures.push('valid-retained-budget-bit');
  }

  const budgetFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_budget_iff');
  requireTokens0(failures, budgetFailure, 'budget-route-reflection', [
    ').FailureAt', '(rankOf handle) .budget ↔',
    'source.checks.checks.sourceCoordinate.frontier =',
    'source.checks.checks.sourceCoordinate.obligation =',
    'source.checks.checks.sourceCoordinate.key.atom =',
    'source.checks.sourceDirection = source.checks.selectorDirection',
    'source.sourceBudget ≠ source.selectorBudget',
  ]);

  const budgetRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_budget_iff');
  requireTokens0(failures, budgetRoute, 'budget-first-route', [
    '= some .budget ↔',
    'source.sourceBudget ≠ source.selectorBudget',
    'packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_iff',
    'failureAt_budget_iff',
  ]);

  for (const [route, category] of [
    ['colour', 'colour-route-impossible'],
    ['charge', 'charge-route-impossible'],
    ['rank', 'rank-route-impossible'],
    ['exactRoute', 'exact-route-impossible'],
  ]) {
    const block = declarationBlock0(source,
      `TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_failureAt_${route}_iff_false`);
    requireTokens0(failures, block, category, [
      `.FailureAt (rankOf handle) .${route} ↔`, 'False',
    ]);
  }

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness');
  requireTokens0(failures, table, 'budget-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsBudgetReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'budget-hb-outcome', [
    'withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'route ≠ .direction ∨',
    'route ≠ .budget ∨',
    'sourceBudget ≠', 'selectorBudget',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding|directionBinding|budgetBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_budget_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-budget-endpoint', [
    'conclusion.existsBudgetReflectedFirstRouteFailure_of_selectorSilence',
    'route ≠ .frontier ∨', 'route ≠ .obligation ∨',
    'route ≠ .activation ∨', 'route ≠ .direction ∨',
    'route ≠ .budget ∨', 'route ≠ .descent ∨',
  ]);

  return [...new Set(failures)];
}

test('Packet budget route reflects exact typed Bud(u) equality', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 37);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketBudgetRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketBudgetRouteReflection$/mu);
});

test('compiled inventory pins every reviewed budget theorem', async () => {
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

test('regression covers independent budget mismatch, route order, and HB', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'budgetChecked := false',
    'sourceBudget := 17', 'selectorBudget := 17',
    'selectorBudget := 18',
    'budgetCheck = true', 'budgetCheck = false',
    'budgetCheck_eq_true_iff', 'budgetCheck_eq_false_iff',
    '= some .frontier ↔', '= some .obligation ↔',
    '= some .activation ↔', '= some .direction ↔', '= some .budget ↔',
    '≠ some .colour', '≠ some .charge', '≠ some .rank',
    '≠ some .exactRoute', '= some .descent',
    'terminalBN6_packet_budget_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns budget reflection without global overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-budget-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-budget-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /typed.*budget|budget.*typed/iu);
  assert.match(milestone.scope, /inequal.*route|route.*inequal/iu);
  assert.match(milestone.nonClaim,
    /budget.*explicit|not.*construct.*budget.*terminal/iu);
  assert.match(milestone.nonClaim,
    /BudgetResolve|budget-envelope|global.*budget/iu);
  assert.equal(status.leanResidualTerminalPacketBudgetRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketBudgetRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketBudgetRouteReflectionScope,
    /arbitrary-finite.*typed-budget.*all-packet-route-fields-reflected/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /typed[- ]budget|budget[- ]route/iu, name);
    assert.match(semanticText0(text), /BudgetResolve|budget envelope|global budget/iu,
      name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketBudgetRouteReflectionAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-budget-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketBudgetRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketBudgetRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile typed-budget mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'decide (payload.sourceBudget = payload.selectorBudget)',
      'payload.checks.checks.checks.budgetChecked'), 'typed-budget-check'],
    [source.replace('budgetChecked := source.budgetCheck',
      'budgetChecked := source.checks.checks.checks.budgetChecked'),
    'computed-budget-projection'],
    [source.replace(
      'source.sourceBudget = source.selectorBudget ∧',
      'source.checks.checks.checks.budgetChecked = true ∧'),
    'valid-reflects-budget'],
    [source.replace(
      'source.sourceBudget ≠ source.selectorBudget := by',
      'False := by'), 'budget-route-reflection'],
    [source.replaceAll('route ≠ .budget ∨', 'route = .budget ∨'),
      'budget-hb-outcome'],
    [`${source}\naxiom budgetShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedBudgetRoute : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem budget_semantics_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
