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
  'lean/PNP/ResidualTerminalPacketDirectionRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketDirectionRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketDirectionRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_direction_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorBN5DirectionPayload.directionCheck_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5DirectionPayload.directionCheck_eq_false_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_fields`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_valid_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_colour_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_activation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_direction_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_activation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_direction_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_descent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness_preserves`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness_faithful`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsDirectionReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_direction_reflected_hb_first_route_failure`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|packet_routes_complete|direction_semantics_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketBN4ActivationRouteReflection',
  ]);

  const payload = declarationBlock0(source,
    'TerminalPacketSelectorBN5DirectionPayload');
  requireTokens0(failures, payload, 'typed-direction-payload', [
    'checks : TerminalPacketSelectorBN5ObligationPayload',
    'sourceDirection : Direction', 'selectorDirection : Direction',
  ]);

  const checker = declarationBlock0(source,
    'TerminalPacketSelectorBN5DirectionPayload.directionCheck');
  requireTokens0(failures, checker, 'typed-direction-check', [
    '[DecidableEq Direction]', 'decide',
    'payload.sourceDirection = payload.selectorDirection',
  ]);
  if (checker.includes('payload.checks.checks.directionChecked')) {
    failures.push('caller-direction-restored');
  }

  for (const [name, category, operator] of [
    ['directionCheck_eq_true_iff', 'direction-true-reflection', '='],
    ['directionCheck_eq_false_iff', 'direction-false-reflection', '≠'],
  ]) {
    requireTokens0(failures, declarationBlock0(source,
      `TerminalPacketSelectorBN5DirectionPayload.${name}`), category, [
      `payload.directionCheck = ${name.includes('true') ? 'true' : 'false'} ↔`,
      `payload.sourceDirection ${operator} payload.selectorDirection`,
    ]);
  }

  const projection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes');
  requireTokens0(failures, projection, 'computed-direction-projection', [
    'source.checks.checks.withComputedColourChargeExactRouteRankDescent',
    'frontierChecked := source.checks.frontierCheck',
    'obligationChecked := source.checks.obligationCheck',
    'activationChecked := source.checks.activationCheck',
    'directionChecked := source.directionCheck',
  ]);
  if (projection.includes('source.checks.checks.directionChecked')) {
    failures.push('caller-direction-restored');
  }

  const valid = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-direction', [
    ').Valid (rankOf handle) ↔',
    'source.checks.sourceCoordinate.frontier =',
    'source.checks.sourceCoordinate.obligation =',
    'source.checks.sourceCoordinate.key.atom =',
    'source.sourceDirection = source.selectorDirection',
    'source.checks.checks.budgetChecked = true',
    '(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (valid.includes('source.checks.checks.directionChecked = true')) {
    failures.push('valid-retained-direction-bit');
  }

  const directionFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_direction_iff');
  requireTokens0(failures, directionFailure, 'direction-route-reflection', [
    ').FailureAt', '(rankOf handle) .direction ↔',
    'source.checks.sourceCoordinate.frontier =',
    'source.checks.sourceCoordinate.obligation =',
    'source.checks.sourceCoordinate.key.atom =',
    'source.sourceDirection ≠ source.selectorDirection',
  ]);

  const directionRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_direction_iff');
  requireTokens0(failures, directionRoute, 'direction-first-route', [
    '= some .direction ↔',
    'source.sourceDirection ≠ source.selectorDirection',
    'packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff',
    'failureAt_direction_iff',
  ]);

  for (const [route, category] of [
    ['colour', 'colour-route-impossible'],
    ['charge', 'charge-route-impossible'],
    ['rank', 'rank-route-impossible'],
    ['exactRoute', 'exact-route-impossible'],
  ]) {
    const block = declarationBlock0(source,
      `TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_${route}_iff_false`);
    requireTokens0(failures, block, category, [
      `.FailureAt (rankOf handle) .${route} ↔`, 'False',
    ]);
  }

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness');
  requireTokens0(failures, table, 'direction-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsDirectionReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'direction-hb-outcome', [
    'withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'route ≠ .direction ∨',
    'sourceDirection ≠', 'selectorDirection',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding|directionBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_direction_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-direction-endpoint', [
    'conclusion.existsDirectionReflectedFirstRouteFailure_of_selectorSilence',
    'route ≠ .frontier ∨', 'route ≠ .obligation ∨',
    'route ≠ .activation ∨', 'route ≠ .direction ∨',
    'route ≠ .descent ∨',
  ]);

  return [...new Set(failures)];
}

test('Packet direction route reflects exact typed Dir(u) equality', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 35);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketDirectionRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketDirectionRouteReflection$/mu);
});

test('compiled inventory pins every reviewed direction theorem', async () => {
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

test('regression covers independent direction mismatch, route order, and HB', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'directionChecked := false',
    'sourceDirection := 13', 'selectorDirection := 13',
    'selectorDirection := 14',
    'directionCheck = true', 'directionCheck = false',
    'directionCheck_eq_true_iff', 'directionCheck_eq_false_iff',
    '= some .frontier ↔', '= some .obligation ↔',
    '= some .activation ↔', '= some .direction ↔',
    '≠ some .colour', '≠ some .charge', '≠ some .rank',
    '≠ some .exactRoute', '= some .descent',
    'terminalBN6_packet_direction_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns direction reflection without global overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-direction-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-direction-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /typed.*direction|direction.*typed/iu);
  assert.match(milestone.scope, /inequal.*route|route.*inequal/iu);
  assert.match(milestone.nonClaim, /sole remaining.*budget|budget.*sole remaining/iu);
  assert.match(milestone.nonClaim,
    /direction.*explicit|not.*construct.*direction.*terminal/iu);
  assert.equal(status.leanResidualTerminalPacketDirectionRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketDirectionRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketDirectionRouteReflectionScope,
    /arbitrary-finite.*typed-direction.*sole-remaining-budget/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /typed[- ]direction|direction[- ]route/iu, name);
    assert.match(semanticText0(text), /sole remaining.*budget|budget.*sole remaining/iu,
      name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketDirectionRouteReflectionAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-direction-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketDirectionRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketDirectionRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile typed-direction mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'decide (payload.sourceDirection = payload.selectorDirection)',
      'payload.checks.checks.directionChecked'), 'typed-direction-check'],
    [source.replace('directionChecked := source.directionCheck',
      'directionChecked := source.checks.checks.directionChecked'),
    'computed-direction-projection'],
    [source.replace(
      'source.sourceDirection = source.selectorDirection ∧',
      'source.checks.checks.directionChecked = true ∧'),
    'valid-reflects-direction'],
    [source.replace(
      'source.sourceDirection ≠ source.selectorDirection := by',
      'False := by'), 'direction-route-reflection'],
    [source.replaceAll('route ≠ .direction ∨', 'route = .direction ∨'),
      'direction-hb-outcome'],
    [`${source}\naxiom directionShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedDirectionRoute : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem direction_semantics_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
