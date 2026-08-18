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
  'lean/PNP/ResidualTerminalPacketBN5ObligationRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketBN5ObligationRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketBN5ObligationRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_bn5_obligation_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.frontierCheck_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.frontierCheck_eq_false_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.obligationCheck_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.obligationCheck_eq_false_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_fields`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_valid_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_colour_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationRoutes_firstRoute_descent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationFaithfulness_preserves`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationFaithfulness_faithful`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsBN5FrontierObligationReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_bn5_frontier_obligation_reflected_hb_first_route_failure`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|bn5_complete|packet_routes_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketFrontierRouteReflection',
    'PNP.ResidualTerminalBN5FullShadowLocalization',
  ]);

  const coordinate = declarationBlock0(source,
    'TerminalPacketSelectorBN5Coordinate');
  requireTokens0(failures, coordinate, 'bn5-coordinate-binding', [
    'TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature TransportType',
    'Frontier ChargeOwner Obligation OriginKernel ModeProjection',
  ]);

  const wrapper = declarationBlock0(source,
    'TerminalPacketSelectorBN5ObligationPayload');
  requireTokens0(failures, wrapper, 'bn5-payload-wrapper', [
    'checks : TerminalPacketSelectorFaithfulnessPayload rankCount',
    'sourceCoordinate : TerminalPacketSelectorBN5Coordinate',
    'selectorCoordinate : TerminalPacketSelectorBN5Coordinate',
    'Frontier ChargeOwner Obligation',
  ]);
  if (/source(?:Frontier|Obligation)\s*:\s*Bool/u.test(wrapper) ||
      /selector(?:Frontier|Obligation)\s*:\s*Bool/u.test(wrapper)) {
    failures.push('erased-bn5-fields');
  }

  const frontierChecker = declarationBlock0(source,
    'TerminalPacketSelectorBN5ObligationPayload.frontierCheck');
  requireTokens0(failures, frontierChecker, 'bn5-frontier-check', [
    '[DecidableEq Frontier]', 'payload.toTypedFrontier.frontierCheck',
  ]);
  if (frontierChecker.includes('payload.checks.frontierChecked')) {
    failures.push('caller-frontier-restored');
  }

  const obligationChecker = declarationBlock0(source,
    'TerminalPacketSelectorBN5ObligationPayload.obligationCheck');
  requireTokens0(failures, obligationChecker, 'bn5-obligation-check', [
    '[DecidableEq Obligation]', 'decide',
    'payload.sourceCoordinate.obligation =',
    'payload.selectorCoordinate.obligation',
  ]);
  if (obligationChecker.includes('payload.checks.obligationChecked')) {
    failures.push('caller-obligation-restored');
  }

  for (const [name, category, tokens] of [
    ['frontierCheck_eq_true_iff', 'frontier-true-reflection', [
      'payload.frontierCheck = true ↔',
      'payload.sourceCoordinate.frontier =',
      'payload.selectorCoordinate.frontier',
    ]],
    ['frontierCheck_eq_false_iff', 'frontier-false-reflection', [
      'payload.frontierCheck = false ↔',
      'payload.sourceCoordinate.frontier ≠',
      'payload.selectorCoordinate.frontier',
    ]],
    ['obligationCheck_eq_true_iff', 'obligation-true-reflection', [
      'payload.obligationCheck = true ↔',
      'payload.sourceCoordinate.obligation =',
      'payload.selectorCoordinate.obligation',
    ]],
    ['obligationCheck_eq_false_iff', 'obligation-false-reflection', [
      'payload.obligationCheck = false ↔',
      'payload.sourceCoordinate.obligation ≠',
      'payload.selectorCoordinate.obligation',
    ]],
  ]) {
    requireTokens0(failures, declarationBlock0(source,
      `TerminalPacketSelectorBN5ObligationPayload.${name}`), category, tokens);
  }

  const projection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes');
  requireTokens0(failures, projection, 'computed-bn5-projection', [
    'source.checks.withComputedColourChargeExactRouteRankDescent',
    'frontierChecked := source.frontierCheck',
    'obligationChecked := source.obligationCheck',
  ]);
  if (projection.includes('source.checks.frontierChecked') ||
      projection.includes('source.checks.obligationChecked')) {
    failures.push('caller-route-bit-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_fields');
  requireTokens0(failures, fields, 'bn5-preserved-fields', [
    'computed.frontierChecked = source.frontierCheck',
    'computed.obligationChecked = source.obligationCheck',
    'computed.colourChecked =', 'packetSelectorCanonicalColourCheck handle',
    'computed.chargeChecked = true', 'computed.rankTag = rankOf handle',
    'computed.exactRouteClear = true',
    'terminalResidualRankLTBool (afterRank handle) (beforeRank handle)',
  ]);

  const valid = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-bn5-fields', [
    ').Valid (rankOf handle) ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation =',
    'source.selectorCoordinate.obligation',
    'source.checks.activationChecked = true',
    'source.checks.directionChecked = true',
    'source.checks.budgetChecked = true',
    '(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (valid.includes('source.checks.frontierChecked = true') ||
      valid.includes('source.checks.obligationChecked = true') ||
      valid.includes('source.checks.colourChecked = true') ||
      valid.includes('source.checks.chargeChecked = true')) {
    failures.push('valid-retained-duplicate-premise');
  }

  const frontierFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_frontier_iff');
  requireTokens0(failures, frontierFailure, 'frontier-route-reflection', [
    ').FailureAt (rankOf handle) .frontier ↔',
    'source.sourceCoordinate.frontier ≠',
    'source.selectorCoordinate.frontier',
  ]);

  const obligationFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_obligation_iff');
  requireTokens0(failures, obligationFailure, 'obligation-route-reflection', [
    ').FailureAt (rankOf handle) .obligation ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation ≠',
    'source.selectorCoordinate.obligation',
  ]);

  for (const [route, category] of [
    ['colour', 'colour-route-impossible'],
    ['charge', 'charge-route-impossible'],
    ['rank', 'rank-route-impossible'],
    ['exactRoute', 'exact-route-impossible'],
  ]) {
    const block = declarationBlock0(source,
      `TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_${route}_iff_false`);
    requireTokens0(failures, block, category, [
      `.FailureAt (rankOf handle) .${route} ↔`, 'False',
    ]);
  }

  const frontierRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_frontier_iff');
  requireTokens0(failures, frontierRoute, 'frontier-first-route', [
    '= some .frontier ↔', 'source.sourceCoordinate.frontier ≠',
    'firstRoute_eq_some_iff_failureAt', 'failureAt_frontier_iff',
  ]);

  const obligationRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_obligation_iff');
  requireTokens0(failures, obligationRoute, 'obligation-first-route', [
    '= some .obligation ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation ≠',
    'firstRoute_eq_some_iff_failureAt', 'failureAt_obligation_iff',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationFaithfulness');
  requireTokens0(failures, table, 'bn5-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsBN5FrontierObligationReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'bn5-hb-outcome', [
    'withComputedPacketSelectorBN5FrontierObligationFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes',
    'packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationRoutes',
    'route ≠ .colour ∧', 'route ≠ .charge ∧', 'route ≠ .rank ∧',
    'route ≠ .exactRoute ∧', 'route ≠ .frontier ∨',
    'sourceCoordinate.frontier ≠', 'selectorCoordinate.frontier',
    'route ≠ .obligation ∨', 'sourceCoordinate.obligation ≠',
    'selectorCoordinate.obligation', 'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding|frontierBinding|obligationBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_bn5_frontier_obligation_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-bn5-endpoint', [
    'conclusion.existsBN5FrontierObligationReflectedFirstRouteFailure_of_selectorSilence',
    'route ≠ .frontier ∨', 'route ≠ .obligation ∨',
    'route ≠ .descent ∨',
  ]);

  return [...new Set(failures)];
}

test('Packet frontier and obligation routes project exact typed BN5 fields', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 36);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketBN5ObligationRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketBN5ObligationRouteReflection$/mu);
});

test('compiled inventory pins every reviewed BN5 obligation theorem', async () => {
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

test('regression covers equality, independent mismatches, route order, and HB', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'sourceCoordinate := coordinate 7 11',
    'selectorCoordinate := coordinate 7 11',
    'selectorCoordinate := coordinate 8 11',
    'selectorCoordinate := coordinate 7 12',
    'frontierCheck = true', 'frontierCheck = false',
    'obligationCheck = true', 'obligationCheck = false',
    '= some .frontier ↔', '= some .obligation ↔',
    '≠ some .colour', '≠ some .charge', '≠ some .rank',
    '≠ some .exactRoute', '= some .descent',
    'terminalBN6_packet_bn5_frontier_obligation_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns BN5-bound reflection without global overclaim', async () => {
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
    ({ id }) => id ===
      'residual-terminal-packet-bn5-obligation-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-bn5-obligation-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /BN5.*frontier.*obligation/iu);
  assert.match(milestone.scope, /inequal.*route/iu);
  assert.match(milestone.nonClaim, /three remaining routes/iu);
  assert.match(milestone.nonClaim,
    /coordinates.*explicit|not.*construct.*coordinates.*terminal/iu);
  assert.equal(
    status.leanResidualTerminalPacketBN5ObligationRouteReflectionFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalPacketBN5ObligationRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalPacketBN5ObligationRouteReflectionScope,
    /arbitrary-finite.*BN5.*frontier.*obligation.*three-earlier/iu,
  );
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /BN5[- ]bound|BN5 coordinate/iu, name);
    assert.match(semanticText0(text), /three remaining|remaining three/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketBN5ObligationRouteReflectionAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-bn5-obligation-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketBN5ObligationRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketBN5ObligationRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile BN5 field mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('payload.toTypedFrontier.frontierCheck',
      'payload.checks.frontierChecked'), 'bn5-frontier-check'],
    [source.replace(
      'decide\n    (payload.sourceCoordinate.obligation =\n      payload.selectorCoordinate.obligation)',
      'payload.checks.obligationChecked'), 'bn5-obligation-check'],
    [source.replace('sourceCoordinate : TerminalPacketSelectorBN5Coordinate',
      'sourceCoordinate : Bool\n  ignored : TerminalPacketSelectorBN5Coordinate'),
    'bn5-payload-wrapper'],
    [source.replace('frontierChecked := source.frontierCheck',
      'frontierChecked := source.checks.frontierChecked'),
    'computed-bn5-projection'],
    [source.replace('obligationChecked := source.obligationCheck',
      'obligationChecked := source.checks.obligationChecked'),
    'computed-bn5-projection'],
    [source.replace(
      'source.sourceCoordinate.obligation ≠\n          source.selectorCoordinate.obligation := by',
      'False := by'), 'obligation-route-reflection'],
    [source.replaceAll('route ≠ .obligation ∨', 'route = .obligation ∨'),
      'bn5-hb-outcome'],
    [`${source}\naxiom bn5ObligationShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedBN5Obligation : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem packet_routes_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
