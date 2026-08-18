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
  'lean/PNP/ResidualTerminalPacketBN4ActivationRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketBN4ActivationRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketBN4ActivationRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_bn4_activation_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_false_iff`,
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_true_iff_activation`,
  `${NAMESPACE}.TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_false_iff_not_activation`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_fields`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_valid_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_colour_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_activation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_obligation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_activation_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationActivationRoutes_firstRoute_descent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness_preserves`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness_faithful`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsBN4ActivationReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_bn4_activation_reflected_hb_first_route_failure`,
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
    'PNP.ResidualTerminalPacketBN5ObligationRouteReflection',
  ]);

  const activationChecker = declarationBlock0(source,
    'TerminalPacketSelectorBN5ObligationPayload.activationCheck');
  requireTokens0(failures, activationChecker, 'bn4-activation-check', [
    '[DecidableEq ActivationAtom]', 'decide',
    'payload.sourceCoordinate.key.atom =',
    'payload.selectorCoordinate.key.atom',
  ]);
  if (activationChecker.includes('payload.checks.activationChecked')) {
    failures.push('caller-activation-restored');
  }

  for (const [name, category, tokens] of [
    ['activationCheck_eq_true_iff', 'activation-true-reflection', [
      'payload.activationCheck = true ↔',
      'payload.sourceCoordinate.key.atom =',
      'payload.selectorCoordinate.key.atom',
    ]],
    ['activationCheck_eq_false_iff', 'activation-false-reflection', [
      'payload.activationCheck = false ↔',
      'payload.sourceCoordinate.key.atom ≠',
      'payload.selectorCoordinate.key.atom',
    ]],
    ['activationCheck_eq_true_iff_activation',
      'activation-function-reflection', [
        'payload.activationCheck = true ↔',
        '∀ cut,',
        'TerminalBN4CodeActive',
        'terminalBN4ActivationCode payload.sourceCoordinate.key.atom',
        'terminalBN4ActivationCode payload.selectorCoordinate.key.atom',
        'terminalBN4ActivationCode_eq_iff_activation',
      ]],
    ['activationCheck_eq_false_iff_not_activation',
      'activation-function-rejection', [
        'payload.activationCheck = false ↔',
        '¬ ∀ cut,',
        'TerminalBN4CodeActive',
        'activationCheck_eq_true_iff_activation',
      ]],
  ]) {
    requireTokens0(failures, declarationBlock0(source,
      `TerminalPacketSelectorBN5ObligationPayload.${name}`),
    category, tokens);
  }
  const projection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes');
  requireTokens0(failures, projection, 'computed-bn4-activation-projection', [
    'source.checks.withComputedColourChargeExactRouteRankDescent',
    'frontierChecked := source.frontierCheck',
    'obligationChecked := source.obligationCheck',
    'activationChecked := source.activationCheck',
  ]);
  if (projection.includes('source.checks.frontierChecked') ||
      projection.includes('source.checks.obligationChecked') ||
      projection.includes('source.checks.activationChecked')) {
    failures.push('caller-route-bit-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_fields');
  requireTokens0(failures, fields, 'activation-preserved-fields', [
    'computed.frontierChecked = source.frontierCheck',
    'computed.obligationChecked = source.obligationCheck',
    'computed.activationChecked = source.activationCheck',
    'computed.colourChecked =', 'packetSelectorCanonicalColourCheck handle',
    'computed.chargeChecked = true', 'computed.rankTag = rankOf handle',
    'computed.exactRouteClear = true',
    'terminalResidualRankLTBool (afterRank handle) (beforeRank handle)',
  ]);

  const valid = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-activation', [
    ').Valid (rankOf handle) ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation =',
    'source.selectorCoordinate.obligation',
    'source.sourceCoordinate.key.atom =',
    'source.selectorCoordinate.key.atom',
    'source.checks.directionChecked = true',
    'source.checks.budgetChecked = true',
    '(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (valid.includes('source.checks.frontierChecked = true') ||
      valid.includes('source.checks.obligationChecked = true') ||
      valid.includes('source.checks.activationChecked = true') ||
      valid.includes('source.checks.colourChecked = true') ||
      valid.includes('source.checks.chargeChecked = true')) {
    failures.push('valid-retained-duplicate-premise');
  }

  const frontierFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_frontier_iff');
  requireTokens0(failures, frontierFailure, 'frontier-route-reflection', [
    ').FailureAt (rankOf handle) .frontier ↔',
    'source.sourceCoordinate.frontier ≠',
    'source.selectorCoordinate.frontier',
  ]);

  const obligationFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_obligation_iff');
  requireTokens0(failures, obligationFailure, 'obligation-route-reflection', [
    ').FailureAt (rankOf handle) .obligation ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation ≠',
    'source.selectorCoordinate.obligation',
  ]);

  const activationFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_activation_iff');
  requireTokens0(failures, activationFailure, 'activation-route-reflection', [
    ').FailureAt', '(rankOf handle) .activation ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation =',
    'source.selectorCoordinate.obligation',
    'source.sourceCoordinate.key.atom ≠',
    'source.selectorCoordinate.key.atom',
  ]);

  for (const [route, category] of [
    ['colour', 'colour-route-impossible'],
    ['charge', 'charge-route-impossible'],
    ['rank', 'rank-route-impossible'],
    ['exactRoute', 'exact-route-impossible'],
  ]) {
    const block = declarationBlock0(source,
      `TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_${route}_iff_false`);
    requireTokens0(failures, block, category, [
      `.FailureAt (rankOf handle) .${route} ↔`, 'False',
    ]);
  }

  const frontierRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_frontier_iff');
  requireTokens0(failures, frontierRoute, 'frontier-first-route', [
    '= some .frontier ↔', 'source.sourceCoordinate.frontier ≠',
    'firstRoute_eq_some_iff_failureAt', 'failureAt_frontier_iff',
  ]);

  const obligationRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_obligation_iff');
  requireTokens0(failures, obligationRoute, 'obligation-first-route', [
    '= some .obligation ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation ≠',
    'firstRoute_eq_some_iff_failureAt', 'failureAt_obligation_iff',
  ]);

  const activationRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_activation_iff');
  requireTokens0(failures, activationRoute, 'activation-first-route', [
    '= some .activation ↔',
    'source.sourceCoordinate.frontier = source.selectorCoordinate.frontier',
    'source.sourceCoordinate.obligation =',
    'source.selectorCoordinate.obligation',
    'source.sourceCoordinate.key.atom ≠',
    'source.selectorCoordinate.key.atom',
    'firstRoute_eq_some_iff_failureAt', 'failureAt_activation_iff',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness');
  requireTokens0(failures, table, 'activation-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsBN4ActivationReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'activation-hb-outcome', [
    'withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes',
    'packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationRoutes',
    'route ≠ .colour ∧', 'route ≠ .charge ∧', 'route ≠ .rank ∧',
    'route ≠ .exactRoute ∧', 'route ≠ .frontier ∨',
    'sourceCoordinate.frontier ≠', 'selectorCoordinate.frontier',
    'route ≠ .obligation ∨', 'sourceCoordinate.obligation ≠',
    'selectorCoordinate.obligation', 'route ≠ .activation ∨',
    'sourceCoordinate.key.atom ≠', 'selectorCoordinate.key.atom',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding|frontierBinding|obligationBinding|activationBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_bn4_activation_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-activation-endpoint', [
    'conclusion.existsBN4ActivationReflectedFirstRouteFailure_of_selectorSilence',
    'route ≠ .frontier ∨', 'route ≠ .obligation ∨',
    'route ≠ .activation ∨',
    'route ≠ .descent ∨',
  ]);

  return [...new Set(failures)];
}

test('Packet activation route reflects the exact nested BN4 activation key', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 34);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketBN4ActivationRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketBN4ActivationRouteReflection$/mu);
});

test('compiled inventory pins every reviewed BN4 activation theorem', async () => {
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
    'sourceCoordinate := coordinate 1 7 11',
    'selectorCoordinate := coordinate 1 7 11',
    'selectorCoordinate := coordinate 1 8 11',
    'selectorCoordinate := coordinate 1 7 12',
    'selectorCoordinate := coordinate 9 7 11',
    'frontierCheck = true', 'frontierCheck = false',
    'obligationCheck = true', 'obligationCheck = false',
    'activationCheck = true', 'activationCheck = false',
    'activationCheck_eq_true_iff_activation',
    'activationCheck_eq_false_iff_not_activation',
    '= some .frontier ↔', '= some .obligation ↔',
    '= some .activation ↔',
    '≠ some .colour', '≠ some .charge', '≠ some .rank',
    '≠ some .exactRoute', '= some .descent',
    'terminalBN6_packet_bn4_activation_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns BN4 activation reflection without global overclaim', async () => {
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
      'residual-terminal-packet-bn4-activation-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-bn4-activation-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /BN4.*activation|activation.*every cut/iu);
  assert.match(milestone.scope, /inequal.*route|route.*inequal/iu);
  assert.match(milestone.nonClaim, /two remaining routes/iu);
  assert.match(milestone.nonClaim,
    /coordinates.*explicit|not.*construct.*coordinates.*terminal/iu);
  assert.equal(
    status.leanResidualTerminalPacketBN4ActivationRouteReflectionFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalPacketBN4ActivationRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalPacketBN4ActivationRouteReflectionScope,
    /arbitrary-finite.*BN4.*activation.*two-(?:earlier|remaining)/iu,
  );
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /BN4[- ]activation|activation-exact/iu, name);
    assert.match(semanticText0(text), /two remaining|remaining two/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketBN4ActivationRouteReflectionAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-packet-bn4-activation-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketBN4ActivationRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketBN4ActivationRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile BN4 activation mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'decide\n    (payload.sourceCoordinate.key.atom =\n      payload.selectorCoordinate.key.atom)',
      'payload.checks.activationChecked'), 'bn4-activation-check'],
    [source.replace(
      'terminalBN4ActivationCode_eq_iff_activation _ _',
      'Iff.rfl'), 'activation-function-reflection'],
    [source.replace('activationChecked := source.activationCheck',
      'activationChecked := source.checks.activationChecked'),
    'computed-bn4-activation-projection'],
    [source.replace(
      'source.sourceCoordinate.key.atom =\n          source.selectorCoordinate.key.atom ∧',
      'source.checks.activationChecked = true ∧'),
    'valid-reflects-activation'],
    [source.replace(
      'source.sourceCoordinate.key.atom ≠\n          source.selectorCoordinate.key.atom := by',
      'False := by'), 'activation-route-reflection'],
    [source.replaceAll('route ≠ .activation ∨', 'route = .activation ∨'),
      'activation-hb-outcome'],
    [`${source}\naxiom activationShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedActivationRoute : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem packet_routes_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
