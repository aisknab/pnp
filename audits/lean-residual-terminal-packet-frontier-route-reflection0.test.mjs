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
  'lean/PNP/ResidualTerminalPacketFrontierRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketFrontierRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketFrontierRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_frontier_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_false_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_fields`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_valid_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_colour_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_frontier_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_ne_some_frontier_of_eq`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_descent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness_preserves`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness_faithful`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsTypedFrontierReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|frontier_faithful_complete|bn5_frontier_derived)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketColourRouteReflection',
  ]);

  const wrapper = declarationBlock0(source,
    'TerminalPacketSelectorTypedFrontierPayload');
  requireTokens0(failures, wrapper, 'typed-frontier-wrapper', [
    '(rankCount : Nat) (Frontier : Type)',
    'checks : TerminalPacketSelectorFaithfulnessPayload rankCount',
    'sourceFrontier : Frontier', 'selectorFrontier : Frontier',
    'deriving DecidableEq',
  ]);

  const checker = declarationBlock0(source,
    'TerminalPacketSelectorTypedFrontierPayload.frontierCheck');
  requireTokens0(failures, checker, 'typed-frontier-check', [
    '[DecidableEq Frontier]',
    'decide (payload.sourceFrontier = payload.selectorFrontier)',
  ]);
  if (checker.includes('payload.checks.frontierChecked')) {
    failures.push('caller-frontier-restored');
  }

  const accepted = declarationBlock0(source,
    'TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_true_iff');
  requireTokens0(failures, accepted, 'typed-frontier-true-reflection', [
    'payload.frontierCheck = true ↔',
    'payload.sourceFrontier = payload.selectorFrontier',
  ]);
  const rejected = declarationBlock0(source,
    'TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_false_iff');
  requireTokens0(failures, rejected, 'typed-frontier-false-reflection', [
    'payload.frontierCheck = false ↔',
    'payload.sourceFrontier ≠ payload.selectorFrontier',
  ]);

  const projection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent');
  requireTokens0(failures, projection, 'computed-frontier-projection', [
    '(family.packetSelectorPayloadAtom handle).payload.checks',
    '|>.withComputedColourChargeExactRouteRankDescent',
    'frontierChecked :=',
    '(family.packetSelectorPayloadAtom handle).payload.frontierCheck',
  ]);
  if (projection.includes('frontierChecked :=\n      (family.packetSelectorPayloadAtom handle).payload.checks.frontierChecked')) {
    failures.push('caller-frontier-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_fields');
  requireTokens0(failures, fields, 'typed-frontier-preserved-fields', [
    'computed.frontierChecked = source.frontierCheck',
    'computed.colourChecked =', 'packetSelectorCanonicalColourCheck handle',
    'computed.chargeChecked = true', 'computed.rankTag = rankOf handle',
    'computed.exactRouteClear = true',
    'terminalResidualRankLTBool (afterRank handle) (beforeRank handle)',
  ]);

  const valid = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-typed-frontier', [
    ').Valid (rankOf handle) ↔',
    'source.sourceFrontier = source.selectorFrontier',
    'source.checks.obligationChecked = true',
    'source.checks.activationChecked = true',
    'source.checks.directionChecked = true',
    'source.checks.budgetChecked = true',
    '(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (valid.includes('source.checks.frontierChecked = true') ||
      valid.includes('source.checks.colourChecked = true') ||
      valid.includes('source.checks.chargeChecked = true') ||
      valid.includes('source.checks.rankTag = rankOf handle') ||
      valid.includes('source.checks.exactRouteClear = true')) {
    failures.push('valid-retained-duplicate-premise');
  }

  const frontierFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_frontier_iff');
  requireTokens0(failures, frontierFailure, 'frontier-route-reflection', [
    ').FailureAt (rankOf handle) .frontier ↔',
    'source.sourceFrontier ≠ source.selectorFrontier',
    'TerminalPacketSelectorTypedFrontierPayload.frontierCheck',
  ]);

  for (const [route, category] of [
    ['colour', 'colour-route-impossible'],
    ['charge', 'charge-route-impossible'],
    ['rank', 'rank-route-impossible'],
    ['exactRoute', 'exact-route-impossible'],
  ]) {
    const block = declarationBlock0(source,
      `TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_${route}_iff_false`);
    requireTokens0(failures, block, category, [
      `.FailureAt (rankOf handle) .${route} ↔`, 'False',
    ]);
  }

  const exactFrontier = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_frontier_iff');
  requireTokens0(failures, exactFrontier, 'frontier-first-route-reflection', [
    '= some .frontier ↔',
    'source.sourceFrontier ≠ source.selectorFrontier',
    'firstRoute_eq_some_iff_failureAt',
    'failureAt_frontier_iff',
  ]);

  const equalExclusion = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_ne_some_frontier_of_eq');
  requireTokens0(failures, equalExclusion, 'equal-frontier-route-excluded', [
    'sourceFrontier =', 'selectorFrontier', '≠ some .frontier',
    'eq_some_frontier_iff',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness');
  requireTokens0(failures, table, 'frontier-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsTypedFrontierReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'typed-frontier-hb-outcome', [
    'withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent',
    'packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent',
    'route ≠ .colour ∧', 'route ≠ .charge ∧', 'route ≠ .rank ∧',
    'route ≠ .exactRoute ∧', 'route ≠ .frontier ∨',
    'sourceFrontier ≠', 'selectorFrontier',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding|frontierBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-typed-frontier-endpoint', [
    'conclusion.existsTypedFrontierReflectedFirstRouteFailure_of_selectorSilence',
    'route ≠ .frontier ∨', 'sourceFrontier ≠', 'selectorFrontier',
    'route ≠ .descent ∨',
  ]);

  return [...new Set(failures)];
}

test('Packet frontier route uses typed equality and preserves prior canonical fields', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 30);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketFrontierRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketFrontierRouteReflection$/mu);
});

test('compiled inventory pins every reviewed typed-frontier theorem', async () => {
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

test('regression exercises equal, unequal, route exclusions, descent, and HB cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'sourceFrontier := 7', 'selectorFrontier := 7',
    'selectorFrontier := 8', 'frontierCheck = true',
    'frontierCheck = false', 'sourceFrontier ≠ unequalFrontiers.selectorFrontier',
    '= some .frontier ↔', '≠ some .frontier', '≠ some .colour',
    '≠ some .charge', '≠ some .rank', '≠ some .exactRoute',
    '= some .descent',
    'terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns typed frontier reflection without semantic overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-frontier-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-frontier-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /typed.*frontier.*equal/iu);
  assert.match(milestone.scope,
    /frontier.*inequal.*colour.*charge.*rank.*exactRoute/iu);
  assert.match(milestone.nonClaim, /four remaining routes/iu);
  assert.match(milestone.nonClaim,
    /supplied.*signatures.*not.*derived.*terminal|not.*construct.*signatures.*terminal/iu);
  assert.equal(status.leanResidualTerminalPacketFrontierRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketFrontierRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketFrontierRouteReflectionScope,
    /arbitrary-finite.*typed-frontier.*frontier-route.*four-earlier/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /typed[- ]frontier|frontier-signature/iu, name);
    assert.match(semanticText0(text), /four remaining|remaining four/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketFrontierRouteReflectionAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-frontier-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketFrontierRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketFrontierRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile typed-frontier mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'decide (payload.sourceFrontier = payload.selectorFrontier)',
      'payload.checks.frontierChecked'), 'typed-frontier-check'],
    [source.replace('sourceFrontier : Frontier', 'sourceFrontier : Bool'),
      'typed-frontier-wrapper'],
    [source.replace('payload.sourceFrontier = payload.selectorFrontier := by',
      'True := by'), 'typed-frontier-true-reflection'],
    [source.replace('payload.sourceFrontier ≠ payload.selectorFrontier := by',
      'False := by'), 'typed-frontier-false-reflection'],
    [source.replace(
      '(family.packetSelectorPayloadAtom handle).payload.frontierCheck',
      '(family.packetSelectorPayloadAtom handle).payload.checks.frontierChecked'),
    'computed-frontier-projection'],
    [source.replace('source.sourceFrontier ≠ source.selectorFrontier := by',
      'True := by'), 'frontier-route-reflection'],
    [source.replaceAll('route ≠ .frontier ∨', 'route = .frontier ∨'),
      'typed-frontier-hb-outcome'],
    [`${source}\naxiom typedFrontierShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedTypedFrontier : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem frontier_faithful_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
