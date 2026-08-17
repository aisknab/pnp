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
  'lean/PNP/ResidualTerminalPacketRankRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketRankRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketRankRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_rank_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_valid_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_firstRoute_eq_some_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedRankDescent_check`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedRankDescent_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedRankDescent_firstRoute_descent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorRankDescentFaithfulness_preserves`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsRankTagReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_rank_tag_reflected_hb_first_route_failure`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|selector_compatibility_complete|hb_negative_closure)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketDescentRouteReflection',
  ]);

  const projection = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent');
  requireTokens0(failures, projection, 'computed-rank-descent-projection', [
    '{ payload.withComputedDescent before after with',
    'rankTag := expectedRank',
  ]);
  if (projection.includes('rankTag := payload.rankTag')) {
    failures.push('caller-rank-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_fields');
  requireTokens0(failures, fields, 'preserved-payload-fields', [
    '.colourChecked =', '.frontierChecked =', '.chargeChecked =',
    '.obligationChecked =', '.activationChecked =', '.directionChecked =',
    '.budgetChecked =', '.rankTag =', 'expectedRank',
    '.exactRouteClear =', '.strictDescentClear =',
    'terminalResidualRankLTBool after before',
  ]);

  const valid = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-canonical-rank-descent', [
    ').Valid', 'expectedRank ↔', 'payload.colourChecked = true',
    'payload.exactRouteClear = true', 'after.LexLT before',
    'terminalResidualRankLTBool_eq_true_iff',
  ]);
  if (valid.includes('payload.rankTag = expectedRank')) {
    failures.push('valid-retained-caller-rank-premise');
  }

  const rankFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_failureAt_rank_iff_false');
  requireTokens0(failures, rankFailure, 'rank-route-impossible', [
    ').FailureAt', 'expectedRank .rank ↔ False',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const noRankRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_firstRoute_ne_some_rank');
  requireTokens0(failures, noRankRoute, 'rank-first-route-excluded', [
    ').firstRoute', 'expectedRank ≠ some .rank',
    'firstRoute_eq_some_iff_failureAt expectedRank .rank',
    'withComputedRankDescent_failureAt_rank_iff_false',
  ]);

  const descentFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_failureAt_descent_iff');
  requireTokens0(failures, descentFailure, 'descent-failure-reflection', [
    ').FailureAt', 'expectedRank .descent ↔',
    'payload.colourChecked = true', 'payload.exactRouteClear = true',
    '¬after.LexLT before', 'terminalResidualRankLTBool_eq_false_iff',
  ]);
  if (descentFailure.includes('payload.rankTag = expectedRank')) {
    failures.push('descent-retained-caller-rank-premise');
  }

  const familyRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedRankDescent');
  requireTokens0(failures, familyRoute, 'canonical-family-rank-reflection', [
    '(family.packetSelectorPayloadAtom handle).payload.withComputedRankDescent',
    '(rankOf handle)', '(beforeRank handle)', '(afterRank handle)',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorRankDescentFaithfulness');
  requireTokens0(failures, table, 'rank-tag-reflected-table', [
    'rankOf := table.environment.rankOf',
    'faithful :=',
    'family.packetSelectorPayloadFaithfulWithComputedRankDescent',
    'table.environment.rankOf beforeRank afterRank',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsRankTagReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'rank-tag-reflected-hb-outcome', [
    'withComputedPacketSelectorRankDescentFaithfulness beforeRank',
    ').noFaithful_of_selectorSilent dependencyTable silenceAccepted',
    'packetSelectorPayloadFirstRouteWithComputedRankDescent',
    '= some route ∧',
    'packetSelectorPayloadFailureAtWithComputedRankDescent',
    'route ≠ .rank ∧', 'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
    'computedRankDescent_firstRoute_ne_some_rank',
    'not_rankDescent_of_computedRankDescent_firstRoute_descent',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_rank_tag_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-rank-tag-reflected-endpoint', [
    'conclusion.existsRankTagReflectedFirstRouteFailure_of_selectorSilence table',
    'dependencyTable beforeRank afterRank silenceAccepted closureAccepted',
    'route ≠ .rank ∧', 'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding)\b/u.test(named)) {
    failures.push('endpoint-retained-route-clear-or-binding');
  }

  return [...new Set(failures)];
}

test('Packet rank tag and descent are computed from authoritative inputs', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length > 0, true);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketRankRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketRankRouteReflection$/mu);
});

test('compiled inventory pins every reviewed rank-tag theorem', async () => {
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

test('regression exercises forged rank, descent, exact route, grouped, and HB cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'rankTag := 1',
    'withComputedRankDescent 0 beforeRank beforeRank',
    'withComputedRankDescent 0 beforeRank smallerAfterRank',
    'some .rank', 'some .descent', 'some .exactRoute',
    'rankDescent_of_withComputedRankDescent_check',
    'computedRankDescent_firstRoute_ne_some_rank',
    'not_rankDescent_of_computedRankDescent_firstRoute_descent',
    'terminalBN6_packet_rank_tag_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns rank-tag reflection without global-route overclaim', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions] = await Promise.all([
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
    ({ id }) => id === 'residual-terminal-packet-rank-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-rank-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /rank tag.*authoritative.*handle rank/iu);
  assert.match(milestone.scope, /cannot return.*rank.*nondecreasing/iu);
  assert.match(milestone.nonClaim, /eight remaining routes/iu);
  assert.match(milestone.nonClaim, /does not construct.*rank map/iu);
  assert.equal(status.leanResidualTerminalPacketRankRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketRankRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketRankRouteReflectionScope,
    /arbitrary-finite.*canonical-rank-tag.*rank-route-excluded/iu);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /rank-tag|rank tag/iu, name);
    assert.match(semanticText0(text), /eight remaining|remaining eight/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketRankRouteReflectionAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-rank-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketRankRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketRankRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile rank-tag reflection mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('rankTag := expectedRank',
      'rankTag := payload.rankTag'), 'computed-rank-descent-projection'],
    [source.replace('{ payload.withComputedDescent before after with',
      '{ payload with'), 'computed-rank-descent-projection'],
    [source.replace('terminalResidualRankLTBool after before',
      'terminalResidualRankLTBool before after'), 'preserved-payload-fields'],
    [source.replace('expectedRank .rank ↔ False',
      'expectedRank .rank ↔ True'), 'rank-route-impossible'],
    [source.replace('faithful :=\n          family.packetSelectorPayloadFaithfulWithComputedRankDescent',
      'faithful :=\n          table.environment.faithful'), 'rank-tag-reflected-table'],
    [source.replace('route ≠ .rank ∧',
      'route = .rank ∧'), 'rank-tag-reflected-hb-outcome'],
    [source.replace('dependencyTable beforeRank afterRank silenceAccepted closureAccepted',
      'dependencyTable beforeRank afterRank rankBinding closureAccepted'),
    'endpoint-retained-route-clear-or-binding'],
    [`${source}\naxiom reflectedRankShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedReflectedRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem zero_slack_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
