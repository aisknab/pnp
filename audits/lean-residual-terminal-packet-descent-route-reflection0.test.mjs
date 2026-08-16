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
  'lean/PNP/ResidualTerminalPacketDescentRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketDescentRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketDescentRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_descent_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_valid_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_firstRoute_eq_some_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedDescent_check`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedDescent_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computed_firstRoute_descent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorDescentFaithfulness_preserves`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsRankReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_rank_reflected_hb_first_route_failure`,
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
    'PNP.ResidualTerminalPacketSelectorFirstRouteSemantics',
  ]);

  const projection = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedDescent');
  requireTokens0(failures, projection, 'computed-descent-projection', [
    '{ payload with',
    'strictDescentClear := terminalResidualRankLTBool after before',
  ]);
  if (projection.includes('strictDescentClear := payload.strictDescentClear')) {
    failures.push('caller-descent-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_fields');
  requireTokens0(failures, fields, 'preserved-payload-fields', [
    '.colourChecked =', '.frontierChecked =', '.chargeChecked =',
    '.obligationChecked =', '.activationChecked =', '.directionChecked =',
    '.budgetChecked =', '.rankTag = payload.rankTag',
    '.exactRouteClear =',
    '.strictDescentClear =', 'terminalResidualRankLTBool after before',
  ]);

  const valid = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-rank-descent', [
    ').Valid expectedRank ↔',
    'payload.rankTag = expectedRank',
    'payload.exactRouteClear = true',
    'after.LexLT before',
    'terminalResidualRankLTBool_eq_true_iff',
  ]);

  const failure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_failureAt_descent_iff');
  requireTokens0(failures, failure, 'descent-failure-reflection', [
    ').FailureAt expectedRank',
    '.descent ↔',
    'payload.colourChecked = true',
    'payload.rankTag = expectedRank',
    'payload.exactRouteClear = true',
    '¬after.LexLT before',
    'terminalResidualRankLTBool_eq_false_iff',
  ]);

  const firstRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_firstRoute_eq_some_descent_iff');
  requireTokens0(failures, firstRoute, 'first-route-reflection', [
    ').firstRoute expectedRank =',
    'some .descent ↔',
    'firstRoute_eq_some_iff_failureAt expectedRank .descent',
    'withComputedDescent_failureAt_descent_iff',
    '¬after.LexLT before',
  ]);

  const familyRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedDescent');
  requireTokens0(failures, familyRoute, 'canonical-family-reflection', [
    'family.packetSelectorPayloadWithComputedDescent beforeRank afterRank handle',
    ').firstRoute (rankOf handle)',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorDescentFaithfulness');
  requireTokens0(failures, table, 'rank-reflected-table', [
    'rankOf := table.environment.rankOf',
    'faithful := family.packetSelectorPayloadFaithfulWithComputedDescent',
    'table.environment.rankOf beforeRank afterRank',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsRankReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'rank-reflected-hb-outcome', [
    'withComputedPacketSelectorDescentFaithfulness beforeRank afterRank',
    ').noFaithful_of_selectorSilent dependencyTable silenceAccepted',
    'packetSelectorPayloadFirstRouteWithComputedDescent',
    '= some route ∧',
    'packetSelectorPayloadFailureAtWithComputedDescent',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
    'not_rankDescent_of_computed_firstRoute_descent',
  ]);
  if (/\b(?:routesClear|bindingAccepted|descentBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_rank_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-rank-reflected-endpoint', [
    'conclusion.existsRankReflectedFirstRouteFailure_of_selectorSilence table',
    'dependencyTable beforeRank afterRank silenceAccepted closureAccepted',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|descentBinding)\b/u.test(named)) {
    failures.push('endpoint-retained-route-clear-or-binding');
  }

  return [...new Set(failures)];
}

test('Packet descent route is computed from exact RankWF semantics', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 17);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketDescentRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketDescentRouteReflection$/mu);
});

test('compiled inventory pins every reviewed rank-reflection theorem', async () => {
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

test('regression exercises forged, decreasing, equal-rank, grouped, and HB cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'strictDescentClear := true',
    'withComputedDescent beforeRank beforeRank',
    'withComputedDescent beforeRank smallerAfterRank',
    'some .descent',
    'rankDescent_of_withComputedDescent_check',
    'not_rankDescent_of_computed_firstRoute_descent',
    'terminalBN6_packet_rank_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns one reflected field without global-route overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-descent-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-descent-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /strict-descent.*ten-coordinate.*RankWF/iu);
  assert.match(milestone.scope, /earlier.*route.*nondecreasing/iu);
  assert.match(milestone.nonClaim, /first nine.*explicit/iu);
  assert.match(milestone.nonClaim, /does not construct.*ranks/iu);
  assert.equal(status.leanResidualTerminalPacketDescentRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketDescentRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketDescentRouteReflectionScope,
    /arbitrary-finite.*rank-reflected.*descent/iu);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /rank-reflected|computed descent/iu, name);
    assert.match(semanticText0(text), /first nine|remaining nine|other nine/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketDescentRouteReflectionAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-descent-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketDescentRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketDescentRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile rank-reflection mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('strictDescentClear := terminalResidualRankLTBool after before',
      'strictDescentClear := payload.strictDescentClear'),
    'computed-descent-projection'],
    [source.replace('terminalResidualRankLTBool after before',
      'terminalResidualRankLTBool before after'),
    'computed-descent-projection'],
    [source.replaceAll('payload.colourChecked = true ∧',
      'true = true ∧'), 'descent-failure-reflection'],
    [source.replace('¬after.LexLT before := by',
      'after.LexLT before := by'), 'descent-failure-reflection'],
    [source.replace('faithful := family.packetSelectorPayloadFaithfulWithComputedDescent',
      'faithful := table.environment.faithful'), 'rank-reflected-table'],
    [source.replace('route ≠ .descent ∨',
      'route = .descent ∨'), 'rank-reflected-hb-outcome'],
    [source.replace('dependencyTable beforeRank afterRank silenceAccepted closureAccepted',
      'dependencyTable beforeRank afterRank descentBinding closureAccepted'),
    'endpoint-retained-route-clear-or-binding'],
    [`${source}\naxiom reflectedDescentShortcut : True\n`,
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
