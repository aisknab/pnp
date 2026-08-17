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
  'lean/PNP/ResidualTerminalPacketChargeRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketChargeRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketChargeRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_charge_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_valid_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_firstRoute_eq_some_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedChargeExactRouteRankDescent_check`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorCanonicalPositiveCharge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedChargeExactRouteRankDescent_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedChargeExactRouteRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedChargeExactRouteRankDescent_firstRoute_descent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorChargeExactRouteRankDescentFaithfulness_preserves`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsChargeReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_charge_reflected_hb_first_route_failure`,
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
    'PNP.ResidualTerminalPacketExactRouteReflection',
  ]);

  const projection = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent');
  requireTokens0(failures, projection, 'computed-positive-charge-projection', [
    '{ payload.withComputedExactRouteRankDescent expectedRank before after with',
    'chargeChecked := true',
  ]);
  if (projection.includes('chargeChecked := payload.chargeChecked')) {
    failures.push('caller-charge-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_fields');
  requireTokens0(failures, fields, 'reflected-charge-preserved-fields', [
    '.colourChecked =', '.frontierChecked =', '.chargeChecked = true',
    '.obligationChecked =', '.activationChecked =', '.directionChecked =',
    '.budgetChecked =', '.rankTag = expectedRank',
    '.exactRouteClear = true', '.strictDescentClear =',
    'terminalResidualRankLTBool after before',
  ]);

  const valid = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-four-canonical-fields', [
    ').Valid expectedRank ↔', 'payload.colourChecked = true',
    'payload.budgetChecked = true', 'after.LexLT before',
    'terminalResidualRankLTBool_eq_true_iff',
  ]);
  if (valid.includes('payload.rankTag = expectedRank') ||
      valid.includes('payload.exactRouteClear = true') ||
      valid.includes('payload.chargeChecked = true')) {
    failures.push('valid-retained-duplicate-premise');
  }

  const chargeFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_failureAt_charge_iff_false');
  requireTokens0(failures, chargeFailure, 'charge-route-impossible', [
    ').FailureAt expectedRank .charge ↔ False',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const noCharge = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_charge');
  requireTokens0(failures, noCharge, 'charge-first-route-excluded', [
    ').firstRoute expectedRank ≠ some .charge',
    'firstRoute_eq_some_iff_failureAt expectedRank .charge',
    'withComputedChargeExactRouteRankDescent_failureAt_charge_iff_false',
  ]);

  const exactFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_failureAt_exactRoute_iff_false');
  requireTokens0(failures, exactFailure, 'exact-route-impossible', [
    ').FailureAt expectedRank .exactRoute ↔ False',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const noExactRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute');
  requireTokens0(failures, noExactRoute, 'exact-first-route-excluded', [
    ').firstRoute expectedRank ≠ some .exactRoute',
    'firstRoute_eq_some_iff_failureAt expectedRank .exactRoute',
    'withComputedChargeExactRouteRankDescent_failureAt_exactRoute_iff_false',
  ]);

  const sourceCharge = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorCanonicalPositiveCharge');
  requireTokens0(failures, sourceCharge, 'canonical-positive-charge-evidence', [
    '0 < (family.packetSelectorPayloadAtom handle).mass',
    'packetSelectorPayloadAtom handle).massPositive',
  ]);

  const familyPayload = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedChargeExactRouteRankDescent');
  requireTokens0(failures, familyPayload, 'canonical-family-charge-reflection', [
    '(family.packetSelectorPayloadAtom handle).payload',
    '|>.withComputedChargeExactRouteRankDescent', '(rankOf handle)',
    '(beforeRank handle)', '(afterRank handle)',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorChargeExactRouteRankDescentFaithfulness');
  requireTokens0(failures, table, 'charge-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedChargeExactRouteRankDescent',
    'table.environment.rankOf beforeRank afterRank',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsChargeReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'charge-reflected-hb-outcome', [
    'withComputedPacketSelectorChargeExactRouteRankDescentFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent',
    'packetSelectorPayloadFailureAtWithComputedChargeExactRouteRankDescent',
    'route ≠ .charge ∧', 'route ≠ .rank ∧', 'route ≠ .exactRoute ∧',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_charge_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-charge-reflected-endpoint', [
    'conclusion.existsChargeReflectedFirstRouteFailure_of_selectorSilence',
    'table dependencyTable beforeRank afterRank silenceAccepted closureAccepted',
    'route ≠ .charge ∧', 'route ≠ .rank ∧', 'route ≠ .exactRoute ∧',
  ]);

  return [...new Set(failures)];
}

test('Packet charge, internal route, rank, and descent use authoritative inputs', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 27);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketChargeRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketChargeRouteReflection$/mu);
});

test('compiled inventory pins every reviewed charge-route theorem', async () => {
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

test('regression exercises forged charge, route, rank, descent, grouped, and HB cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'chargeChecked := false', 'exactRouteClear := false',
    'withComputedChargeExactRouteRankDescent 0 beforeRank',
    'some .rank', 'some .exactRoute', 'some .descent', 'some .colour',
    'some .frontier', 'some .charge', 'some .obligation',
    'some .activation', 'some .direction', 'some .budget',
    'rankDescent_of_withComputedChargeExactRouteRankDescent_check',
    'computedChargeExactRouteRankDescent_firstRoute_ne_some_charge',
    'computedChargeExactRouteRankDescent_firstRoute_ne_some_rank',
    'computedChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute',
    'terminalBN6_packet_charge_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns internal charge-route reflection without semantic overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-charge-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-charge-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /canonical.*handle.*positive.*payload/iu);
  assert.match(milestone.scope, /cannot return.*charge.*rank.*exactRoute/iu);
  assert.match(milestone.nonClaim, /six remaining routes/iu);
  assert.match(milestone.nonClaim, /positive source mass.*not.*charge-surplus/iu);
  assert.equal(status.leanResidualTerminalPacketChargeRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketChargeRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketChargeRouteReflectionScope,
    /arbitrary-finite.*positive-source-charge.*charge-route-excluded/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /charge-route|charge route/iu, name);
    assert.match(semanticText0(text), /six remaining|remaining six/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketChargeRouteReflectionAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-charge-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketChargeRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketChargeRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile charge-route reflection mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('chargeChecked := true',
      'chargeChecked := payload.chargeChecked'),
    'computed-positive-charge-projection'],
    [source.replace('{ payload.withComputedExactRouteRankDescent expectedRank before after with',
      '{ payload with'), 'computed-positive-charge-projection'],
    [source.replace('terminalResidualRankLTBool after before',
      'terminalResidualRankLTBool before after'), 'reflected-charge-preserved-fields'],
    [source.replace('expectedRank .charge ↔ False',
      'expectedRank .charge ↔ True'), 'charge-route-impossible'],
    [source.replace('(family.packetSelectorPayloadAtom handle).massPositive',
      'by exact Nat.zero_lt_succ 0'), 'canonical-positive-charge-evidence'],
    [source.replace('faithful :=\n          family.packetSelectorPayloadFaithfulWithComputedChargeExactRouteRankDescent',
      'faithful :=\n          table.environment.faithful'),
    'charge-reflected-table'],
    [source.replace('route ≠ .charge ∧',
      'route = .charge ∧'), 'charge-reflected-hb-outcome'],
    [`${source}\naxiom reflectedChargeShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedExactRouteRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem zero_slack_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
