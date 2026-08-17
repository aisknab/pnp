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
  'lean/PNP/ResidualTerminalPacketColourRouteReflection.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketColourRouteReflectionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketColourRouteReflection.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_colour_route_reflection.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_valid_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_colour_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_charge_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_rank_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_eq_some_descent_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedColourChargeExactRouteRankDescent_check`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorCanonicalColourEligibility`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent_eq_some_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.not_rankDescent_of_computedColourChargeExactRouteRankDescent_firstRoute_descent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness_preserves`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsColourReflectedFirstRouteFailure_of_selectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_colour_reflected_hb_first_route_failure`,
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
    'PNP.ResidualTerminalPacketChargeRouteReflection',
  ]);

  const projection = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent');
  requireTokens0(failures, projection, 'computed-colour-projection', [
    '{ payload.withComputedChargeExactRouteRankDescent expectedRank before after with',
    'colourChecked := colourCheck',
  ]);
  if (projection.includes('colourChecked := payload.colourChecked')) {
    failures.push('caller-colour-restored');
  }

  const fields = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_fields');
  requireTokens0(failures, fields, 'reflected-colour-preserved-fields', [
    '.colourChecked = colourCheck', '.frontierChecked =', '.chargeChecked = true',
    '.obligationChecked =', '.activationChecked =', '.directionChecked =',
    '.budgetChecked =', '.rankTag = expectedRank',
    '.exactRouteClear = true', '.strictDescentClear =',
    'terminalResidualRankLTBool after before',
  ]);

  const valid = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_valid_iff');
  requireTokens0(failures, valid, 'valid-reflects-five-canonical-fields', [
    ').Valid expectedRank ↔', 'colourCheck = true',
    'payload.budgetChecked = true', 'after.LexLT before',
    'terminalResidualRankLTBool_eq_true_iff',
  ]);
  if (valid.includes('payload.colourChecked = true') ||
      valid.includes('payload.rankTag = expectedRank') ||
      valid.includes('payload.exactRouteClear = true') ||
      valid.includes('payload.chargeChecked = true')) {
    failures.push('valid-retained-duplicate-premise');
  }

  const colourFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_colour_iff');
  requireTokens0(failures, colourFailure, 'colour-route-reflection', [
    ').FailureAt expectedRank .colour ↔ colourCheck = false',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const noColour = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour');
  requireTokens0(failures, noColour, 'colour-first-route-excluded', [
    ').firstRoute expectedRank ≠ some .colour',
    'firstRoute_eq_some_iff_failureAt expectedRank .colour',
    'withComputedColourChargeExactRouteRankDescent_failureAt_colour_iff',
    'colourAccepted : colourCheck = true',
  ]);

  const chargeFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_charge_iff_false');
  requireTokens0(failures, chargeFailure, 'charge-route-impossible', [
    ').FailureAt expectedRank .charge ↔ False',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const noCharge = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge');
  requireTokens0(failures, noCharge, 'charge-first-route-excluded', [
    ').firstRoute expectedRank ≠ some .charge',
    'firstRoute_eq_some_iff_failureAt expectedRank .charge',
    'withComputedColourChargeExactRouteRankDescent_failureAt_charge_iff_false',
  ]);

  const exactFailure = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false');
  requireTokens0(failures, exactFailure, 'exact-route-impossible', [
    ').FailureAt expectedRank .exactRoute ↔ False',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const noExactRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute');
  requireTokens0(failures, noExactRoute, 'exact-first-route-excluded', [
    ').firstRoute expectedRank ≠ some .exactRoute',
    'firstRoute_eq_some_iff_failureAt expectedRank .exactRoute',
    'withComputedColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false',
  ]);

  const colourCheck = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorCanonicalColourCheck');
  requireTokens0(failures, colourCheck, 'canonical-colour-check', [
    'decide (2 ≤ (family.packetSelectorFootprint handle).length)',
  ]);

  const colourEvidence = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorCanonicalColourEligibility');
  requireTokens0(failures, colourEvidence, 'canonical-colour-evidence', [
    'packetSelectorFootprint handle).Sublist family.carrier',
    'family.packetSelectorFootprint_sublist_carrier handle',
    'family.packetSelectorFootprint_large handle',
    'family.packetSelectorCanonicalColourCheck handle = true',
  ]);

  const familyPayload = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent');
  requireTokens0(failures, familyPayload, 'canonical-family-colour-reflection', [
    '(family.packetSelectorPayloadAtom handle).payload',
    '|>.withComputedColourChargeExactRouteRankDescent',
    '(family.packetSelectorCanonicalColourCheck handle)', '(rankOf handle)',
    '(beforeRank handle)', '(afterRank handle)',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness');
  requireTokens0(failures, table, 'colour-reflected-table', [
    'rankOf := table.environment.rankOf',
    'packetSelectorPayloadFaithfulWithComputedColourChargeExactRouteRankDescent',
    'table.environment.rankOf beforeRank afterRank',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);

  const endpoint = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsColourReflectedFirstRouteFailure_of_selectorSilence');
  requireTokens0(failures, endpoint, 'colour-reflected-hb-outcome', [
    'withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness',
    ').noFaithful_of_selectorSilent dependencyTable',
    'packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent',
    'packetSelectorPayloadFailureAtWithComputedColourChargeExactRouteRankDescent',
    'route ≠ .colour ∧', 'route ≠ .charge ∧', 'route ≠ .rank ∧',
    'route ≠ .exactRoute ∧',
    'route ≠ .descent ∨',
    '¬(afterRank handle).LexLT (beforeRank handle)',
  ]);
  if (/\b(?:routesClear|bindingAccepted|rankBinding|descentBinding|exactRouteBinding)\b/u.test(endpoint)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const named = declarationBlock0(source,
    'terminalBN6_packet_colour_reflected_hb_first_route_failure');
  requireTokens0(failures, named, 'named-colour-reflected-endpoint', [
    'conclusion.existsColourReflectedFirstRouteFailure_of_selectorSilence',
    'table dependencyTable beforeRank afterRank silenceAccepted closureAccepted',
    'route ≠ .colour ∧', 'route ≠ .charge ∧', 'route ≠ .rank ∧',
    'route ≠ .exactRoute ∧',
  ]);

  return [...new Set(failures)];
}

test('Packet colour, charge, internal route, rank, and descent use authoritative inputs', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 31);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketColourRouteReflection\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketColourRouteReflection$/mu);
});

test('compiled inventory pins every reviewed colour-route theorem', async () => {
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

test('regression exercises forged colour, charge, route, rank, descent, grouped, and HB cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'chargeChecked := false', 'exactRouteClear := false',
    'withComputedColourChargeExactRouteRankDescent true 0 beforeRank',
    'withComputedColourChargeExactRouteRankDescent false 0 beforeRank',
    'some .rank', 'some .exactRoute', 'some .descent', 'some .colour',
    'some .frontier', 'some .charge', 'some .obligation',
    'some .activation', 'some .direction', 'some .budget',
    'rankDescent_of_withComputedColourChargeExactRouteRankDescent_check',
    'packetSelectorCanonicalColourCheck handle = true',
    'computedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour',
    'computedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge',
    'computedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank',
    'computedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute',
    'terminalBN6_packet_colour_reflected_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns internal colour-route reflection without semantic overclaim', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-colour-route-reflection');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-colour-route-reflection');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /canonical.*handle.*grouped.*footprint/iu);
  assert.match(milestone.scope,
    /cannot return.*colour.*charge.*rank.*exactRoute/iu);
  assert.match(milestone.nonClaim, /five remaining routes/iu);
  assert.match(milestone.nonClaim,
    /internal colour.*not.*external manuscript colour/iu);
  assert.equal(status.leanResidualTerminalPacketColourRouteReflectionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketColourRouteReflectionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketColourRouteReflectionScope,
    /arbitrary-finite.*grouped-footprint-colour.*colour-route-excluded/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /colour-route|colour route/iu, name);
    assert.match(semanticText0(text), /five remaining|remaining five/iu, name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketColourRouteReflectionAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-colour-route-reflection0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketColourRouteReflectionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketColourRouteReflection\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile colour-route reflection mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('colourChecked := colourCheck',
      'colourChecked := payload.colourChecked'),
    'computed-colour-projection'],
    [source.replace('{ payload.withComputedChargeExactRouteRankDescent expectedRank before after with',
      '{ payload with'), 'computed-colour-projection'],
    [source.replace('terminalResidualRankLTBool after before',
      'terminalResidualRankLTBool before after'), 'reflected-colour-preserved-fields'],
    [source.replace('expectedRank .colour ↔ colourCheck = false',
      'expectedRank .colour ↔ True'), 'colour-route-reflection'],
    [source.replace('decide (2 ≤ (family.packetSelectorFootprint handle).length)',
      'false'), 'canonical-colour-check'],
    [source.replace('family.packetSelectorFootprint_sublist_carrier handle',
      'by exact List.Sublist.refl family.carrier'), 'canonical-colour-evidence'],
    [source.replace('faithful :=\n          family.packetSelectorPayloadFaithfulWithComputedColourChargeExactRouteRankDescent',
      'faithful :=\n          table.environment.faithful'),
    'colour-reflected-table'],
    [source.replace('route ≠ .colour ∧',
      'route = .colour ∧'), 'colour-reflected-hb-outcome'],
    [`${source}\naxiom reflectedColourShortcut : True\n`,
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
