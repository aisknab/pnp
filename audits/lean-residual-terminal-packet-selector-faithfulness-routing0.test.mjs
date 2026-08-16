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
  'lean/PNP/ResidualTerminalPacketSelectorFaithfulnessRouting.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorFaithfulnessRoutingAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorFaithfulnessRouting.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_faithfulness_routing.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.check_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_none_of_check`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.check_eq_false_of_firstRoute`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFaithful_eq_true_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_none`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.checkPacketSelectorRoutesClear_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.checkPacketSelectorFaithfulnessBinding_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketSelectorHandleConclusion.existsHandle`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsPacketSelectorHandle`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsFaithfulHandle_of_routesClear`,
  `${NAMESPACE}.terminalBN6_packet_selector_faithfulness_hb_contradiction`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
}

function auditedDeclarations0(source) {
  return declarationNames0(source).map((name) => `${NAMESPACE}.${name}`);
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|selector_faithfulness_complete|hb_negative_closure)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalHBExecutableSelectorSilenceInduction',
  ]);

  const route = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessRoute');
  requireTokens0(failures, route, 'closed-route-enum', [
    '| colour', '| frontier', '| charge', '| obligation', '| activation',
    '| direction', '| budget', '| rank', '| exactRoute', '| descent',
    'deriving Repr, DecidableEq',
  ]);

  const payload = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload');
  requireTokens0(failures, payload, 'data-only-payload', [
    'colourChecked : Bool',
    'frontierChecked : Bool',
    'chargeChecked : Bool',
    'obligationChecked : Bool',
    'activationChecked : Bool',
    'directionChecked : Bool',
    'budgetChecked : Bool',
    'rankTag : Fin rankCount',
    'exactRouteClear : Bool',
    'strictDescentClear : Bool',
  ]);
  if (/\bfaithful\s*:\s*Bool\b/u.test(payload)) {
    failures.push('caller-supplied-faithfulness');
  }

  const check = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.check');
  requireTokens0(failures, check, 'complete-payload-check', [
    'payload.colourChecked &&',
    'payload.frontierChecked &&',
    'payload.chargeChecked &&',
    'payload.obligationChecked &&',
    'payload.activationChecked &&',
    'payload.directionChecked &&',
    'payload.budgetChecked &&',
    'decide (payload.rankTag = expectedRank) &&',
    'payload.exactRouteClear &&',
    'payload.strictDescentClear',
  ]);

  const checkIff = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.check_eq_true_iff');
  requireTokens0(failures, checkIff, 'exact-payload-checker-equivalence', [
    'payload.check expectedRank = true ↔ payload.Valid expectedRank',
    'Bool.and_eq_true',
    'decide_eq_true_eq',
  ]);

  const firstRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.firstRoute');
  requireTokens0(failures, firstRoute, 'fixed-first-route-priority', [
    'if payload.colourChecked = true then',
    'if payload.frontierChecked = true then',
    'if payload.chargeChecked = true then',
    'if payload.obligationChecked = true then',
    'if payload.activationChecked = true then',
    'if payload.directionChecked = true then',
    'if payload.budgetChecked = true then',
    'if payload.rankTag = expectedRank then',
    'if payload.exactRouteClear = true then',
    'if payload.strictDescentClear = true then',
    'none',
    'else some .descent',
    'else some .exactRoute',
    'else some .rank',
    'else some .colour',
  ]);

  const faithful = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFaithful');
  requireTokens0(failures, faithful, 'canonical-source-payload-faithfulness', [
    '(family.packetSelectorPayloadAtom handle).payload.check (rankOf handle)',
  ]);

  const routeScan = declarationBlock0(source,
    'TerminalBN6GroupedFamily.checkPacketSelectorRoutesClear');
  requireTokens0(failures, routeScan, 'exhaustive-canonical-handle-scan', [
    'family.packetSelectorHandles.all fun handle =>',
    'family.packetSelectorPayloadFaithful rankOf handle',
  ]);

  const routeScanIff = declarationBlock0(source,
    'TerminalBN6GroupedFamily.checkPacketSelectorRoutesClear_eq_true_iff');
  requireTokens0(failures, routeScanIff, 'route-scan-all-handles', [
    '∀ handle : family.PacketSelectorHandle,',
    'family.mem_packetSelectorHandles handle',
    'List.all_eq_true.mpr',
  ]);

  const binding = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkPacketSelectorFaithfulnessBinding');
  requireTokens0(failures, binding, 'exact-hb-faithfulness-binding', [
    'family.packetSelectorHandles.all fun handle =>',
    'decide (table.environment.faithful handle =',
    'family.packetSelectorPayloadFaithful table.environment.rankOf handle)',
  ]);

  const handleWitness = declarationBlock0(source,
    'TerminalPacketSelectorHandleConclusion.existsHandle');
  requireTokens0(failures, handleWitness, 'all-packet-branches-have-handle', [
    'cases conclusion with',
    '| pair',
    '| fullSpan',
    '| balancedTriple',
    'let footprint := family.carrier.take 2',
    'List.take_sublist 2 family.carrier',
    'selectors footprint footprintSublist footprintLength',
  ]);

  const faithfulWitness = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsFaithfulHandle_of_routesClear');
  requireTokens0(failures, faithfulWitness,
    'computed-positive-packet-faithfulness', [
      'conclusion.existsPacketSelectorHandle',
      'family.checkPacketSelectorRoutesClear_eq_true_iff',
      'table.checkPacketSelectorFaithfulnessBinding_eq_true_iff',
      'binding.trans computedFaithful',
    ]);

  const contradiction = declarationBlock0(source,
    'terminalBN6_packet_selector_faithfulness_hb_contradiction');
  requireTokens0(failures, contradiction,
    'packet-faithfulness-hb-contradiction', [
      'conclusion.existsFaithfulHandle_of_routesClear realizerTable',
      'realizerTable.noFaithful_of_selectorSilent dependencyTable',
      'silenceAccepted closureAccepted handle',
      'rw [notFaithful] at faithful',
    ]);

  return [...new Set(failures)];
}

test('Packet selector-faithfulness routing is arbitrary-finite and premise-tight', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 20);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorFaithfulnessRouting\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorFaithfulnessRouting$/mu);
});

test('compiled inventory pins every reviewed selector-faithfulness theorem', async () => {
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

test('regression exercises routes, binding, Packet witness, and HB contradiction', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'check_eq_true_iff',
    'check_eq_false_of_firstRoute',
    'checkPacketSelectorRoutesClear_eq_true_iff',
    'checkPacketSelectorFaithfulnessBinding_eq_true_iff',
    'existsPacketSelectorHandle',
    'existsFaithfulHandle_of_routesClear',
    'terminalBN6_packet_selector_faithfulness_hb_contradiction',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns Packet selector-faithfulness routing without widening semantics', async () => {
  const [source, publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions] = await Promise.all([
    text0(SOURCE_PATH),
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
    ({ id }) => id === 'residual-terminal-packet-selector-faithfulness-routing');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-faithfulness-routing');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /positive Packet.*faithful canonical handle/iu);
  assert.match(milestone.scope, /contradiction.*selector silence/iu);
  assert.match(milestone.nonClaim, /route-clear payload checks.*explicit/iu);
  assert.match(milestone.nonClaim, /does not derive positive slack/iu);
  assert.equal(status.leanResidualTerminalPacketSelectorFaithfulnessRoutingFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorFaithfulnessRoutingAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalPacketSelectorFaithfulnessRoutingScope,
    /positive-bn6-packets.*selector-silence-contradiction/iu,
  );
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs,
    new RegExp(`${auditedDeclarations0(source).length} public declarations`, 'u'));
  assert.match(semanticText0(docs), /no caller-supplied faithful flag/iu);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /Packet selector-faithfulness routing/iu);
    assert.match(surface, /route-clear/iu);
    assert.match(surface, /positive slack.*remain/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorFaithfulnessRoutingAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-selector-faithfulness-routing0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorFaithfulnessRoutingAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorFaithfulnessRouting\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile Packet selector-faithfulness mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('payload.colourChecked &&', 'true &&'),
      'complete-payload-check'],
    [source.replace('decide (payload.rankTag = expectedRank) &&', 'true &&'),
      'complete-payload-check'],
    [source.replace('else some .descent', 'else none'),
      'fixed-first-route-priority'],
    [source.replace('else some .colour', 'else some .frontier'),
      'fixed-first-route-priority'],
    [source.replace('(family.packetSelectorPayloadAtom handle).payload.check (rankOf handle)',
      'true'), 'canonical-source-payload-faithfulness'],
    [source.replace('family.packetSelectorHandles.all fun handle =>',
      'family.packetSelectorHandles.tail.all fun handle =>'),
    'exhaustive-canonical-handle-scan'],
    [source.replace('decide (table.environment.faithful handle =',
      'decide (true ='), 'exact-hb-faithfulness-binding'],
    [source.replace('family.carrier.take 2', 'family.carrier.take 1'),
      'all-packet-branches-have-handle'],
    [source.replace('binding.trans computedFaithful', 'computedFaithful'),
      'computed-positive-packet-faithfulness'],
    [source.replace('realizerTable.noFaithful_of_selectorSilent dependencyTable',
      'realizerTable.noFaithful_of_noStrictEquivalentGain dependencyTable'),
    'packet-faithfulness-hb-contradiction'],
    [source.replace('rankTag : Fin rankCount',
      'faithful : Bool\n  rankTag : Fin rankCount'),
    'caller-supplied-faithfulness'],
    [`${source}\naxiom selectorFaithfulnessShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPacketRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem selector_faithfulness_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
