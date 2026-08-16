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
  'lean/PNP/ResidualTerminalPacketSelectorFaithfulnessTable.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorFaithfulnessTableAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorFaithfulnessTable.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_faithfulness_table.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_rankOf`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_hnActive`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_budgetActive`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_claim`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_faithful`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_binding`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsFaithfulHandle_of_computedTable`,
  `${NAMESPACE}.terminalBN6_packet_computed_faithfulness_hb_contradiction`,
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
    'PNP.ResidualTerminalPacketSelectorFaithfulnessRouting',
  ]);

  const constructor = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness');
  requireTokens0(failures, constructor, 'canonical-faithfulness-construction', [
    'rankOf := table.environment.rankOf',
    'faithful := family.packetSelectorPayloadFaithful',
    'table.environment.rankOf',
    'hnActive := table.environment.hnActive',
    'budgetActive := table.environment.budgetActive',
    'claim := table.claim',
  ]);
  if (constructor.includes('faithful := table.environment.faithful')) {
    failures.push('retained-free-faithfulness-function');
  }

  const binding = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_binding');
  requireTokens0(failures, binding, 'binding-by-construction', [
    'checkPacketSelectorFaithfulnessBinding = true',
    'checkPacketSelectorFaithfulnessBinding_eq_true_iff.2',
    'intro handle',
    'rfl',
  ]);
  if (/bindingAccepted/u.test(binding)) {
    failures.push('binding-premise-retained');
  }

  const faithful = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_faithful');
  requireTokens0(failures, faithful, 'computed-faithfulness-equation', [
    'environment.faithful handle =',
    'family.packetSelectorPayloadFaithful table.environment.rankOf handle',
    'rfl',
  ]);

  const witness = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsFaithfulHandle_of_computedTable');
  requireTokens0(failures, witness, 'binding-free-packet-witness', [
    'conclusion.existsFaithfulHandle_of_routesClear',
    'table.withComputedPacketSelectorFaithfulness routesClear',
    'table.withComputedPacketSelectorFaithfulness_binding',
  ]);
  if (/bindingAccepted/u.test(witness)) {
    failures.push('packet-witness-binding-premise');
  }

  const contradiction = declarationBlock0(source,
    'terminalBN6_packet_computed_faithfulness_hb_contradiction');
  requireTokens0(failures, contradiction, 'binding-free-hb-contradiction', [
    'terminalBN6_packet_selector_faithfulness_hb_contradiction conclusion',
    'table.withComputedPacketSelectorFaithfulness dependencyTable routesClear',
    'table.withComputedPacketSelectorFaithfulness_binding silenceAccepted',
    'closureAccepted',
  ]);
  if (/bindingAccepted/u.test(contradiction)) {
    failures.push('contradiction-binding-premise');
  }

  return [...new Set(failures)];
}

test('Packet faithfulness-table construction is arbitrary-finite and premise-tight', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});
test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 9);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorFaithfulnessTable\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorFaithfulnessTable$/mu);
});

test('compiled inventory pins every reviewed table-construction theorem', async () => {
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

test('regression exercises field preservation and binding-free composition', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'withComputedPacketSelectorFaithfulness_rankOf',
    'withComputedPacketSelectorFaithfulness_hnActive',
    'withComputedPacketSelectorFaithfulness_budgetActive',
    'withComputedPacketSelectorFaithfulness_claim',
    'withComputedPacketSelectorFaithfulness_faithful',
    'withComputedPacketSelectorFaithfulness_binding',
    'existsFaithfulHandle_of_computedTable',
    'terminalBN6_packet_computed_faithfulness_hb_contradiction',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns canonical table construction without widening semantics', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-selector-faithfulness-table');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-faithfulness-table');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /canonical.*faithfulness.*payload/iu);
  assert.match(milestone.scope, /without.*binding premise/iu);
  assert.match(milestone.nonClaim, /payload field.*explicit/iu);
  assert.match(milestone.nonClaim, /does not.*terminal candidate/iu);
  assert.equal(status.leanResidualTerminalPacketSelectorFaithfulnessTableFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorFaithfulnessTableAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketSelectorFaithfulnessTableScope,
    /arbitrary-finite.*canonical.*binding-free/iu);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(text, /canonical(?:ized)? (?:Packet )?faithfulness/iu, name);
    assert.match(text, /terminal data|terminal candidate/iu, name);
    assert.match(text, /ZeroSlack/iu, name);
  }
});
