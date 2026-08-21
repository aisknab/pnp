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
  'lean/PNP/ResidualTerminalPacketBudgetNoLowerComposition.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketBudgetNoLowerCompositionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketBudgetNoLowerComposition.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_budget_no_lower_composition.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.checkTerminalPacketBudgetNoLowerComposition_eq_true_iff`,
  `${NAMESPACE}.terminal_packet_budget_no_lower_composition_excludes_gain_and_packet`,
  `${NAMESPACE}.checkTerminalPacketBudgetNoLowerComposition_eq_false_of_feasible_gain`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.checkTerminalPacketBudgetNoLowerComposition_eq_false`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|no_lower_ledger_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketNoLowerLedger',
    'PNP.ResidualTerminalBudgetNoLowerLedger',
  ]);

  const accepted = declarationBlock0(source,
    'TerminalPacketBudgetNoLowerAccepted');
  requireTokens0(failures, accepted, 'exact-component-proposition', [
    'TerminalBudgetNoLowerLedgerAccepted budget candidate model',
    'table.PacketNoLowerLedgerAccepted dependencyTable beforeRank afterRank',
    'candidate.toImplementation',
  ]);
  if (/accepted\s*:\s*Bool/u.test(accepted)) {
    failures.push('caller-acceptance');
  }

  const checker = declarationBlock0(source,
    'checkTerminalPacketBudgetNoLowerComposition');
  requireTokens0(failures, checker, 'computed-composition', [
    'checkTerminalBudgetNoLowerLedger budget candidate model &&',
    'table.checkPacketNoLowerLedger dependencyTable beforeRank afterRank',
    'candidate.toImplementation',
  ]);
  if (/\b(?:budgetAccepted|packetAccepted|compositionAccepted)\s*:\s*Bool/u.test(checker)) {
    failures.push('caller-acceptance');
  }

  const reflection = declarationBlock0(source,
    'checkTerminalPacketBudgetNoLowerComposition_eq_true_iff');
  requireTokens0(failures, reflection, 'exact-reflection', [
    'TerminalPacketBudgetNoLowerAccepted',
    'checkTerminalBudgetNoLowerLedger_eq_true_iff',
    'checkPacketNoLowerLedger_eq_true_iff',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet');
  requireTokens0(failures, endpoint, 'joint-semantic-endpoint', [
    'allTerminalSupportSeeds',
    'budget.Fits candidate model seed',
    'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    '¬TerminalBN6PacketConclusion family',
    'terminal_budget_no_lower_ledger_excludes_feasible_gain',
    'terminalBN6_packet_no_lower_ledger_excludes_positive_packet',
  ]);

  const gainReject = declarationBlock0(source,
    'checkTerminalPacketBudgetNoLowerComposition_eq_false_of_feasible_gain');
  requireTokens0(failures, gainReject, 'gain-rejection', [
    'governed', 'fits', 'gain', '= false',
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet',
  ]);

  const packetReject = declarationBlock0(source,
    'TerminalBN6PacketConclusion.checkTerminalPacketBudgetNoLowerComposition_eq_false');
  requireTokens0(failures, packetReject, 'packet-rejection', [
    'conclusion : TerminalBN6PacketConclusion family',
    '= false',
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet',
  ]);

  return [...new Set(failures)];
}

test('Packet-budget composition recomputes both ledgers over one candidate', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 6);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketBudgetNoLowerComposition\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketBudgetNoLowerComposition$/mu);
});

test('compiled inventory pins every reviewed Packet-budget theorem', async () => {
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

test('regression covers joint acceptance and independent fail-closed branches', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'oneGateBudget', 'fullBudget', 'emptyFamily',
    'TerminalPacketBudgetNoLowerAccepted',
    'checkTerminalPacketBudgetNoLowerComposition',
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet',
    'checkTerminalPacketBudgetNoLowerComposition_eq_false_of_feasible_gain',
    'checkTerminalPacketBudgetNoLowerComposition_eq_false',
    'IsSemanticallyMinimum', 'StrictEquivalentGain',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite two-branch composition', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, terminology, auditQuestions, bridge] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/terminology_crosswalk.md'),
    text0('docs/audit_questions.md'), text0('docs/lean_bridge.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-budget-no-lower-composition');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-budget-no-lower-composition');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /same direct-wire candidate.*budget-feasible.*positive Packet/iu);
  assert.match(milestone.scope,
    /one.*Boolean|one.*checker/iu);
  assert.match(milestone.nonClaim,
    /caps.*Packet family.*tables.*supplied/iu);
  assert.match(milestone.nonClaim,
    /finite two-branch.*not.*complete no-lower.*ZeroSlack.*PCCMin/iu);
  assert.equal(
    status.leanResidualTerminalPacketBudgetNoLowerCompositionFormalized, true);
  assert.equal(
    status.leanResidualTerminalPacketBudgetNoLowerCompositionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketBudgetNoLowerCompositionScope,
    /same-candidate.*budget.*Packet.*gain.*exclusion/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['terminology', terminology],
    ['audit questions', auditQuestions], ['bridge', bridge],
  ]) {
    assert.match(semanticText0(text), /Packet.*budget.*no-lower|budget.*Packet.*no-lower/iu, name);
    assert.match(semanticText0(text), /not.*complete|finite.*two-branch|remain.*supplied/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketBudgetNoLowerCompositionAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-packet-budget-no-lower-composition0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketBudgetNoLowerCompositionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketBudgetNoLowerComposition\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile Packet-budget composition mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'TerminalBudgetNoLowerLedgerAccepted budget candidate model ∧',
      'True ∧'), 'exact-component-proposition'],
    [source.replace(
      'table.PacketNoLowerLedgerAccepted dependencyTable beforeRank afterRank',
      'True'), 'exact-component-proposition'],
    [source.replace(
      'checkTerminalBudgetNoLowerLedger budget candidate model &&',
      'true &&'), 'computed-composition'],
    [source.replace(
      'table.checkPacketNoLowerLedger dependencyTable beforeRank afterRank',
      'true'), 'computed-composition'],
    [source.replace('candidate.toImplementation family rankCount',
      'redundantIdentityImplementation family rankCount'),
    'exact-component-proposition'],
    [source.replace('IsSemanticallyMinimum', 'True'),
      'joint-semantic-endpoint'],
    [source.replace('¬TerminalBN6PacketConclusion family', 'True'),
      'joint-semantic-endpoint'],
    [`${source}\naxiom packetBudgetCompositionShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPacketBudgetCarrier : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem no_lower_ledger_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
