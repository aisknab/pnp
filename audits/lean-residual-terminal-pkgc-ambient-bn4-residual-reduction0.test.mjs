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
  'lean/PNP/ResidualTerminalPkgCAmbientBN4ResidualReduction.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPkgCAmbientBN4ResidualReductionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPkgCAmbientBN4ResidualReduction.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_pkgc_ambient_bn4_residual_reduction.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalBN4ResidualCells_add_common',
  'TerminalPkgCAmbientBN4LedgerEmbedding.residualCells_eq_remainder',
  'terminalBN4ResidualLedgerOver',
  'TerminalPkgCAmbientBN4LedgerEmbedding.residualLedgerOver_eq_remainder',
  'TerminalPkgCAmbientBN4LedgerEmbedding.remainderKey_mem_ambientCanonicalKeys',
  'TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_eq_remainder',
  'TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_empty_of_remainder_empty',
  'TerminalPkgCAmbientBN4ResidualReductionOutcome',
  'classifyTerminalPkgCAmbientBN4ResidualReduction',
  'classifyTerminalPkgCAmbientBN4ResidualReduction_exhaustive',
  'TerminalPkgCComputedAmbientBN4ResidualReduction',
  'TerminalPkgCComputedAmbientBN4Cancellation.residualReduction',
  'TerminalPkgCComputedAmbientBN4Cancellation.residualLedger_empty_of_remainder_empty',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalBN4ResidualCells_add_common`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.residualCells_eq_remainder`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.residualLedgerOver_eq_remainder`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.remainderKey_mem_ambientCanonicalKeys`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_eq_remainder`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_empty_of_remainder_empty`,
  `${NAMESPACE}.classifyTerminalPkgCAmbientBN4ResidualReduction_exhaustive`,
  `${NAMESPACE}.TerminalPkgCComputedAmbientBN4Cancellation.residualLedger_empty_of_remainder_empty`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
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
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|sorry|admit|noncomputable|unsafe)\b/u.test(stripped)) {
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|remainderIsEmpty)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\bFin\b/u.test(stripped)) failures.push('fixed-carrier');
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPkgCAmbientBN4Ledger',
  ])) failures.push('closed-import');

  const common = declarationBlock0(source,
    'terminalBN4ResidualCells_add_common');
  requireTokens0(failures, common, 'balanced-common-invariance', [
    'classifyTerminalBN4KeyCancellation',
    'shared + positive',
    'shared + negative',
    'positive - negative',
    'negative - positive',
  ]);

  const perKey = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.residualCells_eq_remainder');
  requireTokens0(failures, perKey, 'per-key-residual-reduction', [
    'embedding.positiveMass_decomposition key',
    'embedding.negativeMass_decomposition key',
    'pair.restorationCancellation_balanced restorer key',
    'terminalBN4ResidualCells_add_common',
  ]);

  const ledger = declarationBlock0(source, 'terminalBN4ResidualLedgerOver');
  requireTokens0(failures, ledger, 'complete-ledger-definition', [
    'keys.flatMap fun key =>',
    '(terminalBN4CancelAtKey cells key).residualCells key',
  ]);

  const lift = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.residualLedgerOver_eq_remainder');
  requireTokens0(failures, lift, 'finite-ledger-lift', [
    'induction keys',
    'embedding.residualCells_eq_remainder key',
  ]);

  const complete = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.remainderKey_mem_ambientCanonicalKeys');
  requireTokens0(failures, complete, 'remainder-key-completeness', [
    'mem_terminalBN4CanonicalKeys_iff ambient cell.key',
    'embedding.exactDecomposition.mem_iff.mpr',
    'List.mem_append_right _ member',
  ]);

  const canonical = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_eq_remainder');
  requireTokens0(failures, canonical, 'canonical-residual-reduction', [
    'terminalBN4CanonicalKeys ambient',
    'embedding.residualLedgerOver_eq_remainder',
  ]);

  const empty = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_empty_of_remainder_empty');
  requireTokens0(failures, empty, 'empty-remainder-boundary', [
    'remainderEmpty : remainder = []',
    'embedding.canonicalResidualLedger_eq_remainder',
  ]);
  if (/remainderEmpty\s*:\s*Bool/u.test(empty)) {
    failures.push('empty-remainder-boundary');
  }

  const outcome = declarationBlock0(source,
    'TerminalPkgCAmbientBN4ResidualReductionOutcome');
  requireTokens0(failures, outcome, 'fail-closed-reduction-outcome', [
    '| reduced',
    'embedding : TerminalPkgCAmbientBN4LedgerEmbedding',
    'exactResidualReduction :',
    '| mismatch',
    'failure : ambient ≠',
  ]);

  const classifier = declarationBlock0(source,
    'classifyTerminalPkgCAmbientBN4ResidualReduction');
  requireTokens0(failures, classifier, 'mechanical-reduction-classifier', [
    'classifyTerminalPkgCAmbientBN4LedgerBinding',
    '| .embedded embedding =>',
    '.reduced embedding embedding.canonicalResidualLedger_eq_remainder',
    '| .mismatch failure => .mismatch failure',
  ]);
  if (/\b(?:success|accepted|valid)\s*:\s*Bool\b/u.test(classifier)) {
    failures.push('mechanical-reduction-classifier');
  }

  const computed = declarationBlock0(source,
    'TerminalPkgCComputedAmbientBN4ResidualReduction');
  requireTokens0(failures, computed, 'computed-proof-bearing-reduction', [
    'bridge : TerminalPkgCComputedAmbientBN4Cancellation',
    'exactResidualReduction :',
    'bridge.remainder',
  ]);

  const constructor = declarationBlock0(source,
    'TerminalPkgCComputedAmbientBN4Cancellation.residualReduction');
  requireTokens0(failures, constructor, 'computed-mechanical-constructor', [
    'TerminalPkgCComputedAmbientBN4ResidualReduction bridge',
    'bridge.embedding.canonicalResidualLedger_eq_remainder',
  ]);

  const computedEmpty = declarationBlock0(source,
    'TerminalPkgCComputedAmbientBN4Cancellation.residualLedger_empty_of_remainder_empty');
  requireTokens0(failures, computedEmpty, 'computed-empty-boundary', [
    'remainderEmpty : bridge.remainder = []',
    'bridge.embedding.canonicalResidualLedger_empty_of_remainder_empty',
    'remainderEmpty',
  ]);
  return [...new Set(failures)];
}

test('PkgC residual source proves an arbitrary-finite exact executable reduction', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 13-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 13);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPkgCAmbientBN4ResidualReduction\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPkgCAmbientBN4ResidualReduction$/mu);
});

test('compiled inventory pins every reviewed residual-reduction theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of AUDITED_DECLARATIONS) {
    const row = rows.get(name);
    assert.ok(row, name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
  }
  for (const name of MILESTONE_THEOREMS) {
    assert.equal(rows.get(name)?.kind, 'theorem', name);
    assert.ok(inventory.milestoneCandidates.some(
      (entry) => entry.name === name && typeof entry.kernelType === 'string'));
  }
});

test('regression covers ordering, duplicate keys, both remainders, and fail-closed classification', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'pkgCResidualRegressionRemainder',
    'pkgCResidualRegressionReorderedEmbedding',
    'mass := 5',
    'mass := 1',
    'mass := 4',
    'mass := 2',
    'remainderKey_mem_ambientCanonicalKeys',
    'pkgCResidualEmptyRegressionEmbedding',
    'canonicalResidualLedger_empty_of_remainder_empty',
    'pkgCResidualRegressionReductionTag',
    'pkgCResidualRegressionReductionMismatchTag',
    'TerminalPkgCComputedAmbientBN4ResidualReduction',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the explicit finite residual-reduction boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-pkgc-ambient-bn4-residual-reduction');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-pkgc-ambient-bn4-residual-reduction');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /complete canonical executable residual ledger/iu);
  assert.match(milestone.scope, /empty remainder/iu);
  assert.match(milestone.nonClaim, /explicit remainder[^.]*proof-bearing inputs/iu);
  assert.match(milestone.nonClaim,
    /does not[^.]*prove that the remainder is empty/iu);
  assert.equal(
    status.leanResidualTerminalPkgCAmbientBN4ResidualReductionFormalized, true);
  assert.equal(
    status.leanResidualTerminalPkgCAmbientBN4ResidualReductionAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPkgCAmbientBN4ResidualReductionScope,
    /complete-canonical-executable-residual-ledgers/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /finite PkgC ambient BN4 residual reduction/iu);
  assert.match(docs, /does not prove[^.]*remainder[^.]*empty/iu);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-pkgc-ambient-bn4-residual-reduction0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPkgCAmbientBN4ResidualReductionAxiomAudit\.lean[\s\S]{0,1800}-eq 13/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPkgCAmbientBN4ResidualReduction\.lean/u);
});

test('hostile residual-reduction mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('positive - negative := by', 'positive + negative := by'),
      'balanced-common-invariance'],
    [source.replace('embedding.positiveMass_decomposition key',
      'embedding.negativeMass_decomposition key'),
    'per-key-residual-reduction'],
    [source.replace('keys.flatMap fun key =>', 'keys.map fun key =>'),
      'complete-ledger-definition'],
    [source.replace('remainderEmpty : remainder = []',
      'remainderEmpty : True'), 'empty-remainder-boundary'],
    [source.replace('failure : ambient ≠', 'failure : ambient ='),
      'fail-closed-reduction-outcome'],
    [source.replace('bridge.embedding.canonicalResidualLedger_eq_remainder',
      'by rfl'), 'computed-mechanical-constructor'],
    [`${source}\naxiom residualReductionShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedResidualCarrier : Type := Fin 4\n`,
      'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
