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
  'lean/PNP/ResidualTerminalPkgCAmbientBN4Ledger.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPkgCAmbientBN4LedgerAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPkgCAmbientBN4Ledger.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_pkgc_ambient_bn4_ledger.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalBN4PositiveMass_perm',
  'terminalBN4NegativeMass_perm',
  'TerminalPkgCAmbientBN4LedgerEmbedding',
  'TerminalPkgCAmbientBN4LedgerEmbedding.generatedCell_mem_ambient',
  'TerminalPkgCAmbientBN4LedgerEmbedding.cellMultiplicity',
  'TerminalPkgCAmbientBN4LedgerEmbedding.length_eq',
  'TerminalPkgCAmbientBN4LedgerEmbedding.positiveMass_decomposition',
  'TerminalPkgCAmbientBN4LedgerEmbedding.negativeMass_decomposition',
  'TerminalPkgCAmbientBN4LedgerEmbedding.signedMass_eq_remainder',
  'TerminalPkgCAmbientBN4LedgerEmbedding.residualSignedContribution_eq_remainder',
  'TerminalPkgCAmbientBN4LedgerBindingOutcome',
  'classifyTerminalPkgCAmbientBN4LedgerBinding',
  'classifyTerminalPkgCAmbientBN4LedgerBinding_exhaustive',
  'TerminalPkgCComputedAmbientBN4Cancellation',
  'TerminalPkgCComputedAmbientBN4Cancellation.generatedCell_usesCanonicalAtom',
  'TerminalComputedBN4ActivationCancellation.pkgCAmbientCancellation',
  'terminalPkgC_computedAmbientBN4_silence_singletonizes',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalBN4PositiveMass_perm`,
  `${NAMESPACE}.terminalBN4NegativeMass_perm`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.generatedCell_mem_ambient`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.cellMultiplicity`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.length_eq`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.positiveMass_decomposition`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.negativeMass_decomposition`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.signedMass_eq_remainder`,
  `${NAMESPACE}.TerminalPkgCAmbientBN4LedgerEmbedding.residualSignedContribution_eq_remainder`,
  `${NAMESPACE}.classifyTerminalPkgCAmbientBN4LedgerBinding_exhaustive`,
  `${NAMESPACE}.TerminalPkgCComputedAmbientBN4Cancellation.generatedCell_usesCanonicalAtom`,
  `${NAMESPACE}.terminalPkgC_computedAmbientBN4_silence_singletonizes`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|ambientLedgerDerived)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPkgCSameKeyCancellation',
  ])) failures.push('closed-import');

  const embedding = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding');
  requireTokens0(failures, embedding, 'exact-multiset-decomposition', [
    'exactDecomposition : ambient.Perm',
    'pair.restorationCancellationCells restorer ++ remainder',
  ]);
  if (/\b(?:subset|Subset|∀ cell)\b/u.test(embedding)) {
    failures.push('exact-multiset-decomposition');
  }

  const membership = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.generatedCell_mem_ambient');
  requireTokens0(failures, membership, 'generated-cell-membership', [
    'embedding.exactDecomposition.mem_iff.mpr',
    'List.mem_append_left remainder member',
  ]);

  const multiplicity = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.cellMultiplicity');
  requireTokens0(failures, multiplicity, 'exact-cell-multiplicity', [
    'ambient.count cell',
    'embedding.exactDecomposition.count_eq cell',
    'List.count_append',
    'remainder.count cell',
  ]);

  const positive = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.positiveMass_decomposition');
  requireTokens0(failures, positive, 'positive-mass-decomposition', [
    'terminalBN4PositiveMass_perm embedding.exactDecomposition key',
    'terminalBN4PositiveMass_append',
    'terminalBN4PositiveMass remainder key',
  ]);

  const negative = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.negativeMass_decomposition');
  requireTokens0(failures, negative, 'negative-mass-decomposition', [
    'terminalBN4NegativeMass_perm embedding.exactDecomposition key',
    'terminalBN4NegativeMass_append',
    'terminalBN4NegativeMass remainder key',
  ]);

  const signed = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.signedMass_eq_remainder');
  requireTokens0(failures, signed, 'remainder-signed-mass', [
    'terminalBN4InputSignedMass ambient key',
    'terminalBN4InputSignedMass remainder key',
    'embedding.positiveMass_decomposition key',
    'embedding.negativeMass_decomposition key',
    'pair.restorationCancellation_balanced restorer key',
  ]);

  const residual = declarationBlock0(source,
    'TerminalPkgCAmbientBN4LedgerEmbedding.residualSignedContribution_eq_remainder');
  requireTokens0(failures, residual, 'remainder-residual-contribution', [
    'terminalBN4CancelAtKey_signedContribution_exact',
    'embedding.signedMass_eq_remainder',
    'terminalBN4InputSignedMass remainder key',
  ]);

  const classifier = declarationBlock0(source,
    'classifyTerminalPkgCAmbientBN4LedgerBinding');
  requireTokens0(failures, classifier, 'canonical-fail-closed-classifier', [
    'if exact : ambient =',
    'pair.restorationCancellationCells restorer ++ remainder',
    '.embedded ⟨List.Perm.of_eq exact⟩',
    '.mismatch exact',
  ]);
  if (/\b(?:decide|success|accepted|valid)\b/u.test(classifier)) {
    failures.push('canonical-fail-closed-classifier');
  }

  const computed = declarationBlock0(source,
    'TerminalPkgCComputedAmbientBN4Cancellation');
  requireTokens0(failures, computed, 'candidate-kernel-retention', [
    'bn4Kernel : TerminalComputedBN4ActivationCancellation result ambient',
    'remainder : List (TerminalBN4ActivationCell',
    'embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient',
  ]);

  const canonical = declarationBlock0(source,
    'TerminalPkgCComputedAmbientBN4Cancellation.generatedCell_usesCanonicalAtom');
  requireTokens0(failures, canonical, 'candidate-derived-canonical-atoms', [
    'terminalBN4CellsUseCanonicalAtoms_iff result ambient',
    'bridge.bn4Kernel.cellsUseCanonicalAtoms cell',
    'bridge.embedding.generatedCell_mem_ambient cell member',
    'cell.key.atom ∈ result.requestAtoms',
  ]);

  const singletonizes = declarationBlock0(source,
    'terminalPkgC_computedAmbientBN4_silence_singletonizes');
  requireTokens0(failures, singletonizes, 'complete-ambient-silence-boundary', [
    'complete : ∀ pair : TerminalPkgCSeparatingPair system',
    '∃ remainder, TerminalPkgCAmbientBN4LedgerEmbedding pair restorer',
    'silent : ∀ pair : TerminalPkgCSeparatingPair system',
    '¬ Nonempty (TerminalPkgCComputedAmbientBN4Cancellation result ambient',
    'terminalPkgC_sameKeyCancellation_silence_singletonizes system restorer',
    'kernel.pkgCAmbientCancellation pair restorer remainder',
  ]);
  if (/\b(?:silent|accepted|valid)\s*:\s*Bool\b/u.test(singletonizes)) {
    failures.push('complete-ambient-silence-boundary');
  }

  if (/\bFin\b/u.test(stripped)) failures.push('fixed-carrier');
  return [...new Set(failures)];
}

test('PkgC source embeds the generated cancellation as an exact ambient BN4 subledger', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 17-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 17);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPkgCAmbientBN4Ledger\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPkgCAmbientBN4Ledger$/mu);
});

test('compiled inventory pins every ambient-ledger declaration', async () => {
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

test('regression covers exact multiplicity, nonzero remainder, classifier, and computed bridge', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'pkgCAmbientRegressionRemainder',
    'pkgCAmbientRegressionLedger',
    'pkgCAmbientRegressionEmbedding',
    'pkgCAmbientRegressionLedger.length = 7',
    'terminalBN4PositiveMass', '= 8',
    'terminalBN4NegativeMass', '= 3',
    'terminalBN4InputSignedMass', '= 5',
    'residualSignedContribution_eq_remainder',
    'pkgCAmbientRegressionBindingTag',
    'pkgCAmbientRegressionMismatchTag',
    'TerminalPkgCComputedAmbientBN4Cancellation',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the explicit finite ambient-ledger boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-pkgc-ambient-bn4-ledger');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-pkgc-ambient-bn4-ledger');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /exact multiset/iu);
  assert.match(milestone.scope, /remainder/iu);
  assert.match(milestone.nonClaim, /explicit proof-bearing inputs/iu);
  assert.match(milestone.nonClaim, /does not derive[^.]*ambient ledger/iu);
  assert.equal(status.leanResidualTerminalPkgCAmbientBN4LedgerFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPkgCAmbientBN4LedgerAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPkgCAmbientBN4LedgerScope,
    /exact-multiset-embedding/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /finite PkgC ambient BN4 ledger embedding/iu);
  assert.match(docs, /does not derive[^.]*ambient ledger/iu);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-pkgc-ambient-bn4-ledger0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPkgCAmbientBN4LedgerAxiomAudit\.lean[\s\S]{0,1800}-eq 17/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPkgCAmbientBN4Ledger\.lean/u);
});

test('hostile ambient-ledger mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('exactDecomposition : ambient.Perm',
      'exactDecomposition : ∀ cell, cell ∈ ambient → cell ∈'),
    'exact-multiset-decomposition'],
    [source.replace('++ remainder', ''),
      'exact-multiset-decomposition'],
    [source.replace('embedding.exactDecomposition.count_eq cell',
      'embedding.exactDecomposition.length_eq'),
    'exact-cell-multiplicity'],
    [source.replace('terminalBN4PositiveMass_perm embedding.exactDecomposition key',
      'terminalBN4NegativeMass_perm embedding.exactDecomposition key'),
    'positive-mass-decomposition'],
    [source.replace('bn4Kernel : TerminalComputedBN4ActivationCancellation result ambient',
      'bn4Kernel : True'), 'candidate-kernel-retention'],
    [source.replace('complete : ∀ pair : TerminalPkgCSeparatingPair system',
      'complete : ∃ pair : TerminalPkgCSeparatingPair system'),
    'complete-ambient-silence-boundary'],
    [`${source}\naxiom ambientShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedAmbientCarrier : Type := Fin 4\n`,
      'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
