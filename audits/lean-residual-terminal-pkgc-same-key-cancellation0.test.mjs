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
  'lean/PNP/ResidualTerminalPkgCSameKeyCancellation.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPkgCSameKeyCancellationAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPkgCSameKeyCancellation.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_pkgc_same_key_cancellation.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalPkgCRestorationCancellationCellsForAtom',
  'terminalPkgCRestorationCancellationCellsForAtom_key_eq',
  'terminalPkgCRestorationCancellationCellsForAtom_balanced',
  'terminalPkgCRestorationCancellationCellsForAtoms',
  'terminalPkgCRestorationCancellationCellsForAtoms_length',
  'terminalBN4PositiveMass_append',
  'terminalBN4NegativeMass_append',
  'terminalPkgCRestorationCancellationCellsForAtoms_balanced',
  'TerminalPkgCSeparatingPair.restorationCancellationCells',
  'TerminalPkgCSeparatingPair.restorationCancellationCells_length',
  'TerminalPkgCSeparatingPair.restorationCancellation_balanced',
  'TerminalPkgCSeparatingPair.restorationCancellation_residualCells_empty',
  'TerminalPkgCSeparatingPair.restorationCancellation_signedMass_zero',
  'TerminalPkgCSameKeyCancellationRealization',
  'TerminalPkgCSeparatingPair.sameKeyCancellationRealization',
  'TerminalPkgCSameKeyCancellationOutcome',
  'classifyTerminalPkgCSameKeyCancellation',
  'terminalPkgC_typedRestoration_sameKeyCancellation',
  'TerminalPkgCSameKeyCancellationSilent',
  'terminalPkgC_sameKeyCancellation_silence_singletonizes',
  'classifyTerminalPkgCSameKeyCancellation_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalPkgCRestorationCancellationCellsForAtom_key_eq`,
  `${NAMESPACE}.terminalPkgCRestorationCancellationCellsForAtom_balanced`,
  `${NAMESPACE}.terminalPkgCRestorationCancellationCellsForAtoms_length`,
  `${NAMESPACE}.terminalPkgCRestorationCancellationCellsForAtoms_balanced`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.restorationCancellationCells_length`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.restorationCancellation_balanced`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.restorationCancellation_residualCells_empty`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.restorationCancellation_signedMass_zero`,
  `${NAMESPACE}.terminalPkgC_typedRestoration_sameKeyCancellation`,
  `${NAMESPACE}.terminalPkgC_sameKeyCancellation_silence_singletonizes`,
  `${NAMESPACE}.classifyTerminalPkgCSameKeyCancellation_exhaustive`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|ambientLedgerLinked)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPkgCTypedRestoration',
  ])) failures.push('closed-import');

  const atomCells = declarationBlock0(source,
    'terminalPkgCRestorationCancellationCellsForAtom');
  requireTokens0(failures, atomCells, 'canonical-opposite-sign-cells', [
    '(restorer.quotientCoordinate atom).key',
    'sign := .positive',
    '(restorer.fullCoordinate (restorer.restore atom)).key',
    'sign := .negative',
    'mass := 1',
  ]);
  if ((atomCells.match(/sign := \.positive/gu) ?? []).length !== 1
      || (atomCells.match(/sign := \.negative/gu) ?? []).length !== 1
      || (atomCells.match(/mass := 1/gu) ?? []).length !== 2) {
    failures.push('canonical-opposite-sign-cells');
  }
  if (/\(cells\s*:/u.test(atomCells)) failures.push('caller-supplied-cells');

  const keyEquality = declarationBlock0(source,
    'terminalPkgCRestorationCancellationCellsForAtom_key_eq');
  requireTokens0(failures, keyEquality, 'nested-key-preservation', [
    'congrArg TerminalBN5ShadowCoordinate.key',
    'restorer.restore_preserves_coordinate atom',
  ]);

  const atomBalanced = declarationBlock0(source,
    'terminalPkgCRestorationCancellationCellsForAtom_balanced');
  requireTokens0(failures, atomBalanced, 'atom-mass-balance', [
    'terminalBN4PositiveMass', 'terminalBN4NegativeMass',
    'terminalPkgCRestorationCancellationCellsForAtom_key_eq',
  ]);
  if ((atomBalanced.match(/terminalBN4PositiveMass/gu) ?? []).length !== 2
      || (atomBalanced.match(/terminalBN4NegativeMass/gu) ?? []).length !== 2) {
    failures.push('atom-mass-balance');
  }

  const atomList = declarationBlock0(source,
    'terminalPkgCRestorationCancellationCellsForAtoms');
  requireTokens0(failures, atomList, 'unbounded-atom-ledger', [
    'atoms.flatMap',
    'terminalPkgCRestorationCancellationCellsForAtom restorer',
  ]);

  const pairCells = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.restorationCancellationCells');
  requireTokens0(failures, pairCells, 'complete-pair-ledger', [
    'pair.left ++ pair.right',
    'terminalPkgCRestorationCancellationCellsForAtoms restorer',
  ]);

  const residual = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.restorationCancellation_residualCells_empty');
  requireTokens0(failures, residual, 'computed-empty-residual', [
    'terminalBN4CancelAtKey',
    'restorationCancellation_balanced',
    'residualCells', '= []',
  ]);
  if ((residual.match(/terminalBN4CancelAtKey/gu) ?? []).length !== 2) {
    failures.push('computed-empty-residual');
  }

  const signed = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.restorationCancellation_signedMass_zero');
  requireTokens0(failures, signed, 'zero-signed-ledger', [
    'terminalBN4InputSignedMass',
    'restorationCancellation_balanced', '= 0',
  ]);

  const realization = declarationBlock0(source,
    'TerminalPkgCSameKeyCancellationRealization');
  requireTokens0(failures, realization, 'proof-bearing-cancellation', [
    'typedRealization : TerminalPkgCTypedRestorationRealization',
    'canonical : cells = pair.restorationCancellationCells restorer',
    'cellCount :', 'balanced :', 'residualCellsEmpty :', 'signedMassZero :',
  ]);

  const constructor = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.sameKeyCancellationRealization');
  requireTokens0(failures, constructor, 'computed-realization', [
    'pair.typedRestorationRealization restorer',
    'cells := pair.restorationCancellationCells restorer',
    'canonical := rfl',
    'pair.restorationCancellation_residualCells_empty restorer',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPkgCSameKeyCancellationOutcome');
  requireTokens0(failures, outcome, 'two-branch-outcome', [
    '| singletonized', '| cancelled',
    'TerminalPkgCSameKeyCancellationRealization pair restorer',
  ]);

  const totalTheorem = declarationBlock0(source,
    'terminalPkgC_typedRestoration_sameKeyCancellation');
  requireTokens0(failures, totalTheorem, 'typed-cancellation-totality', [
    'system.DisjointPairsSingletonized',
    'TerminalPkgCSameKeyCancellationRealization pair restorer',
    'classifyTerminalPkgCSameKeyCancellation system restorer',
  ]);

  const silence = declarationBlock0(source,
    'TerminalPkgCSameKeyCancellationSilent');
  requireTokens0(failures, silence, 'negative-silence-boundary', [
    '∀ pair : TerminalPkgCSeparatingPair system',
    '¬ Nonempty (TerminalPkgCSameKeyCancellationRealization pair restorer)',
  ]);
  if (/\b(?:silent|accepted|valid)\s*:\s*Bool\b/u.test(silence)) {
    failures.push('positive-silence-flag');
  }

  const singletonizes = declarationBlock0(source,
    'terminalPkgC_sameKeyCancellation_silence_singletonizes');
  requireTokens0(failures, singletonizes, 'silence-singletonizes', [
    'TerminalPkgCSameKeyCancellationSilent system restorer',
    'terminalPkgC_typedRestoration_sameKeyCancellation system restorer',
    'system.DisjointPairsSingletonized',
  ]);

  if (/\bFin\b/u.test(stripped)) failures.push('fixed-carrier');
  return [...new Set(failures)];
}

test('PkgC source computes exact-coordinate same-key cancellation', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 21-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 21);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPkgCSameKeyCancellation\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPkgCSameKeyCancellation$/mu);
});

test('compiled inventory pins every same-key cancellation declaration', async () => {
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

test('regression covers shared-key mass, empty residual, totality, and silence', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'PkgCSameKeyRegressionFullCandidate',
    'pkgCSameKeyRegressionCoordinate',
    'pkgCSameKeyRegressionRestorer',
    'restorationCancellationCells', '= 6',
    'terminalBN4PositiveMass', '= 3',
    'terminalBN4NegativeMass',
    'terminalBN4CancelAtKey', '= []',
    'terminalBN4InputSignedMass', '= 0',
    'pkgCSameKeyRegressionOutcomeTag',
    'terminalPkgC_typedRestoration_sameKeyCancellation',
    'terminalPkgC_sameKeyCancellation_silence_singletonizes',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite generated cancellation boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-pkgc-same-key-cancellation');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-pkgc-same-key-cancellation');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /opposite-sign unit cells/u);
  assert.match(milestone.nonClaim, /ambient BN4 ledger/u);
  assert.equal(status.leanResidualTerminalPkgCSameKeyCancellationFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPkgCSameKeyCancellationAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPkgCSameKeyCancellationScope,
    /every-key-balanced-empty-residual/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /finite PkgC typed restoration same-key cancellation/iu);
  assert.match(docs,
    /explicit ambient BN4 ledger[\s\S]{0,180}does not derive[\s\S]{0,100}(?:binding|ledger)[\s\S]{0,80}candidate/iu);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-pkgc-same-key-cancellation0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPkgCSameKeyCancellationAxiomAudit\.lean[\s\S]{0,1800}-eq 21/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPkgCSameKeyCancellation\.lean/u);
});

test('hostile same-key cancellation mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('sign := .positive', 'sign := .negative'),
      'canonical-opposite-sign-cells'],
    [source.replace('mass := 1', 'mass := 2'),
      'canonical-opposite-sign-cells'],
    [source.replace('congrArg TerminalBN5ShadowCoordinate.key',
      'congrArg TerminalBN5ShadowCoordinate.frontier'),
      'nested-key-preservation'],
    [source.replace('pair.left ++ pair.right', 'pair.left'),
      'complete-pair-ledger'],
    [source.replace('terminalBN4NegativeMass', 'terminalBN4PositiveMass'),
      'atom-mass-balance'],
    [source.replace('terminalBN4CancelAtKey', 'classifyTerminalBN4KeyCancellation'),
      'computed-empty-residual'],
    [source.replace('¬ Nonempty (TerminalPkgCSameKeyCancellationRealization pair restorer)',
      'True'), 'negative-silence-boundary'],
    [`${source}\naxiom cancellationShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedCancellationCarrier : Type := Fin 4\n`,
      'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
