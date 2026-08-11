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
  'lean/PNP/ResidualTerminalPkgCSeparatingConsumers.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPkgCSeparatingConsumersAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPkgCSeparatingConsumers.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_pkgc_separating_consumers.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalPkgCConsumerIsSingleton',
  'terminalPkgCConsumerIsSingleton_eq_true_iff',
  'terminalPkgCDisjointBool',
  'terminalPkgCDisjointBool_eq_true_iff',
  'terminalPkgCConsumerPairs',
  'mem_terminalPkgCConsumerPairs_iff',
  'terminalPkgCPairNeedsRestoration',
  'terminalPkgCPairNeedsRestoration_eq_true_iff',
  'firstTerminalPkgCSeparatingPair?',
  'TerminalPkgCSeparatingPair',
  'terminalPkgCSeparatingPairOfFound',
  'firstTerminalPkgCSeparatingPair?_sound',
  'firstTerminalPkgCSeparatingPair?_eq_none_iff',
  'TerminalPkgCRestorationUniverse',
  'TerminalPkgCSeparatingPair.quotientUnits',
  'TerminalPkgCSeparatingPair.quotientUnits_length',
  'TerminalPkgCSeparatingPair.quotientUnits_nonempty',
  'TerminalPkgCRestorationUniverse.fullRestorations',
  'TerminalPkgCExactCoordinateCoverage',
  'terminalPkgC_restorationEdge_preservesCoordinate',
  'TerminalPkgCNamedLocalRoute',
  'TerminalBN5HallDeficit.pkgCNamedLocalRoute',
  'TerminalBN5HallDeficit.pkgCRestorationNotSilent',
  'TerminalPkgCSeparatingConsumersOutcome',
  'classifyTerminalPkgCSeparatingConsumers',
  'terminalPkgC_separatingConsumers_restorationDichotomy',
  'classifyTerminalPkgCSeparatingConsumers_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalPkgCPairNeedsRestoration_eq_true_iff`,
  `${NAMESPACE}.firstTerminalPkgCSeparatingPair?_sound`,
  `${NAMESPACE}.firstTerminalPkgCSeparatingPair?_eq_none_iff`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.quotientUnits_length`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.quotientUnits_nonempty`,
  `${NAMESPACE}.terminalPkgC_restorationEdge_preservesCoordinate`,
  `${NAMESPACE}.TerminalBN5HallDeficit.pkgCRestorationNotSilent`,
  `${NAMESPACE}.terminalPkgC_separatingConsumers_restorationDichotomy`,
  `${NAMESPACE}.classifyTerminalPkgCSeparatingConsumers_exhaustive`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|bn6Complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalConsumerAntichainNormalForm',
  ])) failures.push('closed-import');

  const scan = declarationBlock0(source,
    'firstTerminalPkgCSeparatingPair?');
  requireTokens0(failures, scan, 'canonical-first-scan', [
    'terminalPkgCConsumerPairs system', '.find?',
    'terminalPkgCPairNeedsRestoration pair.1 pair.2',
  ]);

  const pair = declarationBlock0(source, 'TerminalPkgCSeparatingPair');
  requireTokens0(failures, pair, 'proof-bearing-pair', [
    'leftMember', 'rightMember', 'TerminalV54Disjoint', 'nonsingleton',
  ]);

  const noneIff = declarationBlock0(source,
    'firstTerminalPkgCSeparatingPair?_eq_none_iff');
  requireTokens0(failures, noneIff, 'singletonization-exactness', [
    'system.DisjointPairsSingletonized', 'List.find?_isSome',
    'terminalPkgCConsumerIsSingleton', 'Bool.noConfusion',
  ]);

  const restoration = declarationBlock0(source,
    'TerminalPkgCRestorationUniverse');
  requireTokens0(failures, restoration, 'explicit-restoration-universe', [
    'coordinateOf : Atom -> Coordinate',
    'fullRestorationCoordinates : List Atom -> List Atom -> List Coordinate',
  ]);
  if (restoration.includes('quotientUnits')) {
    failures.push('caller-supplied-quotient-units');
  }

  const quotientUnits = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.quotientUnits');
  requireTokens0(failures, quotientUnits, 'canonical-quotient-generation', [
    'terminalBN5IndexFullUnitsFrom 0', 'pair.left ++ pair.right',
    '.map restoration.coordinateOf',
  ]);

  const nonempty = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.quotientUnits_nonempty');
  requireTokens0(failures, nonempty, 'nonvacuous-quotient', [
    'system.consumerNonempty', 'pair.leftMember', 'leftShape',
  ]);

  const coverage = declarationBlock0(source,
    'TerminalPkgCExactCoordinateCoverage');
  requireTokens0(failures, coverage, 'exact-coordinate-coverage', [
    'TerminalBN5CompleteMultiplicityMatching',
    'pair.quotientUnits restoration', 'restoration.fullRestorations pair',
  ]);

  const edge = declarationBlock0(source,
    'terminalPkgC_restorationEdge_preservesCoordinate');
  requireTokens0(failures, edge, 'coordinate-preservation', [
    'TerminalBN5ShadowEdge unit restoration',
    'unit.coordinate = restoration.coordinate', ':=\n  edge',
  ]);

  const hall = declarationBlock0(source,
    'TerminalBN5HallDeficit.pkgCRestorationNotSilent');
  requireTokens0(failures, hall, 'strict-hall-route', [
    'deficit.pkgCNamedLocalRoute = .qRestorationHall',
    'deficit.neighborShadows.length < deficit.fullSubset.length',
    'deficit.neighbor_card_lt_full_card',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPkgCSeparatingConsumersOutcome');
  requireTokens0(failures, outcome, 'total-outcome', [
    '| singletonized', '| restored', '| localized',
    'TerminalPkgCExactCoordinateCoverage', 'TerminalBN5HallDeficit',
  ]);

  const classifier = declarationBlock0(source,
    'classifyTerminalPkgCSeparatingConsumers');
  requireTokens0(failures, classifier, 'total-classifier', [
    'firstTerminalPkgCSeparatingPair?',
    'firstTerminalPkgCSeparatingPair?_eq_none_iff',
    'terminalPkgCSeparatingPairOfFound',
    'classifyTerminalBN5ShadowMatching',
    '| .matched coverage => .restored pair coverage',
    '| .hallDeficit deficit => .localized pair deficit',
  ]);

  const theorem = declarationBlock0(source,
    'terminalPkgC_separatingConsumers_restorationDichotomy');
  requireTokens0(failures, theorem, 'exact-dichotomy', [
    'system.DisjointPairsSingletonized',
    'TerminalPkgCExactCoordinateCoverage restoration pair',
    'TerminalBN5HallDeficit',
    'deficit.pkgCNamedLocalRoute = .qRestorationHall',
    'deficit.neighborShadows.length < deficit.fullSubset.length',
  ]);
  if (/\bFin\b/u.test(stripped)) failures.push('fixed-carrier');

  return [...new Set(failures)];
}

test('PkgC source proves the finite separating-consumer restoration dichotomy', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 27-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 27);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPkgCSeparatingConsumers\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPkgCSeparatingConsumers$/mu);
});

test('compiled inventory pins every PkgC declaration to the standard allowlist', async () => {
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

test('regression covers singletonized, covered, strict Hall, and canonical scan branches', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'pkgCRegressionSingletonSystem',
    'pkgCRegressionSeparatingSystem',
    'some ([0, 1], [2])',
    'pkgCRegressionMatchedRestoration',
    'pkgCRegressionHallRestoration',
    'pkgCRegressionOutcomeTag',
    '= 0', '= 1', '= 2',
    'terminalPkgC_separatingConsumers_restorationDichotomy',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite explicit PkgC restoration boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-pkgc-separating-consumers');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-pkgc-separating-consumers');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /first disjoint pair/u);
  assert.match(milestone.nonClaim, /restoration coordinate universe remains explicit/u);
  assert.equal(status.leanResidualTerminalPkgCSeparatingConsumersFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPkgCSeparatingConsumersAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPkgCSeparatingConsumersScope,
    /pkgc-separating-consumer/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /finite PkgC separating-consumer restoration dichotomy/iu);
  assert.match(docs, /does not[\s\S]{0,120}full historical PkgC theorem/iu);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-pkgc-separating-consumers0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPkgCSeparatingConsumersAxiomAudit\.lean[\s\S]{0,1800}-eq 27/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPkgCSeparatingConsumers\.lean/u);
});

test('hostile PkgC mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('.find? fun pair =>', '.head? fun pair =>'),
      'canonical-first-scan'],
    [source.replace('(pair.left ++ pair.right).map restoration.coordinateOf',
      'pair.left.map restoration.coordinateOf'),
    'canonical-quotient-generation'],
    [source.replace('unit.coordinate = restoration.coordinate :=\n  edge',
      'unit.coordinate = unit.coordinate :=\n  rfl'),
    'coordinate-preservation'],
    [source.replace(
      'deficit.neighborShadows.length < deficit.fullSubset.length',
      'deficit.neighborShadows.length ≤ deficit.fullSubset.length'),
    'strict-hall-route'],
    [source.replace('| localized\n', '| misplaced\n'), 'total-outcome'],
    [`${source}\naxiom pkgCShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef fixedPkgCCarrier : Type := Fin 4\n`, 'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
