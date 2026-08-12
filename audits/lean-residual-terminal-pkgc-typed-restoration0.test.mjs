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
  'lean/PNP/ResidualTerminalPkgCTypedRestoration.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPkgCTypedRestorationAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPkgCTypedRestoration.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_pkgc_typed_restoration.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalPkgCTypedRestorer',
  'TerminalPkgCSeparatingPair.fullRestorationCandidates',
  'TerminalPkgCSeparatingPair.fullRestorationCandidates_length',
  'TerminalPkgCSeparatingPair.fullRestorationCandidates_coordinates',
  'TerminalPkgCTypedRestorer.coordinateUniverse',
  'TerminalPkgCTypedRestorer.coordinateUniverse_coordinates',
  'terminalPkgCCoordinateMultiplicity',
  'terminalBN5FullMultiplicity_indexed_eq',
  'terminalBN5ShadowMultiplicity_indexed_eq',
  'TerminalPkgCSeparatingPair.typedRestoration_exactCoverage',
  'terminalBN5CompleteMultiplicityMatching_not_hallDeficit',
  'TerminalPkgCTypedRestorationRealization',
  'TerminalPkgCSeparatingPair.typedRestorationRealization',
  'TerminalPkgCTypedRestorationOutcome',
  'classifyTerminalPkgCTypedRestoration',
  'terminalPkgC_typedRestoration_realization',
  'classifyTerminalPkgCTypedRestoration_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPkgCSeparatingPair.fullRestorationCandidates_length`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.fullRestorationCandidates_coordinates`,
  `${NAMESPACE}.TerminalPkgCTypedRestorer.coordinateUniverse_coordinates`,
  `${NAMESPACE}.terminalBN5FullMultiplicity_indexed_eq`,
  `${NAMESPACE}.terminalBN5ShadowMultiplicity_indexed_eq`,
  `${NAMESPACE}.TerminalPkgCSeparatingPair.typedRestoration_exactCoverage`,
  `${NAMESPACE}.terminalBN5CompleteMultiplicityMatching_not_hallDeficit`,
  `${NAMESPACE}.terminalPkgC_typedRestoration_realization`,
  `${NAMESPACE}.classifyTerminalPkgCTypedRestoration_exhaustive`,
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
    'PNP.ResidualTerminalPkgCSeparatingConsumers',
  ])) failures.push('closed-import');

  const restorer = declarationBlock0(source, 'TerminalPkgCTypedRestorer');
  requireTokens0(failures, restorer, 'typed-restorer', [
    'restore : Atom -> FullCandidate',
    'fullCoordinate : FullCandidate -> Coordinate',
    'restore_preserves_coordinate',
    'fullCoordinate (restore atom) = quotientCoordinate atom',
  ]);

  const candidates = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.fullRestorationCandidates');
  requireTokens0(failures, candidates, 'canonical-full-candidates', [
    'List FullCandidate', 'pair.left ++ pair.right',
    '.map restorer.restore',
  ]);

  const coordinates = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.fullRestorationCandidates_coordinates');
  requireTokens0(failures, coordinates, 'positional-coordinate-preservation', [
    '.map restorer.fullCoordinate',
    '.map restorer.quotientCoordinate',
    'restorer.restore_preserves_coordinate atom',
  ]);

  const universe = declarationBlock0(source,
    'TerminalPkgCTypedRestorer.coordinateUniverse');
  requireTokens0(failures, universe, 'derived-coordinate-universe', [
    'coordinateOf := restorer.quotientCoordinate',
    '(left ++ right).map restorer.restore',
    '.map restorer.fullCoordinate',
  ]);
  if (universe.includes('fullRestorationCoordinates := fun _ _ =>')) {
    failures.push('arbitrary-restoration-list');
  }

  const fullMultiplicity = declarationBlock0(source,
    'terminalBN5FullMultiplicity_indexed_eq');
  requireTokens0(failures, fullMultiplicity, 'full-multiplicity-bridge', [
    'terminalBN5IndexFullUnitsFrom start coordinates',
    'terminalPkgCCoordinateMultiplicity coordinates coordinate',
    'induction coordinates',
  ]);

  const shadowMultiplicity = declarationBlock0(source,
    'terminalBN5ShadowMultiplicity_indexed_eq');
  requireTokens0(failures, shadowMultiplicity, 'shadow-multiplicity-bridge', [
    'terminalBN5IndexQuotientShadowsFrom start coordinates',
    'terminalPkgCCoordinateMultiplicity coordinates coordinate',
    'induction coordinates',
  ]);

  const coverage = declarationBlock0(source,
    'TerminalPkgCSeparatingPair.typedRestoration_exactCoverage');
  requireTokens0(failures, coverage, 'typed-exact-coverage', [
    'TerminalPkgCExactCoordinateCoverage restorer.coordinateUniverse pair',
    'terminalBN5FullMultiplicity_indexed_eq',
    'terminalBN5ShadowMultiplicity_indexed_eq',
  ]);

  const noHall = declarationBlock0(source,
    'terminalBN5CompleteMultiplicityMatching_not_hallDeficit');
  requireTokens0(failures, noHall, 'coverage-excludes-hall', [
    'coverage deficit.fullUnit deficit.fullMember',
    'deficit.fullCoordinate', 'deficit.strictDeficit',
    'Nat.not_lt_of_ge',
  ]);

  const realization = declarationBlock0(source,
    'TerminalPkgCTypedRestorationRealization');
  requireTokens0(failures, realization, 'proof-bearing-realization', [
    'fullCandidates : List FullCandidate', 'canonical :',
    'candidateCount :', 'coordinates :', 'exactCoverage :',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPkgCTypedRestorationOutcome');
  requireTokens0(failures, outcome, 'two-branch-outcome', [
    '| singletonized', '| realized',
    'TerminalPkgCTypedRestorationRealization pair restorer',
  ]);
  if (outcome.includes('| localized')) failures.push('retained-hall-branch');

  const classifier = declarationBlock0(source,
    'classifyTerminalPkgCTypedRestoration');
  requireTokens0(failures, classifier, 'canonical-total-classifier', [
    'firstTerminalPkgCSeparatingPair?',
    'firstTerminalPkgCSeparatingPair?_eq_none_iff',
    'terminalPkgCSeparatingPairOfFound',
    'pair.typedRestorationRealization restorer',
  ]);

  const theorem = declarationBlock0(source,
    'terminalPkgC_typedRestoration_realization');
  requireTokens0(failures, theorem, 'typed-total-theorem', [
    'system.DisjointPairsSingletonized',
    'TerminalPkgCTypedRestorationRealization pair restorer',
    'classifyTerminalPkgCTypedRestoration system restorer',
  ]);

  if (/\bFin\b/u.test(stripped)) failures.push('fixed-carrier');
  return [...new Set(failures)];
}

test('PkgC source constructs typed full restorations with exact coverage', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 17-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 17);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPkgCTypedRestoration\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPkgCTypedRestoration$/mu);
});

test('compiled inventory pins every typed restoration declaration', async () => {
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

test('regression covers typed candidates, exact coverage, no Hall, and both outcomes', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'PkgCTypedRegressionFullCandidate',
    'pkgCTypedRegressionRestorer',
    'payload := atom.val + 10',
    'fullRestorationCandidates',
    'typedRestoration_exactCoverage',
    'terminalBN5CompleteMultiplicityMatching_not_hallDeficit',
    'pkgCTypedRegressionOutcomeTag', '= 0', '= 1',
    'terminalPkgC_typedRestoration_realization',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite typed-restoration boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-pkgc-typed-restoration');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-pkgc-typed-restoration');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /typed full-restoration candidates/u);
  assert.match(milestone.nonClaim, /restoration operation remains explicit/u);
  assert.equal(status.leanResidualTerminalPkgCTypedRestorationFormalized, true);
  assert.equal(
    status.leanResidualTerminalPkgCTypedRestorationAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPkgCTypedRestorationScope,
    /typed-full-restoration/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /finite PkgC typed restoration realization/iu);
  assert.match(docs, /restoration operation[\s\S]{0,120}explicit inputs/iu);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-pkgc-typed-restoration0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPkgCTypedRestorationAxiomAudit\.lean[\s\S]{0,1800}-eq 17/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPkgCTypedRestoration\.lean/u);
});

test('hostile typed-restoration mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('restore : Atom -> FullCandidate',
      'restore : Atom -> Coordinate'), 'typed-restorer'],
    [source.replace('(pair.left ++ pair.right).map restorer.restore',
      'pair.left.map restorer.restore'), 'canonical-full-candidates'],
    [source.replace('restorer.restore_preserves_coordinate atom', 'rfl'),
      'positional-coordinate-preservation'],
    [source.replace('terminalBN5FullMultiplicity_indexed_eq,',
      'terminalBN5ShadowMultiplicity_indexed_eq,'), 'typed-exact-coverage'],
    [source.replace('deficit.strictDeficit', 'Nat.lt_add_one _'),
      'coverage-excludes-hall'],
    [source.replace('| realized\n', '| localized\n'),
      'two-branch-outcome'],
    [`${source}\naxiom typedRestorationShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedTypedRestorationCarrier : Type := Fin 4\n`,
      'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
