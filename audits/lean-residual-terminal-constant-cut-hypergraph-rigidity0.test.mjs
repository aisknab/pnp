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
  'lean/PNP/ResidualTerminalConstantCutHypergraphRigidity.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalConstantCutHypergraphRigidityAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalConstantCutHypergraphRigidity.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_constant_cut_hypergraph_rigidity.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalV53Sublist_of_included',
  'terminalV53IncludedBool',
  'terminalV53IncludedBool_eq_true_iff',
  'terminalV53_notIncluded_has_witness',
  'terminalV53CanonicalPair',
  'mem_terminalV53CanonicalPair_iff',
  'terminalV53CanonicalPair_sublist',
  'terminalV53CanonicalPair_length',
  'terminalV53_filter_congr',
  'terminalV53Complement_sublist',
  'terminalV53_nil_sublist',
  'terminalV53_singleton_sublist_of_mem',
  'terminalV53_two_distinct_members',
  'terminalV53_eq_three_of_length',
  'terminalV53_sublist_cons_cases',
  'terminalV53_sublist_mem_terminalListSubsets',
  'terminalV53_threeCarrier_largeSublist_classification',
  'terminalV53Complement_length_add',
  'TerminalV53Hyperedge',
  'TerminalV53Hypergraph',
  'TerminalV53Hyperedge.Crosses',
  'TerminalV53Hyperedge.crossesBool',
  'TerminalV53Hyperedge.crossesBool_eq_true_iff',
  'TerminalV53Hyperedge.insideContribution',
  'TerminalV53Hyperedge.cutContribution',
  'TerminalV53Hypergraph.insideWeight',
  'TerminalV53Hypergraph.cutWeight',
  'TerminalV53Hypergraph.footprintWeight',
  'TerminalV53Hypergraph.totalWeight',
  'TerminalV53Hypergraph.ProperCut',
  'TerminalV53Hypergraph.ConstantProperCuts',
  'TerminalV53Hypergraph.cell_partition',
  'terminalV53_sum_congr',
  'terminalV53_sum_partition',
  'terminalV53_sum_pair_le',
  'terminalV53_sum_triple_le',
  'terminalV53_term_le_sum',
  'TerminalV53Hypergraph.cut_partition',
  'TerminalV53Hypergraph.insideWeight_eq_zero_of_length_lt_two',
  'TerminalV53Hypergraph.insideWeight_eq_footprintWeight_of_length_two',
  'TerminalV53Hypergraph.insideWeight_carrier_eq_totalWeight',
  'TerminalV53Hypergraph.cellMass_le_footprintWeight',
  'TerminalV53Hypergraph.footprintWeight_carrier_eq_total_of_cellsFull',
  'TerminalV53Hypergraph.insideWeight_complement_singleton_eq_zero_of_cellsFull',
  'TerminalV53Hypergraph.fullWeight_eq_cutValue_of_cellsFull',
  'TerminalV53Hypergraph.insideWeight_add_footprintWeight_le',
  'TerminalV53Hypergraph.insideWeight_add_twoFootprintWeights_le',
  'TerminalV53Hypergraph.pair_complement_identity',
  'terminalV53Complement_pair_in_singleton',
  'TerminalV53Hypergraph.footprintWeight_le_pairWeight',
  'TerminalV53Hypergraph.pairWeights_equal_of_shared',
  'TerminalV53Hypergraph.pairWeight_eq_zero_of_four',
  'TerminalV53Hypergraph.properFootprintWeight_eq_zero_of_four',
  'TerminalV53Hypergraph.cellsFull_of_four',
  'TerminalV53Hypergraph.twoAnchor_fullWeight',
  'TerminalV53Hypergraph.threeAnchor_rigidity',
  'TerminalV53Hypergraph.fourAnchor_rigidity',
  'terminalV53_constantCut_hypergraph_rigidity',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalV53Hypergraph.cell_partition`,
  `${NAMESPACE}.TerminalV53Hypergraph.cut_partition`,
  `${NAMESPACE}.TerminalV53Hypergraph.pair_complement_identity`,
  `${NAMESPACE}.TerminalV53Hypergraph.pairWeights_equal_of_shared`,
  `${NAMESPACE}.TerminalV53Hypergraph.pairWeight_eq_zero_of_four`,
  `${NAMESPACE}.TerminalV53Hypergraph.properFootprintWeight_eq_zero_of_four`,
  `${NAMESPACE}.TerminalV53Hypergraph.twoAnchor_fullWeight`,
  `${NAMESPACE}.TerminalV53Hypergraph.threeAnchor_rigidity`,
  `${NAMESPACE}.TerminalV53Hypergraph.fourAnchor_rigidity`,
  `${NAMESPACE}.terminalV53_constantCut_hypergraph_rigidity`,
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

  const system = declarationBlock0(source, 'TerminalV53Hypergraph');
  for (const token of [
    'carrierNodup', 'footprintsNodup', 'footprintSublist',
    'footprintLarge', 'massPositive', 'cutValuePositive',
  ]) if (!system.includes(token)) failures.push('finite-positive-hypergraph');

  const constantCuts = declarationBlock0(source,
    'TerminalV53Hypergraph.ConstantProperCuts');
  for (const token of [
    '∀ cut', 'system.ProperCut cut',
    'system.cutWeight cut = system.cutValue',
  ]) if (!constantCuts.includes(token)) failures.push('constant-proper-cuts');

  const partition = declarationBlock0(source,
    'TerminalV53Hypergraph.cut_partition');
  for (const token of [
    'system.insideWeight cut',
    'terminalV54Complement system.carrier cut',
    'system.cutWeight cut', 'system.totalWeight',
  ]) if (!partition.includes(token)) failures.push('exact-mass-partition');

  const pairIdentity = declarationBlock0(source,
    'TerminalV53Hypergraph.pair_complement_identity');
  for (const token of [
    'system.footprintWeight pair',
    'terminalV54Complement system.carrier pair',
    'terminalV54Complement system.carrier [excluded]',
  ]) if (!pairIdentity.includes(token)) failures.push('pair-region-identity');

  const theorem = declarationBlock0(source,
    'terminalV53_constantCut_hypergraph_rigidity');
  for (const token of [
    '_carrierAtLeastTwo : 2 ≤ system.carrier.length',
    'system.carrier.length = 2',
    'system.carrier.length = 3',
    '4 ≤ system.carrier.length',
    'system.footprintWeight system.carrier = system.cutValue',
    'system.footprintWeight system.carrier + 2 * p = system.cutValue',
    'system.footprintWeight footprint = 0',
  ]) if (!theorem.includes(token)) failures.push('exact-v53-classification');
  if (/\bFin\b|\bV53(?:Two|Three|Four)Atom\b/u.test(stripped)) {
    failures.push('fixed-carrier');
  }

  return [...new Set(failures)];
}

test('V53 source proves arbitrary finite constant-cut hypergraph rigidity', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 58-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 58);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalConstantCutHypergraphRigidity\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalConstantCutHypergraphRigidity$/mu);
});

test('compiled inventory pins every V53 declaration to the standard allowlist', async () => {
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

test('regression demonstrates q2, q3, q4, and hostile unequal-pair data', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'v53TwoAnchorSystem',
    'v53ThreeAnchorSystem',
    'v53FourAnchorSystem',
    'v53HostileUnequalPairSystem.cutWeight [0] = 3',
    '¬ v53HostileUnequalPairSystem.ConstantProperCuts',
    'terminalV53_constantCut_hypergraph_rigidity',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the exact V53 rigidity boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-constant-cut-hypergraph-rigidity');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-v53-constant-cut-hypergraph-rigidity');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /q=2, q=3, and q>=4/u);
  assert.match(milestone.nonClaim, /does not construct PkgC/u);
  assert.equal(
    status.leanResidualTerminalConstantCutHypergraphRigidityFormalized, true);
  assert.equal(
    status.leanResidualTerminalConstantCutHypergraphRigidityAxiomAuditPassed,
    true);
  assert.match(
    status.leanResidualTerminalConstantCutHypergraphRigidityScope,
    /constant-cut-hypergraph-rigidity-v53/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /V53 constant-cut hypergraph rigidity/u);
  assert.match(docs, /does not construct PkgC/u);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-constant-cut-hypergraph-rigidity0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalConstantCutHypergraphRigidityAxiomAudit\.lean[\s\S]{0,1800}-eq 58/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalConstantCutHypergraphRigidity\.lean/u);
});

test('hostile V53 mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('massPositive :', 'massNonnegative :'),
      'finite-positive-hypergraph'],
    [source.replace('system.cutWeight cut = system.cutValue',
      'system.cutWeight cut = system.cutWeight cut'),
    'constant-proper-cuts'],
    [source.replace('system.totalWeight := by', 'system.cutValue := by'),
      'exact-mass-partition'],
    [source.replace('_carrierAtLeastTwo : 2 ≤ system.carrier.length',
      '_carrierAtLeastTwo : 3 ≤ system.carrier.length'), 'exact-v53-classification'],
    [source.replace('4 ≤ system.carrier.length ->\n      (∀ footprint',
      '5 ≤ system.carrier.length ->\n      (∀ footprint'),
    'exact-v53-classification'],
    [`${source}\naxiom v53Shortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
