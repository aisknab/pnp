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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalBN6HypergraphPacket.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBN6HypergraphPacketAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBN6HypergraphPacket.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_bn6_hypergraph_packet.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalBN6_disjointPairsSingletonized_of_all_singletons',
  'TerminalBN6PayloadAtom',
  'TerminalBN6GroupedCell',
  'TerminalBN6GroupedCell.mass',
  'TerminalBN6GroupedCell.massPositive',
  'TerminalBN6GroupedCell.footprint',
  'TerminalBN6GroupedCell.toHyperedge',
  'TerminalBN6GroupedCell.crosses_iff_footprintCrosses',
  'TerminalBN6GroupedCell.crossesBool_eq_cutIndicatorBool',
  'TerminalBN6GroupedCell.crossesBool_eq_cutActivationBool',
  'TerminalBN6GroupedFamily',
  'TerminalBN6GroupedFamily.activationWeight',
  'TerminalBN6GroupedFamily.ConstantActivation',
  'TerminalBN6GroupedFamily.hypergraph',
  'TerminalBN6GroupedFamily.cutWeight_eq_activationWeight',
  'TerminalBN6GroupedFamily.constantProperCuts',
  'TerminalBN6GroupedFamily.HasPayloadAt',
  'TerminalBN6GroupedFamily.footprintWeight_eq_groupedMass',
  'TerminalBN6GroupedFamily.hasPayloadAt_of_footprintWeight_positive',
  'TerminalBN6PacketConclusion',
  'terminalBN6_hypergraph_packet',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedCell.massPositive`,
  `${NAMESPACE}.TerminalBN6GroupedCell.crosses_iff_footprintCrosses`,
  `${NAMESPACE}.TerminalBN6GroupedCell.crossesBool_eq_cutActivationBool`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.cutWeight_eq_activationWeight`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.constantProperCuts`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.footprintWeight_eq_groupedMass`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasPayloadAt_of_footprintWeight_positive`,
  `${NAMESPACE}.terminalBN6_hypergraph_packet`,
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
    'PNP.ResidualTerminalConstantCutHypergraphRigidity',
  ])) failures.push('closed-import');

  const groupedCell = declarationBlock0(source, 'TerminalBN6GroupedCell');
  for (const token of [
    'consumerSystem', 'singletonized', 'atoms',
    'atomsNonempty : atoms ≠ []',
  ]) if (!groupedCell.includes(token)) failures.push('payload-group');

  const family = declarationBlock0(source, 'TerminalBN6GroupedFamily');
  for (const token of [
    'carrierNodup', 'groupCarrier', 'groupFootprintLarge',
    'groupFootprintsNodup', 'cutValuePositive',
  ]) if (!family.includes(token)) failures.push('grouped-family');

  const constant = declarationBlock0(source,
    'TerminalBN6GroupedFamily.ConstantActivation');
  for (const token of [
    '∀ cut', 'cut.Sublist family.carrier', 'cut ≠ []',
    'cut ≠ family.carrier',
    'family.activationWeight cut = family.cutValue',
  ]) if (!constant.includes(token)) failures.push('constant-activation');

  const cutBridge = declarationBlock0(source,
    'TerminalBN6GroupedFamily.cutWeight_eq_activationWeight');
  for (const token of [
    'family.hypergraph.cutWeight cut', 'family.activationWeight cut',
    'crossesBool_eq_cutActivationBool',
  ]) if (!cutBridge.includes(token)) failures.push('v54-v53-cut-bridge');

  const conclusion = declarationBlock0(source,
    'TerminalBN6PacketConclusion');
  for (const token of [
    '| pair', '| balancedTripleOrFullSpan', '| fullSpan',
    'positiveAlternative', 'balancedPayloads', 'fullSpanPayload',
    'properFootprintsZero',
  ]) if (!conclusion.includes(token)) failures.push('packet-classification');

  const theorem = declarationBlock0(source,
    'terminalBN6_hypergraph_packet');
  for (const token of [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalV53_constantCut_hypergraph_rigidity',
    'TerminalBN6PacketConclusion.pair',
    'TerminalBN6PacketConclusion.balancedTripleOrFullSpan',
    'TerminalBN6PacketConclusion.fullSpan',
    'hasPayloadAt_of_footprintWeight_positive',
  ]) if (!theorem.includes(token)) failures.push('exact-bn6-classification');
  if (/\bFin\b|BN6(?:Two|Three|Four)Atom/u.test(stripped)) {
    failures.push('fixed-carrier');
  }

  return [...new Set(failures)];
}

test('BN6 source proves the arbitrary finite V54-to-V53 packet bridge', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 21-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 21);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBN6HypergraphPacket\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalBN6HypergraphPacket$/mu);
});

test('compiled inventory pins every BN6 declaration to the standard allowlist', async () => {
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

test('regression covers q2, mixed q3, q4, and hostile premises', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'bn6TwoFamily',
    'bn6ThreeFamily',
    'bn6FourFamily',
    'bn6HostileNonsingletonSystem',
    'bn6HostileUnequalPairFamily.activationWeight [0] = 3',
    '¬bn6HostileUnequalPairFamily.ConstantActivation',
    'terminalBN6_hypergraph_packet',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite BN6 packet boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-bn6-hypergraph-packet');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-bn6-hypergraph-packet');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /mixed three-anchor/u);
  assert.match(milestone.nonClaim, /does not construct PkgC/u);
  assert.equal(status.leanResidualTerminalBN6HypergraphPacketFormalized, true);
  assert.equal(status.leanResidualTerminalBN6HypergraphPacketAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalBN6HypergraphPacketScope,
    /grouped-hypergraph-packet-bn6/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /BN6 hypergraph packet/u);
  assert.match(docs, /does not complete PkgC/u);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-bn6-hypergraph-packet0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalBN6HypergraphPacketAxiomAudit\.lean[\s\S]{0,1800}-eq 21/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalBN6HypergraphPacket\.lean/u);
});

test('hostile BN6 mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('atomsNonempty : atoms ≠ []', 'atomsNonempty : True'),
      'payload-group'],
    [source.replace('groupFootprintsNodup :', 'groupFootprintsListed :'),
      'grouped-family'],
    [source.replace('family.activationWeight cut = family.cutValue',
      'family.activationWeight cut = family.activationWeight cut'),
    'constant-activation'],
    [source.replace('family.hypergraph.cutWeight cut = family.activationWeight cut',
      'family.hypergraph.cutWeight cut = family.hypergraph.cutWeight cut'),
    'v54-v53-cut-bridge'],
    [source.replace('| balancedTripleOrFullSpan', '| tripleOnly'),
      'packet-classification'],
    [source.replace('carrierAtLeastTwo : 2 ≤ family.carrier.length',
      'carrierAtLeastTwo : 3 ≤ family.carrier.length'),
    'exact-bn6-classification'],
    [`${source}\naxiom bn6Shortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
