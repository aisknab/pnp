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
  'lean/PNP/ResidualTerminalConsumerAntichainNormalForm.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalConsumerAntichainNormalFormAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalConsumerAntichainNormalForm.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_consumer_antichain_normal_form.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalV54Included',
  'TerminalV54StrictIncluded',
  'TerminalV54Disjoint',
  'terminalV54Included_refl',
  'terminalV54Included_trans',
  'terminalV54Disjoint_symm',
  'TerminalV54ConsumerSystem',
  'TerminalV54ConsumerSystem.RequestActive',
  'TerminalV54ConsumerSystem.requestBool',
  'TerminalV54ConsumerSystem.requestBool_eq_true_iff',
  'TerminalV54ConsumerSystem.requestActive_monotone',
  'TerminalV54ConsumerSystem.requestActive_empty_false',
  'TerminalV54ConsumerSystem.consumer_is_minimal',
  'terminalV54Complement',
  'mem_terminalV54Complement_iff',
  'TerminalV54ConsumerSystem.CutActive',
  'TerminalV54ConsumerSystem.cutActivationBool',
  'TerminalV54ConsumerSystem.cutActivationBool_eq_true_iff',
  'TerminalV54ConsumerSystem.singletonFootprint',
  'TerminalV54ConsumerSystem.mem_singletonFootprint_iff',
  'TerminalV54ConsumerSystem.FootprintCrossesCut',
  'TerminalV54ConsumerSystem.cutIndicatorBool',
  'TerminalV54ConsumerSystem.cutIndicatorBool_eq_true_iff',
  'TerminalV54ConsumerSystem.cutActive_has_disjoint_consumers',
  'terminalV54_cutActivation_nonzero_iff_disjoint_consumers',
  'TerminalV54ConsumerSystem.DisjointPairsSingletonized',
  'terminalV54_consumerAntichain_normal_form_iff',
  'terminalV54_consumerAntichain_normal_form',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalV54ConsumerSystem.requestActive_monotone`,
  `${NAMESPACE}.TerminalV54ConsumerSystem.requestActive_empty_false`,
  `${NAMESPACE}.TerminalV54ConsumerSystem.consumer_is_minimal`,
  `${NAMESPACE}.TerminalV54ConsumerSystem.cutActive_has_disjoint_consumers`,
  `${NAMESPACE}.terminalV54_cutActivation_nonzero_iff_disjoint_consumers`,
  `${NAMESPACE}.terminalV54_consumerAntichain_normal_form_iff`,
  `${NAMESPACE}.terminalV54_consumerAntichain_normal_form`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|bn6Complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\b(?:callerIndicator|callerSingletonized|trustedMinimal|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-certificate');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalBN5FullShadowLocalization',
  ])) failures.push('closed-import');

  const system = declarationBlock0(source, 'TerminalV54ConsumerSystem');
  for (const token of [
    'carrierNodup', 'consumersNodup', 'consumerNodup',
    'consumerNonempty', 'consumer ≠ []', 'consumerContained',
    'consumerAntichain',
    'TerminalV54Included left right -> left = right',
  ]) if (!system.includes(token)) failures.push('minimal-consumer-antichain');

  const request = declarationBlock0(source,
    'TerminalV54ConsumerSystem.RequestActive');
  for (const token of [
    '∃ consumer', 'consumer ∈ system.consumers',
    'TerminalV54Included consumer cut',
  ]) if (!request.includes(token)) failures.push('request-generated-by-consumers');

  const empty = declarationBlock0(source,
    'TerminalV54ConsumerSystem.requestActive_empty_false');
  if (!empty.includes('¬ system.RequestActive []')) {
    failures.push('empty-inactive');
  }
  const minimal = declarationBlock0(source,
    'TerminalV54ConsumerSystem.consumer_is_minimal');
  for (const token of [
    'system.RequestActive consumer', 'TerminalV54StrictIncluded subset consumer',
    '¬ system.RequestActive subset',
  ]) if (!minimal.includes(token)) failures.push('consumer-minimality');

  const complement = declarationBlock0(source, 'terminalV54Complement');
  for (const token of ['carrier.filter', 'decide (atom ∉ cut)']) {
    if (!complement.includes(token)) failures.push('exact-complement');
  }
  const cutActive = declarationBlock0(source,
    'TerminalV54ConsumerSystem.CutActive');
  for (const token of [
    'system.RequestActive cut',
    'system.RequestActive (terminalV54Complement system.carrier cut)',
  ]) if (!cutActive.includes(token)) failures.push('two-sided-activation');

  const footprint = declarationBlock0(source,
    'TerminalV54ConsumerSystem.singletonFootprint');
  for (const token of [
    'system.carrier.filter', 'decide ([atom] ∈ system.consumers)',
  ]) if (!footprint.includes(token)) failures.push('singleton-footprint');
  const singletonized = declarationBlock0(source,
    'TerminalV54ConsumerSystem.DisjointPairsSingletonized');
  for (const token of [
    'TerminalV54Disjoint left right', '∃ leftAtom rightAtom',
    'left = [leftAtom]', 'right = [rightAtom]',
  ]) if (!singletonized.includes(token)) failures.push('pkgc-singletonization');

  const nonzero = declarationBlock0(source,
    'terminalV54_cutActivation_nonzero_iff_disjoint_consumers');
  for (const token of [
    '(∃ cut, system.CutActive cut) ↔',
    'TerminalV54Disjoint left right',
  ]) if (!nonzero.includes(token)) failures.push('nonzero-disjoint-equivalence');
  const normalForm = declarationBlock0(source,
    'terminalV54_consumerAntichain_normal_form');
  for (const token of [
    'singletonized : system.DisjointPairsSingletonized',
    'system.cutActivationBool cut = system.cutIndicatorBool cut',
  ]) if (!normalForm.includes(token)) failures.push('exact-cut-indicator');
  if (/\bFin\b|\bV54RegressionAtom\b/u.test(stripped)) {
    failures.push('fixed-carrier');
  }

  return [...new Set(failures)];
}

test('V54 source proves the arbitrary finite consumer-antichain normal form', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 28-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 28);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalConsumerAntichainNormalForm\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalConsumerAntichainNormalForm$/mu);
});

test('compiled inventory pins every V54 declaration to the standard allowlist', async () => {
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

test('regression demonstrates crossing, noncrossing, nonsingleton, and intersecting cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'v54RegressionCrossingSummary = (true, true)',
    'v54RegressionNoncrossingSummary = (false, false)',
    'v54RegressionNonsingletonSummary = (true, false)',
    'v54RegressionIntersectingAnyActive = false',
    'v54RegressionSingletonSystem.requestActive_empty_false',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the V54 normal-form boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-consumer-antichain-normal-form');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-v54-consumer-antichain-normal-form');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite carrier/u);
  assert.match(milestone.scope, /cut indicator/u);
  assert.match(milestone.nonClaim, /does not construct PkgC/u);
  assert.equal(
    status.leanResidualTerminalConsumerAntichainNormalFormFormalized, true);
  assert.equal(
    status.leanResidualTerminalConsumerAntichainNormalFormAxiomAuditPassed,
    true);
  assert.match(
    status.leanResidualTerminalConsumerAntichainNormalFormScope,
    /v54-consumer-antichain/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /V54 consumer-antichain normal form/u);
  assert.match(docs, /does not yet construct PkgC/u);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-consumer-antichain-normal-form0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalConsumerAntichainNormalFormAxiomAudit\.lean[\s\S]{0,1800}-eq 28/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalConsumerAntichainNormalForm\.lean/u);
});

test('hostile V54 mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('consumerAntichain :', 'consumerComparable :'),
      'minimal-consumer-antichain'],
    [source.replace('consumer ≠ []', 'True'),
      'minimal-consumer-antichain'],
    [source.replace('decide (atom ∉ cut)', 'true'), 'exact-complement'],
    [source.replace(
      'system.RequestActive (terminalV54Complement system.carrier cut)',
      'system.RequestActive cut'), 'two-sided-activation'],
    [source.replace('TerminalV54Disjoint left right ->', 'True ->'),
      'pkgc-singletonization'],
    [source.replace(
      'system.cutActivationBool cut = system.cutIndicatorBool cut',
      'system.cutActivationBool cut = system.cutActivationBool cut'),
    'exact-cut-indicator'],
    [`${source}\naxiom v54Shortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
