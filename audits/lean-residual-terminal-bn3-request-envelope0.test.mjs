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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalBN3RequestEnvelope.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBN3RequestEnvelopeAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBN3RequestEnvelope.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_bn3_request_envelope.md';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalListSubsets_sublist',
  'TerminalComputedBCELAnchorNucleus.requestAtoms',
  'TerminalComputedBCELAnchorNucleus.requestAtoms_nodup',
  'TerminalBN3RequestPredicate',
  'terminalBN3RequestPredicateBool',
  'terminalBN3RequestPredicateBool_eq_true_iff',
  'terminalBN3RequestPredicate_monotone',
  'terminalBN3RequestPredicate_stable',
  'terminalBN3MinimalConsumer',
  'terminalBN3MinimalConsumer_exact',
  'TerminalComputedBCELAnchorNucleus.activeRequestAtoms',
  'TerminalComputedBCELAnchorNucleus.mem_activeRequestAtoms_iff',
  'TerminalComputedBCELAnchorNucleus.activeRequestAtoms_nodup',
  'TerminalComputedBCELAnchorNucleus.mem_activeRequestAtoms_iff_properCut',
  'TerminalComputedBCELAnchorNucleus.canonicalRequestBasis',
  'TerminalComputedBCELAnchorNucleus.canonicalRequestBasis_jointlySideTight',
  'TerminalComputedBN3RequestEnvelope',
  'TerminalComputedBCELAnchorNucleus.computedBN3RequestEnvelope',
  'TerminalBN3RequestEnvelopeOutcome',
  'classifyTerminalBN3RequestEnvelope',
  'classifyTerminalBN3RequestEnvelope_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalListSubsets_sublist`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.requestAtoms_nodup`,
  `${NAMESPACE}.terminalBN3RequestPredicateBool_eq_true_iff`,
  `${NAMESPACE}.terminalBN3RequestPredicate_monotone`,
  `${NAMESPACE}.terminalBN3RequestPredicate_stable`,
  `${NAMESPACE}.terminalBN3MinimalConsumer_exact`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.mem_activeRequestAtoms_iff_properCut`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.activeRequestAtoms_nodup`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.canonicalRequestBasis_jointlySideTight`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.computedBN3RequestEnvelope`,
  `${NAMESPACE}.classifyTerminalBN3RequestEnvelope_exhaustive`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|bcelReady|routeComplete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\b(?:callerRequest|callerBasis|callerEnvelope|trustFlag|jointSideTightRealizability\s*:\s*Bool)\b/u.test(stripped)) {
    failures.push('caller-certificate');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalBCELAnchorNucleus',
  ])) failures.push('closed-import');

  const atoms = declarationBlock0(source,
    'TerminalComputedBCELAnchorNucleus.requestAtoms');
  if (!atoms.includes('result.nucleus.anchors')) {
    failures.push('canonical-request-identities');
  }
  const atomsNodup = declarationBlock0(source,
    'TerminalComputedBCELAnchorNucleus.requestAtoms_nodup');
  for (const token of [
    'problem.anchorRecords_nodup.sublist',
    'terminalListSubsets_sublist problem.anchorRecords result.requestAtoms',
  ]) if (!atomsNodup.includes(token)) failures.push('duplicate-free-identities');

  const predicate = declarationBlock0(source, 'TerminalBN3RequestPredicate');
  if (!predicate.includes('atom ∈ cut')) failures.push('exact-membership-predicate');
  const boolExact = declarationBlock0(source,
    'terminalBN3RequestPredicateBool_eq_true_iff');
  if (!boolExact.includes('decide_eq_true_iff')) {
    failures.push('executable-predicate-exactness');
  }
  const monotone = declarationBlock0(source,
    'terminalBN3RequestPredicate_monotone');
  if (!monotone.includes('included atom active')) {
    failures.push('monotone-membership');
  }
  const stable = declarationBlock0(source,
    'terminalBN3RequestPredicate_stable');
  if (!stable.includes('transport atom')) failures.push('stable-membership');

  const minimal = declarationBlock0(source, 'terminalBN3MinimalConsumer');
  if (!minimal.includes('[atom]')) failures.push('singleton-minimal-consumer');
  const minimalExact = declarationBlock0(source,
    'terminalBN3MinimalConsumer_exact');
  if (!minimalExact.includes('terminalBN3MinimalConsumer')) {
    failures.push('minimal-consumer-exactness');
  }

  const active = declarationBlock0(source,
    'TerminalComputedBCELAnchorNucleus.activeRequestAtoms');
  for (const token of [
    'result.requestAtoms.filter',
    'terminalBN3RequestPredicateBool atom cut',
  ]) if (!active.includes(token)) failures.push('candidate-derived-incidence');
  const activeNodup = declarationBlock0(source,
    'TerminalComputedBCELAnchorNucleus.activeRequestAtoms_nodup');
  if (!activeNodup.includes('requestAtoms_nodup.sublist List.filter_sublist')) {
    failures.push('duplicate-free-incidence');
  }

  const basis = declarationBlock0(source,
    'TerminalComputedBCELAnchorNucleus.canonicalRequestBasis');
  if (!basis.includes('canonicalImplementationBasis')) {
    failures.push('canonical-basis-selection');
  }
  const joint = declarationBlock0(source,
    'TerminalComputedBCELAnchorNucleus.canonicalRequestBasis_jointlySideTight');
  for (const token of [
    'result.properCutLocalConclusion cut proper',
    'canonicalImplementationBasis_isTightCoherent',
    'localResult.noRoutes.1',
    'localResult.noRoutes.2',
  ]) if (!joint.includes(token)) failures.push('joint-side-tight-realizability');

  const envelope = declarationBlock0(source,
    'TerminalComputedBN3RequestEnvelope');
  for (const field of [
    'requestAtomsNodup', 'properCutsComplete', 'predicatesMonotone',
    'predicatesStable', 'minimalConsumersExact', 'activeAtomsExact',
    'activeAtomsNodup', 'jointSideTightRealizability',
  ]) if (!envelope.includes(field)) failures.push('proof-bearing-envelope');

  const classify = declarationBlock0(source,
    'classifyTerminalBN3RequestEnvelope');
  for (const branch of [
    '.insufficient failure', '.algebraFailure nucleus first failure',
    '.cutDefectFailure nucleus first failure',
    '.cutRouteFailure nucleus first failure',
    '.ready result result.computedBN3RequestEnvelope',
  ]) if (!classify.includes(branch)) failures.push('total-failure-preservation');
  return [...new Set(failures)];
}

test('finite BN3 source derives one stable candidate request envelope', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 21-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 21);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBN3RequestEnvelope\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalBN3RequestEnvelope$/mu);
});

test('compiled inventory pins every BN3 declaration to the standard allowlist', async () => {
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

test('regression reaches the nontrivial two-cut ready envelope', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'classifyTerminalBN3RequestEnvelope',
    'TerminalComputedBN3RequestEnvelope result',
    'result.computedBN3RequestEnvelope',
    'bcelAnchorBN3ReadyOutcome = (4, 2)',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite BN3 milestone and keeps global claims closed', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-bn3-request-envelope',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-bn3-request-envelope');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /canonical duplicate-free/u);
  assert.match(milestone.scope, /every proper cut/u);
  assert.match(milestone.nonClaim, /exponential/u);
  assert.match(milestone.nonClaim, /BN4-BN6/u);
  assert.equal(status.leanResidualTerminalBN3RequestEnvelopeFormalized, true);
  assert.equal(
    status.leanResidualTerminalBN3RequestEnvelopeAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalBN3RequestEnvelopeScope,
    /canonical-stable-request-identities/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /Candidate-derived finite BN3 request envelope/u);
  assert.match(docs, /exponential/u);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-bn3-request-envelope0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalBN3RequestEnvelopeAxiomAudit\.lean[\s\S]{0,1800}-eq 21/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalBN3RequestEnvelope\.lean/u);
});

test('hostile BN3 mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('result.nucleus.anchors', 'problem.anchorRecords'),
      'canonical-request-identities'],
    [source.replace('atom ∈ cut\n', 'True\n'),
      'exact-membership-predicate'],
    [source.replace('[atom]\n', '[]\n'),
      'singleton-minimal-consumer'],
    [source.replace('result.requestAtoms.filter', 'cut.filter'),
      'candidate-derived-incidence'],
    [source.replace('canonicalImplementationBasis\n', 'callerBasis\n'),
      'caller-certificate'],
    [source.replace('.ready result result.computedBN3RequestEnvelope',
      '.ready result callerEnvelope'), 'caller-certificate'],
    [`${source}\naxiom bn3Shortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
