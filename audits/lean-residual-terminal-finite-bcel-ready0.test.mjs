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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalFiniteBCELReady.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFiniteBCELReadyAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFiniteBCELReady.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_finite_bcel_ready.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalFiniteBCELReadyCertificate',
  'checkTerminalFiniteBCELReady',
  'terminal_finite_saturate_positive_bcel_ready_checked_complete',
  'TerminalFiniteBCELReadyCertificate.anchorSizeAtLeastTwo',
  'TerminalFiniteBCELReadyCertificate.properCutConstantEquation',
  'TerminalFiniteBCELReadyCertificate.properCutLocalConclusion',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminal_finite_saturate_positive_bcel_ready_checked_complete`,
  `${NAMESPACE}.TerminalFiniteBCELReadyCertificate.anchorSizeAtLeastTwo`,
  `${NAMESPACE}.TerminalFiniteBCELReadyCertificate.properCutConstantEquation`,
  `${NAMESPACE}.TerminalFiniteBCELReadyCertificate.properCutLocalConclusion`,
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
  if (/\b(?:callerReady|callerResult|callerSuccess|trustFlag|hostLookup|digestWitness)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/(?:def|theorem)\s+(?:bcelReady|saturatePositive|zeroSlack|p_eq_np)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalFiniteSaturatePositive',
  ])) failures.push('closed-import');

  const certificate = declarationBlock0(source,
    'TerminalFiniteBCELReadyCertificate');
  for (const token of [
    'allSafe', 'finalPositive', 'wholePositive',
    'result : TerminalComputedBCELAnchorNucleus',
    'selected : classifyTerminalFiniteSaturatePositive candidate model problem =',
    '.projectionPositive allSafe finalPositive wholePositive (.ready result)',
  ]) if (!certificate.includes(token)) failures.push('exact-selected-certificate');

  const checker = declarationBlock0(source, 'checkTerminalFiniteBCELReady');
  for (const token of [
    'classifyTerminalFiniteSaturatePositive candidate model problem',
    '.projectionPositive _allSafe _finalPositive _wholePositive (.ready _result)',
    '| _ => false',
  ]) if (!checker.includes(token)) failures.push('recomputed-ready-checker');

  const complete = declarationBlock0(source,
    'terminal_finite_saturate_positive_bcel_ready_checked_complete');
  for (const token of [
    'checkTerminalFiniteBCELReady candidate model problem = true',
    'generalize selected',
    'fullPositiveProjectionLost', 'interfaceExposure',
    'originKernelObligation', 'otherNontransparent',
    'projectionPositive allSafe finalPositive wholePositive bcel',
    'insufficient', 'algebraFailure', 'cutDefectFailure',
    'cutRouteFailure', 'ready result', 'selected := selected',
  ]) if (!complete.includes(token)) failures.push('complete-fail-closed-reflection');

  const constantCut = declarationBlock0(source,
    'TerminalFiniteBCELReadyCertificate.properCutConstantEquation');
  if (!constantCut.includes(
    'certificate.result.properCutConstantEquation cut proper')) {
    failures.push('computed-constant-cut-delegation');
  }
  const local = declarationBlock0(source,
    'TerminalFiniteBCELReadyCertificate.properCutLocalConclusion');
  if (!local.includes(
    'certificate.result.properCutLocalConclusion cut proper')) {
    failures.push('computed-local-conclusion-delegation');
  }
  return [...new Set(failures)];
}

test('finite BCEL-ready composition is source-closed and fail-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact six-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 6);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFiniteBCELReady\n'), true);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualTerminalFiniteBCELReady$/mu);
});

test('compiled closure is approved for every new declaration', async () => {
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
  }
});

test('generic regression exposes only facts retained by the checked branch', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'checkTerminalFiniteBCELReady candidate model problem = true',
    'terminal_finite_saturate_positive_bcel_ready_checked_complete',
    'certificate.allSafe', 'certificate.finalPositive',
    'certificate.wholePositive', 'certificate.anchorSizeAtLeastTwo',
    'certificate.properCutConstantEquation cut proper',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication records only the checked finite BCEL-ready bridge', async () => {
  const [publication, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse), text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-finite-bcel-ready-composition',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-finite-bcel-ready-composition');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /recomputed finite SaturatePositive classifier/u);
  assert.match(milestone.scope, /computed BCEL-ready anchor nucleus/u);
  assert.match(milestone.nonClaim, /initial positive full-slack premise/u);
  assert.match(milestone.nonClaim, /BN3--BN6/u);
  assert.match(milestone.nonClaim, /ZeroSlack/u);
  assert.match(docs, /Checked finite SaturatePositive-to-BCEL-ready composition/u);
  assert.match(docs, /exact classifier equality/u);
});

test('status earns only the finite checked bridge', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  assert.equal(status.leanResidualTerminalFiniteBCELReadyCompositionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalFiniteBCELReadyCompositionAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalFiniteBCELReadyCompositionScope,
    /recomputed-finite-saturate-positive/u);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.finalTheoremReady, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /PNPResidualTerminalFiniteBCELReadyAxiomAudit\.lean[\s\S]{0,1800}-eq 6/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFiniteBCELReady\.lean/u);
  assert.match(workflow,
    /audits\/lean-residual-terminal-finite-bcel-ready0\.test\.mjs/u);
});

test('hostile ready-branch mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('(.ready _result)', '_bcel'),
      'recomputed-ready-checker'],
    [source.replace('| _ => false', '| _ => true'),
      'recomputed-ready-checker'],
    [source.replace('selected : classifyTerminalFiniteSaturatePositive',
      'callerReady : classifyTerminalFiniteSaturatePositive'),
      'caller-or-host-certificate'],
    [source.replace('generalize selected', 'generalize callerSuccess'),
      'caller-or-host-certificate'],
    [source.replace('certificate.result.properCutConstantEquation cut proper',
      'by sorry'), 'forbidden-shortcut'],
    [`${source}\naxiom readyShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ntheorem bcelReady : True := trivial\n`, 'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
