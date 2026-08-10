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
  'lean/PNP/ResidualTerminalSaturationPositivityFirewall.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalSaturationPositivityFirewallAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalSaturationPositivityFirewall.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_saturation_positivity_firewall.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBCELAnchorProblem.wholeCorners',
  'TerminalBCELAnchorProblem.wholeCorners_projectionDefect',
  'TerminalProjectionPositivityLoss',
  'terminalProjectionPositivityLossOfZero',
  'TerminalProjectionPositivityLoss.minima_eq',
  'TerminalSaturationPositivityOutcome',
  'classifyTerminalSaturationPositivity',
  'classifyTerminalSaturationPositivity_loss_of_zero',
  'classifyTerminalSaturationPositivity_bcel_of_positive',
  'terminalSaturationPositivity_no_checkedFullLiftAtMinimum',
  'classifyTerminalSaturationPositivity_exhaustive',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBCELAnchorProblem.wholeCorners_projectionDefect`,
  `${NAMESPACE}.TerminalProjectionPositivityLoss.minima_eq`,
  `${NAMESPACE}.classifyTerminalSaturationPositivity_loss_of_zero`,
  `${NAMESPACE}.classifyTerminalSaturationPositivity_bcel_of_positive`,
  `${NAMESPACE}.terminalSaturationPositivity_no_checkedFullLiftAtMinimum`,
  `${NAMESPACE}.classifyTerminalSaturationPositivity_exhaustive`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.terminalProjectionDefect_eq_zero_iff_minima_eq`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.TerminalFullCarrierRealization.checkedFullLift`,
  `${NAMESPACE}.terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum`,
  `${NAMESPACE}.classifyTerminalBCELAnchorNucleus`,
  `${NAMESPACE}.TerminalProperPositiveSupport.saturatedRecords_closed`,
  `${NAMESPACE}.TerminalProperPositiveSupport.physically_compatible`,
  `${NAMESPACE}.TerminalProperPositiveSupport.extracted_semantics`,
]);

const REUSED_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalProjectionDefect_eq_zero_iff_minima_eq`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum`,
  `${NAMESPACE}.TerminalProperPositiveSupport.saturatedRecords_closed`,
  `${NAMESPACE}.TerminalProperPositiveSupport.physically_compatible`,
  `${NAMESPACE}.TerminalProperPositiveSupport.extracted_semantics`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  ...REUSED_THEOREMS,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
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

function commonFailures0(source) {
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
  if (/\b(?:callerCertificate|callerPositive|callerDefect|callerBCELShortcut|hostLookup|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialSaturationPositivity)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalBCELAnchorNucleus',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }

  const wholeCorners = declarationBlock0(
    source,
    'TerminalBCELAnchorProblem.wholeCorners',
  );
  const loss = declarationBlock0(source, 'TerminalProjectionPositivityLoss');
  const lossConstructor = declarationBlock0(
    source,
    'terminalProjectionPositivityLossOfZero',
  );
  const outcome = declarationBlock0(
    source,
    'TerminalSaturationPositivityOutcome',
  );
  const classifier = declarationBlock0(
    source,
    'classifyTerminalSaturationPositivity',
  );
  const positiveSound = declarationBlock0(
    source,
    'classifyTerminalSaturationPositivity_bcel_of_positive',
  );
  const noLift = declarationBlock0(
    source,
    'terminalSaturationPositivity_no_checkedFullLiftAtMinimum',
  );

  for (const token of [
    'problem.carrier problem.anchorRecords []',
    '.optimizationCorners',
    'problem.observe',
  ]) if (!wholeCorners.includes(token)) failures.push('canonical-whole-corners');
  for (const token of [
    'defectZero : problem.familyDefect problem.anchorRecords = 0',
    'comparison : TerminalQuotientComparison problem.wholeCorners.system',
    'atMinimum : comparison.realization.implementation.gateCount =',
    'checkedFullLift : TerminalCheckedFullLift comparison',
  ]) if (!loss.includes(token)) failures.push('proof-bearing-zero-boundary');
  for (const token of [
    'terminalProjectionDefect_eq_zero_iff_minima_eq',
    'terminalFullProfileMinimumRealization',
    'full.project',
    'full.checkedFullLift',
  ]) if (!lossConstructor.includes(token)) failures.push('constructive-zero-lift');
  if (lossConstructor.includes(
    'terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum',
  )) failures.push('prop-existential-elimination');
  const lostIndex = outcome.indexOf('| projectionPositivityLost');
  const bcelIndex = outcome.indexOf('| bcel');
  if (lostIndex === -1 || bcelIndex === -1 || lostIndex >= bcelIndex) {
    failures.push('two-branch-outcome');
  }
  if (outcome.includes('| unknown') || outcome.includes('| callerSelected')) {
    failures.push('two-branch-outcome');
  }
  const classifierOrder = [
    'if defectZero : problem.familyDefect problem.anchorRecords = 0',
    '.projectionPositivityLost',
    'Nat.pos_of_ne_zero defectZero',
    '.bcel wholePositive',
    'classifyTerminalBCELAnchorNucleus problem wholePositive',
  ].map((token) => classifier.indexOf(token));
  if (classifierOrder.some((index) => index === -1)
      || classifierOrder.some((index, offset) => offset > 0
        && index <= classifierOrder[offset - 1])) {
    failures.push('ordered-computed-classifier');
  }
  if (/\(wholePositive\s*:/u.test(classifier)
      || /\(defectZero\s*:/u.test(classifier)) {
    failures.push('caller-positivity-input');
  }
  if (!positiveSound.includes('classifyTerminalBCELAnchorNucleus problem positive')) {
    failures.push('exact-bcel-delegation');
  }
  if (!noLift.includes(
    'terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum',
  )) failures.push('positive-branch-no-lift');
  return [...new Set(failures)];
}

test('terminal saturation-positivity firewall is source-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact public and reused boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 20);
  assert.equal(PUBLIC_DECLARATIONS.length, 11);
  assert.equal(REUSED_DECLARATIONS.length, 9);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalSaturationPositivityFirewall\n',
  ), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalSaturationPositivityFirewall$/mu);
});

test('compiled closure is approved across the positivity firewall', async () => {
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

test('regression covers both whole-defect branches and BCEL propagation', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'saturationFirewallLossDefectZero',
    'TerminalProjectionPositivityLoss saturationFirewallLossProblem',
    'saturationFirewallReadyOutcome = 5',
    'saturationFirewallSingletonOutcome = 1',
    'saturationFirewallSharedOutcome = 2',
    'saturationFirewallRouteOutcome = 4',
    'terminalSaturationPositivity_no_checkedFullLiftAtMinimum',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication pins only the finite saturation-positivity boundary', async () => {
  const [inventory, publication, docs] = await Promise.all([
    text0(INVENTORY_PATH).then(JSON.parse),
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const byName = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  for (const name of PUBLIC_DECLARATIONS) assert.equal(byName.has(name), true, name);
  for (const name of MILESTONE_THEOREMS) {
    const entry = byName.get(name);
    assert.equal(entry?.kind, 'theorem', name);
    assert.equal(entry.axioms.some((axiom) => axiom.startsWith('PNP.')), false, name);
    assert.equal(entry.axioms.includes('Classical.choice'), false, name);
    assert.equal(entry.axioms.includes('sorryAx'), false, name);
  }
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-saturation-positivity-firewall',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-saturation-positivity-firewall');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /zero projection defect/u);
  assert.match(milestone.scope, /positive defect/u);
  assert.match(milestone.nonClaim, /projectionPositivityNotLostSilently/u);
  assert.match(milestone.nonClaim, /transparentSaturationCostBalanced/u);
  assert.match(docs, /Computed terminal saturation-positivity firewall/u);
  assert.match(docs, /checked full lift/u);
});

test('status earns the narrow edge without widening global claims', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  assert.equal(
    status.leanResidualTerminalSaturationPositivityFirewallFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalSaturationPositivityFirewallAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalSaturationPositivityFirewallScope,
    /total-zero-or-positive-whole-support-projection-defect-classification/u);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
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
    /audits\/lean-residual-terminal-saturation-positivity-firewall0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalSaturationPositivityFirewallAxiomAudit\.lean[\s\S]{0,1800}-eq 20/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalSaturationPositivityFirewall\.lean/u);
});

test('hostile saturation-positivity mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('problem.carrier problem.anchorRecords []',
      'problem.carrier [] []'), 'canonical-whole-corners'],
    [source.replace('checkedFullLift : TerminalCheckedFullLift comparison',
      'checkedFullLift : True'), 'proof-bearing-zero-boundary'],
    [source.replace('full.checkedFullLift', 'callerCertificate'),
      'caller-or-host-certificate'],
    [source.replace(
      'if defectZero : problem.familyDefect problem.anchorRecords = 0 then',
      'if callerDefect : problem.familyDefect problem.anchorRecords = 0 then'),
    'caller-or-host-certificate'],
    [source.replace('classifyTerminalBCELAnchorNucleus problem wholePositive',
      'callerBCELShortcut problem wholePositive'),
    'caller-or-host-certificate'],
    [source.replace('classifyTerminalBCELAnchorNucleus problem positive',
      'callerBCELShortcut problem positive'),
    'caller-or-host-certificate'],
    [source.replace('| projectionPositivityLost', '| unknown'),
      'two-branch-outcome'],
    [source.replace(
      '(problem : TerminalBCELAnchorProblem candidate system) :\n    TerminalSaturationPositivityOutcome problem :=',
      '(problem : TerminalBCELAnchorProblem candidate system)\n    (callerPositive : 0 < problem.familyDefect problem.anchorRecords) :\n    TerminalSaturationPositivityOutcome problem :='),
    'caller-or-host-certificate'],
    [`${source}\naxiom saturationShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef saturatePositive : Prop := True\n`, 'overclaim'],
    [`${source}\n#eval 1 + 1\n`, 'host-evaluation'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
