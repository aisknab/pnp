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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalBCELAnchorNucleus.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBCELAnchorNucleusAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBCELAnchorNucleus.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_bcel_anchor_nucleus.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBCELAnchorProblem',
  'TerminalBCELAnchorProblem.anchorRecords',
  'TerminalBCELAnchorProblem.mem_anchorRecords_iff',
  'TerminalBCELAnchorProblem.anchorRecords_nodup',
  'TerminalBCELAnchorProblem.allAnchorSubfamilies',
  'TerminalBCELAnchorProblem.anchorRecords_mem_allAnchorSubfamilies',
  'TerminalBCELAnchorProblem.carrier',
  'TerminalBCELAnchorProblem.familyDefect',
  'TerminalMinimalPositiveAnchorNucleus',
  'findTerminalPositiveAnchorNucleus',
  'findTerminalPositiveAnchorNucleus_sound',
  'findTerminalPositiveAnchorNucleus_eq_none_iff',
  'findTerminalPositiveAnchorNucleus_exists_of_whole_positive',
  'findTerminalPositiveAnchorNucleus_unique',
  'terminalBCELAnchorIntersection',
  'terminalBCELAnchorUnion',
  'TerminalBCELAnchorAlgebraLaw',
  'TerminalBCELAnchorAlgebraCheck',
  'TerminalBCELAnchorAlgebraCheck.Holds',
  'TerminalBCELAnchorAlgebraCheck.disagrees',
  'TerminalBCELAnchorAlgebraCheck.disagrees_eq_true_iff',
  'allTerminalBCELAnchorAlgebraChecks',
  'terminalBCELAnchorAlgebraCheck_mem',
  'mem_allTerminalBCELAnchorAlgebraChecks_governed',
  'TerminalBCELAnchorAlgebra',
  'firstTerminalBCELAnchorAlgebraMismatch?',
  'firstTerminalBCELAnchorAlgebraMismatch?_sound',
  'firstTerminalBCELAnchorAlgebraMismatch?_eq_none_iff',
  'TerminalBCELAnchorAlgebraFailure',
  'TerminalBCELAnchorAlgebraClassification',
  'classifyTerminalBCELAnchorAlgebra',
  'TerminalBCELProperCutSeed',
  'terminalBCELProperCutSeedBool',
  'terminalBCELProperCutSeedBool_eq_true_iff',
  'allTerminalBCELProperCutSeeds',
  'mem_allTerminalBCELProperCutSeeds_iff',
  'terminalBCELAnchorComplement',
  'TerminalBCELAnchorProblem.cutCarrier',
  'TerminalBCELAnchorProblem.cutDefect',
  'TerminalBCELCutDefectKind',
  'TerminalBCELCutDefectCheck',
  'TerminalBCELCutDefectCheck.Holds',
  'TerminalBCELCutDefectCheck.disagrees',
  'TerminalBCELCutDefectCheck.disagrees_eq_true_iff',
  'allTerminalBCELCutDefectChecks',
  'terminalBCELCutDefectCheck_mem',
  'mem_allTerminalBCELCutDefectChecks_proper',
  'firstTerminalBCELCutDefectMismatch?',
  'firstTerminalBCELCutDefectMismatch?_sound',
  'firstTerminalBCELCutDefectMismatch?_eq_none_all',
  'TerminalBCELCutDefectFailure',
  'TerminalBCELCutRoute',
  'TerminalBCELCutRoute.Selected',
  'firstTerminalBCELCutRoute?',
  'firstTerminalBCELCutRoute?_sound',
  'firstTerminalBCELCutRoute?_eq_none_noRoutes',
  'TerminalBCELCutRouteFailure',
  'TerminalComputedBCELCutConclusion',
  'computedBCELCutConclusionOfNoFailures',
  'TerminalComputedBCELAnchorNucleus',
  'TerminalBCELInsufficientNucleusFailure',
  'TerminalBCELAnchorNucleusOutcome',
  'classifyTerminalBCELAnchorNucleus',
  'TerminalComputedBCELAnchorNucleus.strictSubfamily_defect_zero',
  'TerminalComputedBCELAnchorNucleus.anchorSizeAtLeastTwo',
  'TerminalComputedBCELAnchorNucleus.properCutConstantEquation',
  'TerminalComputedBCELAnchorNucleus.properCutLocalConclusion',
  'classifyTerminalBCELAnchorNucleus_exhaustive',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBCELAnchorProblem.mem_anchorRecords_iff`,
  `${NAMESPACE}.TerminalBCELAnchorProblem.anchorRecords_nodup`,
  `${NAMESPACE}.TerminalBCELAnchorProblem.anchorRecords_mem_allAnchorSubfamilies`,
  `${NAMESPACE}.findTerminalPositiveAnchorNucleus_sound`,
  `${NAMESPACE}.findTerminalPositiveAnchorNucleus_eq_none_iff`,
  `${NAMESPACE}.findTerminalPositiveAnchorNucleus_exists_of_whole_positive`,
  `${NAMESPACE}.findTerminalPositiveAnchorNucleus_unique`,
  `${NAMESPACE}.TerminalBCELAnchorAlgebraCheck.disagrees_eq_true_iff`,
  `${NAMESPACE}.terminalBCELAnchorAlgebraCheck_mem`,
  `${NAMESPACE}.mem_allTerminalBCELAnchorAlgebraChecks_governed`,
  `${NAMESPACE}.firstTerminalBCELAnchorAlgebraMismatch?_sound`,
  `${NAMESPACE}.firstTerminalBCELAnchorAlgebraMismatch?_eq_none_iff`,
  `${NAMESPACE}.terminalBCELProperCutSeedBool_eq_true_iff`,
  `${NAMESPACE}.mem_allTerminalBCELProperCutSeeds_iff`,
  `${NAMESPACE}.TerminalBCELCutDefectCheck.disagrees_eq_true_iff`,
  `${NAMESPACE}.terminalBCELCutDefectCheck_mem`,
  `${NAMESPACE}.mem_allTerminalBCELCutDefectChecks_proper`,
  `${NAMESPACE}.firstTerminalBCELCutDefectMismatch?_sound`,
  `${NAMESPACE}.firstTerminalBCELCutDefectMismatch?_eq_none_all`,
  `${NAMESPACE}.firstTerminalBCELCutRoute?_sound`,
  `${NAMESPACE}.firstTerminalBCELCutRoute?_eq_none_noRoutes`,
  `${NAMESPACE}.computedBCELCutConclusionOfNoFailures`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.strictSubfamily_defect_zero`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.anchorSizeAtLeastTwo`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.properCutConstantEquation`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.properCutLocalConclusion`,
  `${NAMESPACE}.classifyTerminalBCELAnchorNucleus_exhaustive`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.allTerminalPrimitiveRecords_nodup`,
  `${NAMESPACE}.filter_mem_terminalListSubsets`,
  `${NAMESPACE}.mem_allTerminalPrimitiveRecords`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumRoute?_sound`,
  `${NAMESPACE}.TerminalFourCornerOptimumRoutedFailure.sound`,
  `${NAMESPACE}.TerminalComputedBN2SquareLegitimate`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2SquareLegitimate`,
  `${NAMESPACE}.TerminalComputedBN2LocalConclusion`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2LocalConclusion`,
  `${NAMESPACE}.TerminalProjectionFourCorners.constantCutEquation_of_defects`,
  `${NAMESPACE}.TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut`,
]);

const REUSED_THEOREMS = Object.freeze([
  `${NAMESPACE}.allTerminalPrimitiveRecords_nodup`,
  `${NAMESPACE}.filter_mem_terminalListSubsets`,
  `${NAMESPACE}.mem_allTerminalPrimitiveRecords`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumRoute?_sound`,
  `${NAMESPACE}.TerminalFourCornerOptimumRoutedFailure.sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2SquareLegitimate`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2LocalConclusion`,
  `${NAMESPACE}.TerminalProjectionFourCorners.constantCutEquation_of_defects`,
  `${NAMESPACE}.TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut`,
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
  if (/\b(?:hostLookup|anchorCertificate|algebraCertificate|cutCertificate|routeCertificate|silenceCertificate|callerCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialAnchorNucleus)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateSource0(source) {
  const failures = commonFailures0(source);
  const stripped = stripLeanCommentsAndStrings0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalBN2SquareLegitimacy',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }

  const anchors = declarationBlock0(
    source,
    'TerminalBCELAnchorProblem.anchorRecords',
  );
  const familyDefect = declarationBlock0(
    source,
    'TerminalBCELAnchorProblem.familyDefect',
  );
  const minimum = declarationBlock0(source, 'TerminalMinimalPositiveAnchorNucleus');
  const finder = declarationBlock0(source, 'findTerminalPositiveAnchorNucleus');
  const algebraChecks = declarationBlock0(
    source,
    'allTerminalBCELAnchorAlgebraChecks',
  );
  const cutSeeds = declarationBlock0(source, 'allTerminalBCELProperCutSeeds');
  const cutDefects = declarationBlock0(source, 'allTerminalBCELCutDefectChecks');
  const cutRoute = declarationBlock0(source, 'firstTerminalBCELCutRoute?');
  const routeSound = declarationBlock0(source, 'firstTerminalBCELCutRoute?_sound');
  const cutConclusion = declarationBlock0(
    source,
    'TerminalComputedBCELCutConclusion',
  );
  const cutConstructor = declarationBlock0(
    source,
    'computedBCELCutConclusionOfNoFailures',
  );
  const outcome = declarationBlock0(source, 'TerminalBCELAnchorNucleusOutcome');
  const classifier = declarationBlock0(source, 'classifyTerminalBCELAnchorNucleus');

  for (const token of [
    'allTerminalPrimitiveRecords',
    '.filter',
    'problem.support.saturatedRecords',
  ]) if (!anchors.includes(token)) failures.push('canonical-anchor-universe');
  if (!familyDefect.includes('problem.carrier family []')
      || !familyDefect.includes('corners.left')) {
    failures.push('family-defect-left-corner');
  }
  for (const token of [
    'positive : 0 < problem.familyDefect anchors',
    'minimumCardinality',
    'smaller.length < anchors.length',
    'problem.familyDefect smaller = 0',
  ]) if (!minimum.includes(token)) failures.push('minimum-positive-contract');
  if (!finder.includes('minimumPositiveAnchorOutcome')
      || !finder.includes('problem.allAnchorSubfamilies')) {
    failures.push('computed-minimum-search');
  }
  const meetIndex = algebraChecks.indexOf('law := .meet');
  const joinIndex = algebraChecks.indexOf('law := .join');
  for (const token of [
    'terminalListSubsets nucleus',
    'allTerminalPrimitiveRecords inputs gates outputs profileWidth',
  ]) if (!algebraChecks.includes(token)) failures.push('exhaustive-anchor-algebra');
  if (meetIndex === -1 || joinIndex === -1 || meetIndex >= joinIndex) {
    failures.push('meet-before-join');
  }
  if (!cutSeeds.includes('terminalListSubsets nucleus')
      || !cutSeeds.includes('terminalBCELProperCutSeedBool nucleus')) {
    failures.push('canonical-proper-cuts');
  }
  const defectOrder = [
    '.meetZero', '.leftZero', '.rightZero', '.joinNucleus',
  ].map((token) => cutDefects.indexOf(token));
  if (defectOrder.some((index) => index === -1)
      || defectOrder.some((index, offset) => offset > 0
        && index <= defectOrder[offset - 1])) {
    failures.push('ordered-cut-defect-firewall');
  }
  if (!cutRoute.includes('allTerminalBCELProperCutSeeds nucleus')) {
    failures.push('canonical-cut-route-scan');
  }
  for (const token of [
    'TerminalBCELProperCutSeed nucleus route.cut',
    'route.Selected',
    'route.failure.Sound',
    'firstOptimumRoute?_sound',
  ]) if (!routeSound.includes(token)) failures.push('proof-bearing-route-soundness');
  for (const token of [
    'TerminalComputedBN2SquareLegitimate',
    'meetDefect',
    'leftDefect',
    'rightDefect',
    'joinDefect',
    'constantCutEquation',
    'positiveExcess : 0 <',
    'TerminalComputedBN2LocalConclusion',
  ]) if (!cutConclusion.includes(token)) failures.push('complete-cut-conclusion');
  for (const token of [
    'firstTerminalBCELCutDefectMismatch?_eq_none_all',
    'firstTerminalBCELCutRoute?_eq_none_noRoutes',
    'computedBN2SquareLegitimate',
    'constantCutEquation_of_defects',
    'projectionExcess_pos_of_constantCut',
    'computedBN2LocalConclusion',
  ]) if (!cutConstructor.includes(token)) failures.push('computed-cut-constructor');
  for (const token of [
    '| insufficient', '| algebraFailure', '| cutDefectFailure',
    '| cutRouteFailure', '| ready',
  ]) if (!outcome.includes(token)) failures.push('total-outcome-surface');
  const classifierOrder = [
    'if atLeastTwo',
    'classifyTerminalBCELAnchorAlgebra',
    'firstTerminalBCELCutDefectMismatch?',
    'firstTerminalBCELCutRoute?',
    '.ready',
  ].map((token) => classifier.indexOf(token));
  if (classifierOrder.some((index) => index === -1)
      || classifierOrder.some((index, offset) => offset > 0
        && index <= classifierOrder[offset - 1])) {
    failures.push('ordered-total-classifier');
  }
  for (const token of [
    'defectChecksSilent := defectFound',
    'routeChecksSilent := routeFound',
    'computedBCELCutConclusionOfNoFailures',
  ]) if (!classifier.includes(token)) failures.push('ready-retains-computed-scans');
  if (!stripped.includes('findTerminalPositiveAnchorNucleus_eq_none_iff')
      || !stripped.includes('classifyTerminalBCELAnchorNucleus_exhaustive')) {
    failures.push('total-search-boundary');
  }
  return [...new Set(failures)];
}

test('computed terminal BCEL anchor nucleus is source-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact public boundary and reused dependencies', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 79);
  assert.equal(PUBLIC_DECLARATIONS.length, 68);
  assert.equal(REUSED_DECLARATIONS.length, 11);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBCELAnchorNucleus\n',
  ), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalBCELAnchorNucleus$/mu);
});

test('compiled closure is approved across the anchor boundary', async () => {
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

test('regression covers computed selection and the fail-closed branches', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'bcelAnchorReadyFoundLength = some 2',
    'bcelAnchorSingletonOutcome = (0, 1)',
    'bcelAnchorSharedOutcome = (1, true)',
    'bcelAnchorRouteOutcome = (3, true)',
    'TerminalSupportProper',
    'TerminalSupportPositive',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication pins only the computed finite anchor boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-computed-bcel-anchor-nucleus',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-computed-bcel-anchor-nucleus');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /minimum-cardinality positive anchor nucleus/u);
  assert.match(milestone.scope, /full-before-quotient/u);
  assert.match(milestone.nonClaim, /positive whole-support projection defect/u);
  assert.match(milestone.nonClaim, /SaturatePositive/u);
  assert.match(docs, /Computed terminal BCEL anchor nucleus/u);
  assert.match(docs, /cut-defect branch/u);
});

test('status earns the scoped anchor edge without widening global claims', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalComputedBCELAnchorNucleusFormalized',
    'leanResidualTerminalBCELMinimumPositiveNucleusFormalized',
    'leanResidualTerminalBCELAnchorAlgebraFormalized',
    'leanResidualTerminalBCELCutDefectFirewallFormalized',
    'leanResidualTerminalBCELCutRouteDichotomyFormalized',
    'leanResidualTerminalBCELConstantCutConclusionFormalized',
    'leanResidualTerminalBCELAnchorNucleusAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.match(status.leanResidualTerminalBCELAnchorNucleusScope,
    /positive-whole-support-projection-defect/u);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-bcel-anchor-nucleus0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalBCELAnchorNucleusAxiomAudit\.lean[\s\S]{0,1800}-eq 79/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalBCELAnchorNucleus\.lean/u);
});

test('hostile anchor-nucleus mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('allTerminalPrimitiveRecords inputs gates outputs profileWidth',
      'hostAnchorRecords inputs gates outputs profileWidth'),
    'canonical-anchor-universe'],
    [source.replace('problem.carrier family []', 'problem.carrier family family'),
      'family-defect-left-corner'],
    [source.replace('positive : 0 < problem.familyDefect anchors',
      'positive : True'), 'minimum-positive-contract'],
    [source.replace('law := .meet },\n           { left := left, right := right, record := record, law := .join',
      'law := .join },\n           { left := left, right := right, record := record, law := .meet'),
    'meet-before-join'],
    [source.replace(
      '(terminalListSubsets nucleus).filter\n    (terminalBCELProperCutSeedBool nucleus)',
      '(terminalListSubsets nucleus).filter\n    (callerCutSelector nucleus)'),
    'canonical-proper-cuts'],
    [source.replace('{ cut := cut, kind := .leftZero },',
      '{ cut := cut, kind := .joinNucleus },'),
    'ordered-cut-defect-firewall'],
    [source.replaceAll('route.failure.Sound', 'True'),
      'proof-bearing-route-soundness'],
    [source.replace('positiveExcess : 0 <', 'positiveExcess : 0 ≤'),
      'complete-cut-conclusion'],
    [source.replace('constantCutEquation_of_defects', 'callerCertificate'),
      'caller-or-host-certificate'],
    [source.replace('| cutDefectFailure', '| skippedDefectFailure'),
      'total-outcome-surface'],
    [source.replace(
      'match classifyTerminalBCELAnchorAlgebra\n            problem nucleus.anchors with',
      'match classifyTerminalBCELAnchorShortcut\n            problem nucleus.anchors with'),
    'ordered-total-classifier'],
    [source.replace('defectChecksSilent := defectFound',
      'defectChecksSilent := callerCertificate'),
    'caller-or-host-certificate'],
    [`${source}\naxiom anchorShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef bcelReady : Prop := True\n`, 'overclaim'],
    [`${source}\n#eval 1 + 1\n`, 'host-evaluation'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
