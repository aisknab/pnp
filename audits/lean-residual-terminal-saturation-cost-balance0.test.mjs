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
const TRACE_PATH = 'lean/PNP/ResidualTerminalExecutableSaturation.lean';
const CANDIDATE_PATH = 'lean/PNP/ResidualTerminalCandidateSaturation.lean';
const COST_PATH = 'lean/PNP/ResidualTerminalSaturationCostBalance.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalSaturationCostBalanceAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalSaturationCostBalance.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_saturation_cost_balance.md';
const NAMESPACE = 'PNP.DirectWire';

const TRACE_LOCAL_DECLARATIONS = Object.freeze([
  'terminalFirstSaturationRule?',
  'TerminalSaturationTraceEvent',
  'TerminalSaturationEventsLinked',
  'TerminalSaturationTrace',
  'terminalSaturateTrace',
  'terminalSaturateTrace_eventsLinked',
  'terminalSaturateTrace_records',
  'terminalSaturateTrace_normalizedSeed',
]);

const CANDIDATE_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalExtractedSupport.interfaceIndex?',
  'terminalAmbientSupportCandidate',
  'terminalAmbientSupportImplementation',
  'TerminalCandidateSaturationModel',
  'TerminalCandidateSaturationModel.ambientProfileSystem',
  'terminalSaturationRuleOfProfileRole',
  'terminalGateInfluencesProfile',
  'terminalCandidateRequires',
  'terminalCandidateSaturationSystem',
  'terminalCandidateSaturationSystem_profileSystem',
  'TerminalCandidateProperPositiveSupport',
  'findTerminalCandidateProperPositiveSupport',
  'TerminalCandidateBCELAnchorProblem',
  'TerminalCandidateBCELAnchorProblem.toProblem',
  'classifyTerminalCandidateSaturationPositivity',
]);

const COST_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalSaturationCostSnapshot',
  'terminalSaturationCostSnapshot',
  'terminalSaturationEventCost',
  'terminalSaturationEventOwners',
  'TerminalTransparentSaturationStep',
  'TerminalTransparentSaturationStep.rulePresent',
  'TerminalTransparentSaturationStep.uniqueMaterializerOwner',
  'TerminalTransparentSaturationStep.supportCostBalanced',
  'TerminalTransparentSaturationStep.fullCostBalanced',
  'TerminalTransparentSaturationStep.quotientCostBounded',
  'TerminalTransparentSaturationStep.fullSlack_preserved',
  'TerminalTransparentSaturationStep.projectionDefect_mono',
  'TerminalTransparentSaturationStep.fullPositive_preserved',
  'TerminalSaturationEventsLinked.fullSlack_preserved',
  'TerminalSaturationEventsLinked.projectionDefect_mono',
  'TerminalSaturationEventsLinked.fullPositive_preserved',
  'TerminalNontransparentSaturationReason',
  'TerminalSaturationStepBalanceOutcome',
  'classifyTerminalSaturationStepBalance',
  'terminalSaturationStepTransparentBool',
  'terminalSaturationStepFailureReason?',
  'TerminalFirstNontransparentSaturationStep',
  'TerminalSaturationBalanceOutcome',
  'classifyTerminalSaturationBalance',
  'terminalSaturationBalanceBalancedBool',
  'terminalSaturationBalanceFirstFailure?',
  'TerminalSaturationBalanceOutcome.balanced_event',
  'TerminalSaturationBalanceOutcome.balanced_fullSlack_preserved',
  'TerminalSaturationBalanceOutcome.balanced_projectionDefect_mono',
  'TerminalSaturationBalanceOutcome.balanced_fullPositive_preserved',
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...TRACE_LOCAL_DECLARATIONS,
  ...CANDIDATE_LOCAL_DECLARATIONS,
  ...COST_LOCAL_DECLARATIONS,
].map((name) => `${NAMESPACE}.${name}`));

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalSaturateTrace_eventsLinked`,
  `${NAMESPACE}.terminalSaturateTrace_records`,
  `${NAMESPACE}.terminalCandidateSaturationSystem_profileSystem`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.uniqueMaterializerOwner`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.supportCostBalanced`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.fullCostBalanced`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.quotientCostBounded`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.fullSlack_preserved`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.projectionDefect_mono`,
  `${NAMESPACE}.TerminalTransparentSaturationStep.fullPositive_preserved`,
  `${NAMESPACE}.TerminalSaturationEventsLinked.fullSlack_preserved`,
  `${NAMESPACE}.TerminalSaturationEventsLinked.projectionDefect_mono`,
  `${NAMESPACE}.TerminalSaturationEventsLinked.fullPositive_preserved`,
  `${NAMESPACE}.TerminalSaturationBalanceOutcome.balanced_event`,
  `${NAMESPACE}.TerminalSaturationBalanceOutcome.balanced_fullSlack_preserved`,
  `${NAMESPACE}.TerminalSaturationBalanceOutcome.balanced_projectionDefect_mono`,
  `${NAMESPACE}.TerminalSaturationBalanceOutcome.balanced_fullPositive_preserved`,
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
  if (/\b(?:callerRequires|callerCost|callerOwner|callerTransparent|callerFailure|hostLookup|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialSaturationBalance)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateTrace0(source) {
  const failures = commonFailures0(source);
  for (const name of TRACE_LOCAL_DECLARATIONS) {
    if (!declarationBlock0(source, name)) failures.push('trace-surface');
  }
  const event = declarationBlock0(source, 'TerminalSaturationTraceEvent');
  const step = source.slice(source.indexOf('private def terminalSaturationTraceStep'),
    source.indexOf('private theorem terminalSaturationTraceStep_linked'));
  const trace = declarationBlock0(source, 'terminalSaturateTrace');
  for (const token of ['kind?', 'dependent', 'required', 'beforeRecords', 'afterRecords']) {
    if (!event.includes(token)) failures.push('rule-labelled-event');
  }
  for (const token of [
    'terminalFirstSaturationRule? system current.record required',
    'beforeRecords := state.costRecords',
    'afterRecords := afterRecords',
    'events := state.events ++ [event]',
  ]) if (!step.includes(token)) failures.push('continuous-trace-step');
  for (const token of [
    'records := terminalSaturateRecords system seed',
    'replayRecords := final.costRecords',
  ]) if (!trace.includes(token)) failures.push('exact-old-saturation-boundary');
  return [...new Set(failures)];
}

function validateCandidate0(source) {
  const failures = commonFailures0(source);
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(CANDIDATE_LOCAL_DECLARATIONS)) {
    failures.push('candidate-declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalSaturationPositivityFirewall',
  ])) failures.push('candidate-closed-import');
  const model = declarationBlock0(source, 'TerminalCandidateSaturationModel');
  const influence = declarationBlock0(source, 'terminalGateInfluencesProfile');
  const requires = declarationBlock0(source, 'terminalCandidateRequires');
  const system = declarationBlock0(source, 'terminalCandidateSaturationSystem');
  for (const token of ['profileSystem', 'projection', 'observe']) {
    if (!model.includes(token)) failures.push('executable-model');
  }
  if (/\brequires\b/u.test(model) || /certificate|correctness|soundness/iu.test(model)) {
    failures.push('caller-derived-relation');
  }
  for (const token of [
    'terminalListSubsets otherGates',
    'terminalAmbientSupportImplementation candidate after',
    'terminalAmbientSupportImplementation candidate before',
    'model.observe',
  ]) if (!influence.includes(token)) failures.push('context-exhaustive-influence');
  for (const token of [
    'terminalCandidateGateSourceRequires',
    'terminalCandidateInterfaceRequires',
    'terminalCandidateProfileRequires',
  ]) if (!requires.includes(token)) failures.push('candidate-derived-relation');
  if (!system.includes('requires := terminalCandidateRequires candidate model')) {
    failures.push('candidate-derived-system');
  }
  return [...new Set(failures)];
}

function validateCost0(source) {
  const failures = commonFailures0(source);
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(COST_LOCAL_DECLARATIONS)) {
    failures.push('cost-declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalCandidateSaturation',
  ])) failures.push('cost-closed-import');
  const snapshot = declarationBlock0(source, 'terminalSaturationCostSnapshot');
  const owners = declarationBlock0(source, 'terminalSaturationEventOwners');
  const transparent = declarationBlock0(source, 'TerminalTransparentSaturationStep');
  const reason = declarationBlock0(source,
    'TerminalNontransparentSaturationReason');
  const first = declarationBlock0(source,
    'TerminalFirstNontransparentSaturationStep');
  const classifier = declarationBlock0(source,
    'classifyTerminalSaturationBalance');
  for (const token of [
    'terminalAmbientSupportImplementation candidate records',
    'terminalFullProfileMinimum system current',
    'terminalQuotientProfileMinimum system model.projection current',
  ]) if (!snapshot.includes(token)) failures.push('recomputed-cost-snapshot');
  for (const token of ['event.beforeRecords.flatMap', 'system.requires']) {
    if (!owners.includes(token)) failures.push('derived-active-ownership');
  }
  for (const token of [
    'event.kind? ≠ none',
    'terminalSaturationEventOwners',
    ').length = 1',
    ').supportSize =',
    ').fullMinimum =',
    ').quotientMinimum ≤',
  ]) if (!transparent.includes(token)) failures.push('exact-transparent-contract');
  for (const token of [
    '| missingRule',
    '| nonuniqueMaterializerOwner',
    '| supportCostMismatch',
    '| fullCostMismatch',
    '| quotientCostExceeded',
  ]) if (!reason.includes(token)) failures.push('typed-failure-reasons');
  for (const token of [
    'prior', 'event', 'remaining', 'split', 'priorTransparent', 'reason', 'failure',
  ]) if (!first.includes(token)) failures.push('exact-first-failure');
  for (const token of [
    'terminalSaturateTrace',
    'terminalCandidateSaturationSystem candidate model',
    'classifyTerminalSaturationBalanceEvents',
  ]) if (!classifier.includes(token)) failures.push('production-trace-classifier');
  for (const theorem of [
    'TerminalSaturationEventsLinked.fullSlack_preserved',
    'TerminalSaturationEventsLinked.projectionDefect_mono',
    'TerminalSaturationBalanceOutcome.balanced_fullSlack_preserved',
    'TerminalSaturationBalanceOutcome.balanced_fullPositive_preserved',
  ]) if (!declarationBlock0(source, theorem)) failures.push('aggregate-balance');
  return [...new Set(failures)];
}

test('candidate-derived saturation and cost balance are source-closed', async () => {
  const [trace, candidate, cost] = await Promise.all([
    text0(TRACE_PATH), text0(CANDIDATE_PATH), text0(COST_PATH),
  ]);
  assert.deepEqual(validateTrace0(trace), []);
  assert.deepEqual(validateCandidate0(candidate), []);
  assert.deepEqual(validateCost0(cost), []);
});

test('axiom transcript covers the exact 53-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 53);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalSaturationCostBalance\n'), true);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualTerminalCandidateSaturation$/mu);
  assert.match(root, /^import PNP\.ResidualTerminalSaturationCostBalance$/mu);
});

test('compiled closure is approved for every milestone theorem', async () => {
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

test('regression exercises derived edges, exact costs, and first failure', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalGateInfluencesProfile derivedBalanceCandidate',
    'derivedBalanceTrace.events.map',
    'terminalSaturationStepTransparentBool',
    'derivedBalanceMultipleOwnerEvent',
    'some .nonuniqueMaterializerOwner',
    'terminalSaturationBalanceBalancedBool',
    'terminalSaturationBalanceFirstFailure?',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication records only the finite candidate-derived balance milestone', async () => {
  const [publication, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse), text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-candidate-saturation-cost-balance',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-candidate-saturation-cost-balance');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /candidate-derived dependency system/u);
  assert.match(milestone.scope, /first nontransparent event/u);
  assert.match(milestone.nonClaim, /interfaceExposureRoutesToE/u);
  assert.match(milestone.nonClaim, /originKernelObligationClosureRouted/u);
  assert.match(docs, /Candidate-derived terminal saturation cost balance/u);
  assert.match(docs, /exact first nontransparent event/u);
});

test('status earns the narrow edge without widening global claims', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  assert.equal(status.leanResidualTerminalCandidateSaturationFormalized, true);
  assert.equal(status.leanResidualTerminalSaturationCostBalanceFormalized, true);
  assert.equal(status.leanResidualTerminalFirstNontransparentStepFormalized, true);
  assert.equal(status.leanResidualTerminalSaturationCostBalanceAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalSaturationCostBalanceScope,
    /candidate-derived-dependency-system/u);
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
    /audits\/lean-residual-terminal-saturation-cost-balance0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalSaturationCostBalanceAxiomAudit\.lean[\s\S]{0,1800}-eq 53/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalSaturationCostBalance\.lean/u);
});

test('hostile candidate and cost mutations fail closed', async () => {
  const [trace, candidate, cost] = await Promise.all([
    text0(TRACE_PATH), text0(CANDIDATE_PATH), text0(COST_PATH),
  ]);
  const mutations = [
    [validateTrace0, trace.replace(
      'records := terminalSaturateRecords system seed',
      'records := final.costRecords'), 'exact-old-saturation-boundary'],
    [validateCandidate0, candidate.replace(
      'observe : Implementation (inputs + gates) gates →',
      'callerRequires : Bool\n  observe : Implementation (inputs + gates) gates →'),
    'caller-or-host-certificate'],
    [validateCandidate0, candidate.replace(
      'terminalListSubsets otherGates', '[[]]'),
    'context-exhaustive-influence'],
    [validateCandidate0, candidate.replace(
      'requires := terminalCandidateRequires candidate model',
      'requires := fun _kind _dependent _required => false'),
    'candidate-derived-system'],
    [validateCost0, cost.replace('event.beforeRecords.flatMap',
      '[].flatMap'), 'derived-active-ownership'],
    [validateCost0, cost.replace(').length = 1', ').length = 0'),
    'exact-transparent-contract'],
    [validateCost0, `${cost}\naxiom saturationBalanceShortcut : True\n`,
      'assumption-declaration'],
    [validateCost0, `${cost}\ndef saturatePositive : Prop := True\n`,
      'overclaim'],
    [validateCost0, `${cost}\n#eval 1 + 1\n`, 'host-evaluation'],
  ];
  for (const [validate, mutated, expected] of mutations) {
    assert.equal(validate(mutated).includes(expected), true, expected);
  }
});
