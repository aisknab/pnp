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
const EXECUTABLE_PATH = 'lean/PNP/ResidualTerminalExecutableSaturation.lean';
const PHYSICAL_PATH = 'lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPhysicalSupportCompletionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPhysicalSupportCompletion.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_physical_support_completion.md';
const NAMESPACE = 'PNP.DirectWire';

const EXECUTABLE_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.allTerminalSaturationRuleKinds`,
  `${NAMESPACE}.mem_allTerminalSaturationRuleKinds`,
  `${NAMESPACE}.terminalSaturationEdge`,
  `${NAMESPACE}.terminalSaturationEdge_eq_true_iff`,
  `${NAMESPACE}.terminalSaturateRecords`,
  `${NAMESPACE}.terminalSaturateRecords_extensive`,
  `${NAMESPACE}.terminalSaturateRecords_sound`,
  `${NAMESPACE}.terminalSaturateRecords_closed`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
]);

const PHYSICAL_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalSupportWire`,
  `${NAMESPACE}.allTerminalSupportWires`,
  `${NAMESPACE}.mem_allTerminalSupportWires`,
  `${NAMESPACE}.Source.terminalSupportWire?`,
  `${NAMESPACE}.Program.terminalGateSources`,
  `${NAMESPACE}.Program.terminalGateUsesWire`,
  `${NAMESPACE}.terminalGateSelected`,
  `${NAMESPACE}.terminalWireExternal`,
  `${NAMESPACE}.terminalBoundaryWire`,
  `${NAMESPACE}.terminalGateHasExternalConsumer`,
  `${NAMESPACE}.terminalGateIsGlobalOutput`,
  `${NAMESPACE}.terminalInterfaceGate`,
  `${NAMESPACE}.terminalGateSelected_eq_true_iff`,
  `${NAMESPACE}.terminalWireExternal_eq_true_iff`,
  `${NAMESPACE}.terminalBoundaryWire_eq_true_iff`,
  `${NAMESPACE}.terminalGateHasExternalConsumer_eq_true_iff`,
  `${NAMESPACE}.terminalInterfaceGate_eq_true_iff`,
  `${NAMESPACE}.terminalBoundaryPorts`,
  `${NAMESPACE}.terminalInterfacePorts`,
  `${NAMESPACE}.mem_terminalBoundaryPorts_iff`,
  `${NAMESPACE}.mem_terminalInterfacePorts_iff`,
  `${NAMESPACE}.TerminalPhysicalCompletedSupport`,
  `${NAMESPACE}.completeTerminalPhysicalSupport`,
  `${NAMESPACE}.TerminalPhysicalCompletedSupport.SourceAccounted`,
  `${NAMESPACE}.TerminalPhysicalCompletedSupport.Compatible`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_incoming_complete`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_outgoing_complete`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_records`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_compatible`,
]);

const PUBLIC_DECLARATIONS = Object.freeze([
  ...EXECUTABLE_DECLARATIONS,
  ...PHYSICAL_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.mem_allTerminalSaturationRuleKinds`,
  `${NAMESPACE}.terminalSaturationEdge_eq_true_iff`,
  `${NAMESPACE}.terminalSaturateRecords_extensive`,
  `${NAMESPACE}.terminalSaturateRecords_sound`,
  `${NAMESPACE}.terminalSaturateRecords_closed`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.mem_allTerminalSupportWires`,
  `${NAMESPACE}.mem_terminalBoundaryPorts_iff`,
  `${NAMESPACE}.mem_terminalInterfacePorts_iff`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_incoming_complete`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_outgoing_complete`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_records`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_compatible`,
]);

const EXECUTABLE_PRIVATE_HELPERS = Object.freeze([
  'terminalAny',
  'terminalAny_true_iff',
  'nodup_of_listNoDuplicates',
  'allTerminalPrimitiveRecords_nodup',
  'TerminalSaturationWorkState',
  'TerminalSaturationWorkState.known',
  'terminalNewRequiredRecords',
  'mem_terminalNewRequiredRecords_iff',
  'terminalNewRequiredRecords_nodup',
  'terminalSaturationStep',
  'terminalSaturationWork',
  'mem_reordered_terminal_work_lists',
  'reordered_terminal_work_lists_nodup',
  'terminalSaturationStep_known_eq',
  'TerminalSaturationWorkState.FinitelySupported',
  'terminalSaturationStep_finitelySupported',
  'terminalSaturationWork_finitelySupported',
  'listNoDuplicates_of_nodup',
  'terminalSaturationWork_pending_empty',
  'terminalSaturationWork_processed_length_of_pending_ne',
  'terminalSaturationStep_known_mono',
  'terminalSaturationWork_known_mono',
  'TerminalSaturationWorkState.SaturationSound',
  'terminalSaturationStep_sound',
  'terminalSaturationWork_sound',
  'TerminalSaturationWorkState.FrontierClosed',
  'terminalSaturationStep_frontierClosed',
  'terminalSaturationWork_frontierClosed',
  'terminalSaturationInitialState',
  'terminalSaturationInitialState_finitelySupported',
  'terminalSaturationInitialState_sound',
  'terminalSaturationInitialState_frontierClosed',
  'mem_terminalSaturationInitialState_known_of_mem',
  'terminalSaturationFinalState',
  'terminalSaturationFinalState_pending_empty',
  'terminalSaturationFinalState_sound',
  'terminalSaturationFinalState_frontierClosed',
]);

const PHYSICAL_PRIVATE_HELPERS = Object.freeze([
  'physicalTerminalAny',
  'physicalTerminalAny_true_iff',
  'sourceMatchesTerminalWire',
  'sourceMatchesTerminalWire_self',
  'gateUsesWire_of_left',
  'gateUsesWire_of_right',
  'boundaryWire_of_selected_source',
  'sourceAccounted',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
}

function privateHelpers0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return [...stripped.matchAll(
    /^private\s+(?:def|theorem|inductive|structure|abbrev)\s+([^\s({:]+)/gmu,
  )].map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function commonFailures0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|dependencyCertificate|saturationCertificate|closureCertificate)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|properSupport|supportCompletion|projectionSquare|squareLegitimate|saturatePositive|bcelReady|completeGainRoute|zeroSlackComplete|pccMinExact)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateExecutable0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalSaturation',
    'PNP.DirectWireBaseline',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(EXECUTABLE_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(EXECUTABLE_PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const kinds = declarationBlock0(source, 'allTerminalSaturationRuleKinds');
  const edge = declarationBlock0(source, 'terminalSaturationEdge');
  const newRequired = source.slice(
    source.indexOf('private def terminalNewRequiredRecords'),
    source.indexOf('private theorem mem_terminalNewRequiredRecords_iff'),
  );
  const work = source.slice(
    source.indexOf('private def terminalSaturationStep'),
    source.indexOf('private theorem mem_reordered_terminal_work_lists'),
  );
  const finalState = source.slice(
    source.indexOf('private def terminalSaturationFinalState'),
    source.indexOf('private theorem terminalSaturationFinalState_pending_empty'),
  );
  const output = declarationBlock0(source, 'terminalSaturateRecords');
  const exact = declarationBlock0(source, 'mem_terminalSaturateRecords_iff');
  for (const kind of [
    '.gateSource', '.interfaceConsumer', '.origin', '.kernel', '.obligation',
    '.prefixTail', '.budget', '.saturation', '.direction', '.charge',
  ]) if (!kinds.includes(kind)) failures.push('ten-rule-schedule');
  if (!/terminalAny allTerminalSaturationRuleKinds[\s\S]*system\.requires kind dependent required/u.test(edge)) {
    failures.push('rule-union-edge');
  }
  if (!/allTerminalPrimitiveRecords[\s\S]*\.filter[\s\S]*terminalSaturationEdge system dependent required &&[\s\S]*!\(decide \(required ∈ known\)\)/u.test(newRequired)) {
    failures.push('finite-deduplicated-frontier');
  }
  if (!/processed := dependent :: processed[\s\S]*pending := remaining \+\+ newlyRequired/u.test(work)) {
    failures.push('work-list-transition');
  }
  if (!/allTerminalPrimitiveRecords inputs gates outputs profileWidth\)\.length[\s\S]*terminalSaturationInitialState seed/u.test(finalState)) {
    failures.push('finite-universe-fuel');
  }
  if (!/terminalSaturationFinalState system seed\)\.processed/u.test(output)) {
    failures.push('processed-output');
  }
  if (!/terminalSaturateRecords_sound[\s\S]*terminalSaturate_least[\s\S]*terminalSaturateRecords_extensive[\s\S]*terminalSaturateRecords_closed/u.test(exact)) {
    failures.push('exact-inductive-equivalence');
  }
  return [...new Set(failures)];
}

function validatePhysical0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalExecutableSaturation',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PHYSICAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PHYSICAL_PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const wire = declarationBlock0(source, 'TerminalSupportWire');
  const sourceWire = declarationBlock0(source, 'Source.terminalSupportWire?');
  const gateSources = declarationBlock0(source, 'Program.terminalGateSources');
  const boundary = declarationBlock0(source, 'terminalBoundaryWire');
  const interfaceGate = declarationBlock0(source, 'terminalInterfaceGate');
  const boundaryPorts = declarationBlock0(source, 'terminalBoundaryPorts');
  const interfacePorts = declarationBlock0(source, 'terminalInterfacePorts');
  const compatible = declarationBlock0(
    source,
    'completeTerminalPhysicalSupport_compatible',
  );
  const combined = declarationBlock0(source, 'completeSaturatedTerminalPhysicalSupport');
  const combinedCompatible = declarationBlock0(
    source,
    'completeSaturatedTerminalPhysicalSupport_compatible',
  );
  if (!/\| input \(index : Fin inputs\)[\s\S]*\| gate \(index : Fin gates\)/u.test(wire)) {
    failures.push('physical-wire-universe');
  }
  if (!/\| \.input index => some \(\.input index\)[\s\S]*\| \.constant _value => none[\s\S]*\| \.gate index => some \(\.gate index\)/u.test(sourceWire)) {
    failures.push('constant-locality');
  }
  if (!/Program inputs gates → Fin gates →[\s\S]*Source inputs gates × Source inputs gates[\s\S]*terminalGateSources initial/u.test(gateSources)) {
    failures.push('actual-program-source-lookup');
  }
  if (!/terminalWireExternal records wire &&[\s\S]*terminalGateSelected records consumer &&[\s\S]*program\.terminalGateUsesWire consumer wire/u.test(boundary)) {
    failures.push('exact-incoming-crossing');
  }
  if (!/terminalGateSelected records producer &&[\s\S]*terminalGateHasExternalConsumer[\s\S]*terminalGateIsGlobalOutput/u.test(interfaceGate)) {
    failures.push('exact-outgoing-crossing');
  }
  if (!/allTerminalSupportWires inputs gates\)\.filter[\s\S]*terminalBoundaryWire/u.test(boundaryPorts)
      || !/allFin gates\)\.filter \(terminalInterfaceGate/u.test(interfacePorts)) {
    failures.push('canonical-port-order');
  }
  if (!/completeTerminalPhysicalSupport_incoming_complete[\s\S]*completeTerminalPhysicalSupport_outgoing_complete/u.test(compatible)) {
    failures.push('universal-compatibility');
  }
  if (!/completeTerminalPhysicalSupport candidate[\s\S]*terminalSaturateRecords system seed/u.test(combined)
      || !/completeTerminalPhysicalSupport_compatible candidate[\s\S]*terminalSaturateRecords system seed/u.test(combinedCompatible)) {
    failures.push('saturated-composition');
  }
  return [...new Set(failures)];
}

test('executable saturation exposes one exact finite work-list interface', async () => {
  assert.deepEqual(validateExecutable0(await text0(EXECUTABLE_PATH)), []);
});

test('physical completion derives exact ports from the actual candidate', async () => {
  assert.deepEqual(validatePhysical0(await text0(PHYSICAL_PATH)), []);
});

test('axiom transcript covers all 40 public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, 40);
  assert.equal(PUBLIC_DECLARATIONS.length, 40);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualTerminalExecutableSaturation$/mu);
  assert.match(root, /^import PNP\.ResidualTerminalPhysicalSupportCompletion$/mu);
});

test('compiled closure is approved for every executable and physical declaration', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of PUBLIC_DECLARATIONS) {
    const row = rows.get(name);
    assert.ok(row, name);
    for (const axiom of row.axioms) assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
  }
});

test('regression covers normalization, cycles, exact crossings, and composition', async () => {
  const regression = stripLeanCommentsAndStrings0(await text0(REGRESSION_PATH));
  for (const token of [
    'allTerminalSaturationRuleKinds.length = 10',
    'terminalSaturateRecords physicalSupportSaturationSystem [] = []',
    '[physicalSupportGate2Record, physicalSupportGate1Record,',
    'physicalSupportGate0Record ∉',
    'mem_terminalSaturateRecords_iff',
    'terminalBoundaryPorts physicalSupportProgram physicalSupportGate1Only',
    'terminalInterfacePorts physicalSupportCandidate physicalSupportGate1Only',
    'physicalSupportAllGates',
    'completeSaturatedTerminalPhysicalSupport',
    'completeSaturatedTerminalPhysicalSupport_compatible',
    'physicalSupportCycleSystem',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(regression, /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('status earns only executable physical completion and preserves open blockers', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualTerminalExecutableSaturationFormalized',
    'leanResidualTerminalPhysicalSupportCompletionFormalized',
    'leanResidualTerminalPhysicalBoundaryFormalized',
    'leanResidualTerminalPhysicalInterfaceFormalized',
    'leanResidualTerminalPhysicalCompatibilityFormalized',
    'leanResidualTerminalPhysicalSupportCompletionAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalPhysicalSupportCompletionScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-finite-seed-lists',
  );
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  for (const field of [
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalProjectionSquareFormalized',
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-physical-support-completion',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the manuscript anchor and the exact remaining boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§2', '§3', '(U, ∂U, ιU)', 'finite work list', 'actual direct-wire program',
    'constants', 'no crossing wire is omitted', 'profile frontier',
    'proper positive support', 'square legitimacy', 'SaturatePositive',
    'ZeroSlack', 'polynomial runtime', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-physical-support-completion0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalPhysicalSupportCompletionAxiomAudit\.lean[\s\S]{0,1800}-eq 40/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalPhysicalSupportCompletion\.lean/u);
});

test('hostile executable mutations revoke milestone credit', async () => {
  const source = await text0(EXECUTABLE_PATH);
  assert.equal(validateExecutable0(source.replace('    .prefixTail, ', '    ')).includes('ten-rule-schedule'), true);
  assert.equal(validateExecutable0(source.replace(
    '(allTerminalPrimitiveRecords inputs gates outputs profileWidth).length',
    '0',
  )).includes('finite-universe-fuel'), true);
  assert.equal(validateExecutable0(source.replace(
    'terminalSaturationEdge system dependent required &&\n        !(decide (required ∈ known))',
    'terminalSaturationEdge system dependent required',
  )).includes('finite-deduplicated-frontier'), true);
  assert.equal(validateExecutable0(source.replace(
    '(terminalSaturationFinalState system seed).processed',
    '(terminalSaturationFinalState system seed).pending',
  )).includes('processed-output'), true);
  assert.equal(validateExecutable0(source.replace(
    'terminalSaturateRecords_sound system seed record',
    'terminalSaturateRecords_extensive system seed record',
  )).includes('exact-inductive-equivalence'), true);
  assert.equal(validateExecutable0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateExecutable0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateExecutable0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-helper-surface'), true);
  assert.equal(validateExecutable0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateExecutable0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateExecutable0(`${source}\ndef callerCertificate := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateExecutable0(`${source}\ntheorem properSupport : True := True.intro\n`).includes('overclaim'), true);
  assert.equal(validateExecutable0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});

test('hostile physical mutations revoke milestone credit', async () => {
  const source = await text0(PHYSICAL_PATH);
  assert.equal(validatePhysical0(source.replace(
    '  | .constant _value => none\n',
    '',
  )).includes('constant-locality'), true);
  assert.equal(validatePhysical0(source.replace(
    '  terminalWireExternal records wire &&\n',
    '',
  )).includes('exact-incoming-crossing'), true);
  assert.equal(validatePhysical0(source.replace(
    '  terminalGateSelected records producer &&\n',
    '',
  )).includes('exact-outgoing-crossing'), true);
  assert.equal(validatePhysical0(source.replace(
    '(allTerminalSupportWires inputs gates).filter',
    '([]).filter',
  )).includes('canonical-port-order'), true);
  assert.equal(validatePhysical0(source.replace(
    '(terminalSaturateRecords system seed)',
    'seed',
  )).includes('saturated-composition'), true);
  assert.equal(validatePhysical0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validatePhysical0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validatePhysical0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-helper-surface'), true);
  assert.equal(validatePhysical0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validatePhysical0(`${source}\ntheorem hidden : True := by bv_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validatePhysical0(`${source}\ndef hostLookup := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validatePhysical0(`${source}\ntheorem squareLegitimate : True := True.intro\n`).includes('overclaim'), true);
  assert.equal(validatePhysical0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
