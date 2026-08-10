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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalSupportExtraction.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalSupportExtractionAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalSupportExtraction.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_support_extraction.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  'terminalSelectedGateIndices',
  'terminalSelectedGates',
  'mem_terminalSelectedGateIndices_iff',
  'mem_terminalSelectedGates_iff',
  'terminalSelectedGateIndices_nodup',
  'terminalSelectedGates_nodup',
  'TerminalExtractedSupport',
  'extractTerminalSupport',
  'extractTerminalSupport_records',
  'extractTerminalSupport_boundary',
  'extractTerminalSupport_selectedGates',
  'extractTerminalSupport_interface',
  'extractTerminalSupport_gateCount',
  'terminalOpenGateEvaluation',
  'terminalOpenSupportSemantics',
  'TerminalSupportWire.candidateValue',
  'terminalInducedBoundaryValuation',
  'terminalOpenGateEvaluation_induced_selected',
  'terminalOpenSupportSemantics_induced',
  'extractTerminalSupport_semantics',
  'extractTerminalSupport_induced',
  'extractSaturatedTerminalSupport',
  'extractSaturatedTerminalSupport_records',
  'extractSaturatedTerminalSupport_gateCount',
  'extractSaturatedTerminalSupport_semantics',
  'extractSaturatedTerminalSupport_induced',
].map((name) => `${NAMESPACE}.${name}`));

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.terminalSaturateRecords`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.terminalGateSelected`,
  `${NAMESPACE}.terminalBoundaryPorts`,
  `${NAMESPACE}.terminalInterfacePorts`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_incoming_complete`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_compatible`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.mem_terminalSelectedGateIndices_iff`,
  `${NAMESPACE}.mem_terminalSelectedGates_iff`,
  `${NAMESPACE}.terminalSelectedGateIndices_nodup`,
  `${NAMESPACE}.terminalSelectedGates_nodup`,
  `${NAMESPACE}.extractTerminalSupport_records`,
  `${NAMESPACE}.extractTerminalSupport_boundary`,
  `${NAMESPACE}.extractTerminalSupport_selectedGates`,
  `${NAMESPACE}.extractTerminalSupport_interface`,
  `${NAMESPACE}.extractTerminalSupport_gateCount`,
  `${NAMESPACE}.terminalOpenGateEvaluation_induced_selected`,
  `${NAMESPACE}.terminalOpenSupportSemantics_induced`,
  `${NAMESPACE}.extractTerminalSupport_semantics`,
  `${NAMESPACE}.extractTerminalSupport_induced`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_records`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_gateCount`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_semantics`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_induced`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_incoming_complete`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_compatible`,
]);

const PRIVATE_HELPERS = Object.freeze([
  'locateMember',
  'memberIndex',
  'get_memberIndex',
  'bool_eq_false_of_ne_true',
  'terminalBoundaryValue',
  'mem_map_finCastSucc_iff',
  'finLast_not_mem_map_castSucc',
  'finCastSucc_ne_last',
  'finLastCasesConstructive',
  'finLastCasesConstructive_castSucc',
  'finLastCasesConstructive_last',
  'nodup_map_injective',
  'Source.evalTerminalOpen',
  'Program.evalTerminalOpenAux',
  'Program.evalTerminalOpenAux_snoc_castSucc',
  'Source.terminalAccounted',
  'Program.terminalSourcesAccounted',
  'Source.terminalAccounted_weaken_one_iff',
  'Program.terminalGateSources_snoc_castSucc',
  'Program.terminalGateSources_snoc_last',
  'Program.terminalSourcesAccounted_of_random_access',
  'Source.evalTerminalOpen_eq_of_accounted',
  'Program.evalTerminalOpenAux_eq_program',
  'TerminalExtractionState',
  'boundaryInputSource',
  'boundaryInputSource_eval',
  'Source.extractTerminal',
  'Source.extractTerminal_eval',
  'extractTerminalProgramAux',
  'terminalExtractionState',
  'terminalInterfaceGet_selected',
  'terminalExtractedCandidate',
  'terminalBoundaryValue_induced_of_mem',
  'physicalSourceAccounted_iff_terminalAccounted',
  'physicalTerminalSourcesAccounted',
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
    /^private\s+(?:noncomputable\s+)?(?:def|theorem|inductive|structure|abbrev)\s+([^\s({:]+)/gmu,
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
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|dependencyCertificate|saturationCertificate|closureCertificate|reindexCertificate|boundaryCertificate)\b/u.test(stripped)) {
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

function validateSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPhysicalSupportCompletion',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const selected = declarationBlock0(source, 'terminalSelectedGates');
  const state = source.slice(
    source.indexOf('private structure TerminalExtractionState'),
    source.indexOf('/-- Extracted direct-wire support with exact computed dimensions.'),
  );
  const sourceExtraction = source.slice(
    source.indexOf('private def Source.extractTerminal'),
    source.indexOf('private theorem Source.extractTerminal_eval'),
  );
  const output = source.slice(
    source.indexOf('private def terminalExtractedCandidate'),
    source.indexOf('/-- Construct the extracted support solely'),
  );
  const concreteState = source.slice(
    source.indexOf('private def terminalExtractionState'),
    source.indexOf('private theorem terminalInterfaceGet_selected'),
  );
  const support = declarationBlock0(source, 'extractTerminalSupport');
  const openSemantics = declarationBlock0(source, 'terminalOpenSupportSemantics');
  const semantics = declarationBlock0(source, 'extractTerminalSupport_semantics');
  const inducedGate = declarationBlock0(
    source,
    'terminalOpenGateEvaluation_induced_selected',
  );
  const induced = declarationBlock0(source, 'extractTerminalSupport_induced');
  const saturated = declarationBlock0(source, 'extractSaturatedTerminalSupport');
  const saturatedSemantics = declarationBlock0(
    source,
    'extractSaturatedTerminalSupport_semantics',
  );

  if (!/terminalSelectedGateIndices \(terminalGateSelected records\)/u.test(selected)) {
    failures.push('canonical-selected-gates');
  }
  if (!/extractTerminalProgramAux[\s\S]*terminalBoundaryPorts candidate\.program records[\s\S]*candidate\.program[\s\S]*terminalGateSelected records/u.test(concreteState)) {
    failures.push('exact-physical-boundary');
  }
  if (!/\| \.input index => boundaryInputSource boundary \(inputWire index\)[\s\S]*\| \.constant value => \.constant value[\s\S]*\| \.gate index =>[\s\S]*if selectedGate[\s\S]*\.gate \(state\.gateIndex index selectedGate\)[\s\S]*else boundaryInputSource boundary \(gateWire index\)/u.test(sourceExtraction)) {
    failures.push('exact-source-partition');
  }
  if (!/extractTerminalProgramAux boundary initial earlierSelected[\s\S]*extractedProgram := \.snoc earlier\.extractedProgram[\s\S]*gate\.left\.extractTerminal earlier[\s\S]*gate\.right\.extractTerminal earlier/u.test(state)) {
    failures.push('all-gate-structural-scan');
  }
  if (!/gateCount_eq := by[\s\S]*terminalSelectedGateIndices[\s\S]*earlier\.gateCount_eq/u.test(state)) {
    failures.push('exact-selected-gate-count');
  }
  if (!/interface\.get output[\s\S]*terminalGateSelected records producer[\s\S]*\.gate \(state\.gateIndex producer selected\)/u.test(output)) {
    failures.push('ordered-interface-reindex');
  }
  if (!/records := records[\s\S]*boundary := terminalBoundaryPorts[\s\S]*selectedGates := terminalSelectedGates[\s\S]*interface := interface/u.test(support)) {
    failures.push('exact-extracted-fields');
  }
  if (!/terminalOpenGateEvaluation candidate records boundaryValuation[\s\S]*terminalInterfacePorts candidate records/u.test(openSemantics)) {
    failures.push('independent-open-semantics');
  }
  if (!/state\.correct boundaryValuation[\s\S]*terminalInterfacePorts candidate records/u.test(semantics)) {
    failures.push('universal-semantic-equality');
  }
  if (!/completeTerminalPhysicalSupport_incoming_complete/u.test(source)
      || !/Program\.evalTerminalOpenAux_eq_program/u.test(inducedGate)
      || !/physicalTerminalSourcesAccounted/u.test(inducedGate)
      || !/terminalInducedBoundaryValuation/u.test(inducedGate)) {
    failures.push('whole-circuit-boundary-recovery');
  }
  if (!/extractTerminalSupport_semantics[\s\S]*terminalOpenSupportSemantics_induced/u.test(induced)) {
    failures.push('induced-interface-recovery');
  }
  if (!/extractTerminalSupport candidate \(terminalSaturateRecords system seed\)/u.test(saturated)
      || !/extractTerminalSupport_semantics candidate[\s\S]*terminalSaturateRecords system seed/u.test(saturatedSemantics)) {
    failures.push('saturated-extraction-composition');
  }
  if (/\b(?:startGate|endGate|gateOffset|selectedInterval|coordinateTable)\b/u.test(stripLeanCommentsAndStrings0(source))) {
    failures.push('hard-coded-support-interval');
  }
  return [...new Set(failures)];
}

test('arbitrary terminal extraction has one closed executable interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 26 new and eight reused declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 34);
  assert.equal(PUBLIC_DECLARATIONS.length, 26);
  assert.equal(REUSED_DECLARATIONS.length, 8);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualTerminalSupportExtraction$/mu);
});

test('compiled closure is approved for every extraction declaration', async () => {
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
  }
});

test('regression covers empty, singleton, noncontiguous, full, exact semantics, and saturation', async () => {
  const regression = stripLeanCommentsAndStrings0(await text0(REGRESSION_PATH));
  for (const token of [
    'terminalSelectedGates ([] : List extractionRecord) = []',
    'terminalSelectedGates [extractionGate2Record] = [extractionGate2]',
    '[extractionGate0, extractionGate2]',
    '[.input extractionInput0, .gate extractionGate1]',
    '[extractionGate0, extractionGate2]',
    ').gateCount = 0',
    ').gateCount = 4',
    '.constant true',
    '.gate ⟨0, by decide⟩, .input ⟨1, by decide⟩',
    'extractionBoundary00',
    'extractionBoundary01',
    'extractionBoundary10',
    'extractionBoundary11',
    'extractTerminalSupport_semantics',
    'terminalSaturateRecords extractionSaturationSystem',
    'extractSaturatedTerminalSupport_induced',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(regression, /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('status earns extraction while preserving every downstream blocker', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualTerminalSupportExtractionFormalized',
    'leanResidualTerminalOpenSemanticsFormalized',
    'leanResidualTerminalInducedRecoveryFormalized',
    'leanResidualTerminalSupportExtractionAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalSupportExtractionScope,
    'all-finite-direct-wire-candidates-terminal-record-lists-boundary-valuations-and-interface-coordinates',
  );
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  for (const field of [
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-support-extraction',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the manuscript theorem and exact remaining boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§2.2', '(L_U, W_U) = Extract(C, U)', '[[W_U]] = F_{C,U}',
    'arbitrary finite', 'noncontiguous', 'incoming boundary',
    'outgoing interface', 'constants stay local', 'whole-circuit execution',
    'proper positive support', 'square legitimacy', 'SaturatePositive',
    'ZeroSlack', 'polynomial runtime', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-support-extraction0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalSupportExtractionAxiomAudit\.lean[\s\S]{0,1800}-eq 34/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalSupportExtraction\.lean/u);
});

test('hostile extraction mutations revoke milestone credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(source.replace(
    'terminalSelectedGateIndices (terminalGateSelected records)',
    '[]',
  )).includes('canonical-selected-gates'), true);
  assert.equal(validateSource0(source.replace(
    'terminalBoundaryPorts candidate.program records',
    '[]',
  )).includes('exact-physical-boundary'), true);
  assert.equal(validateSource0(source.replace(
    '| .constant value => .constant value',
    '| .constant value => boundaryInputSource boundary (inputWire (Fin.last _)) state.gateCount',
  )).includes('exact-source-partition'), true);
  assert.equal(validateSource0(source.replace(
    '.gate (state.gateIndex index selectedGate)',
    'boundaryInputSource boundary (gateWire index) state.gateCount',
  )).includes('exact-source-partition'), true);
  assert.equal(validateSource0(source.replace(
    'else boundaryInputSource boundary (gateWire index) state.gateCount',
    'else .constant false',
  )).includes('exact-source-partition'), true);
  assert.equal(validateSource0(source.replace(
    '.gate (state.gateIndex producer selected)',
    '.constant false',
  )).includes('ordered-interface-reindex'), true);
  assert.equal(validateSource0(source.replaceAll(
    'state.correct boundaryValuation',
    'by exact False.elim (by contradiction)',
  )).includes('universal-semantic-equality'), true);
  assert.equal(validateSource0(source.replace(
    'extractTerminalSupport candidate (terminalSaturateRecords system seed)',
    'extractTerminalSupport candidate seed',
  )).includes('saturated-extraction-composition'), true);
  assert.equal(validateSource0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateSource0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-helper-surface'), true);
  assert.equal(validateSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(`${source}\ndef callerCertificate := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateSource0(`${source}\ndef startGate := 0\n`).includes('hard-coded-support-interval'), true);
  assert.equal(validateSource0(`${source}\ntheorem squareLegitimate : True := True.intro\n`).includes('overclaim'), true);
  assert.equal(validateSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
