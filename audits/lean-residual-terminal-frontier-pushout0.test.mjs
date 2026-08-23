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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalFrontierPushout.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalFrontierPushoutAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalFrontierPushout.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_frontier_pushout.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalFrontierDisposition',
  'allTerminalSupportWires_nodup',
  'terminalBoundaryFrontierPushout',
  'terminalInterfaceFrontierPushout',
  'terminalProfileFrontierPushout',
  'terminalGovernedFrontierPushout',
  'TerminalGovernedFrontier.extensionality',
  'mem_terminalBoundaryFrontierPushout_iff',
  'mem_terminalInterfaceFrontierPushout_iff',
  'mem_terminalProfileFrontierPushout_iff',
  'terminalBoundaryFrontierPushout_nodup',
  'terminalInterfaceFrontierPushout_nodup',
  'terminalProfileFrontierPushout_nodup',
  'terminalBoundaryFrontierDisposition',
  'terminalInterfaceFrontierDisposition',
  'TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout',
  'TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout',
  'TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff',
  'TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff',
  'TerminalSaturatedSupportSquare.governedCompleted_join_profile_eq_pushout',
  'TerminalSaturatedSupportSquare.side_profile_mem_join',
  'TerminalSaturatedSupportSquare.left_boundary_disposition',
  'TerminalSaturatedSupportSquare.right_boundary_disposition',
  'TerminalSaturatedSupportSquare.side_interface_disposition',
  'TerminalSaturatedSupportSquare.governed_frontier_pushout',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.mem_allTerminalSupportWires`,
  `${NAMESPACE}.mem_allFin`,
  `${NAMESPACE}.terminalGateSelected_eq_true_iff`,
  `${NAMESPACE}.terminalWireExternal_eq_true_iff`,
  `${NAMESPACE}.terminalBoundaryWire_eq_true_iff`,
  `${NAMESPACE}.terminalGateHasExternalConsumer_eq_true_iff`,
  `${NAMESPACE}.terminalInterfaceGate_eq_true_iff`,
  `${NAMESPACE}.mem_terminalBoundaryPorts_iff`,
  `${NAMESPACE}.mem_terminalInterfacePorts_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.mem_meetRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.mem_joinRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.records_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.physically_compatible`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_profile_iff`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...PUBLIC_DECLARATIONS.filter((name) => [
    'allTerminalSupportWires_nodup',
    'TerminalGovernedFrontier.extensionality',
    'mem_terminalBoundaryFrontierPushout_iff',
    'mem_terminalInterfaceFrontierPushout_iff',
    'mem_terminalProfileFrontierPushout_iff',
    'terminalBoundaryFrontierPushout_nodup',
    'terminalInterfaceFrontierPushout_nodup',
    'terminalProfileFrontierPushout_nodup',
    'TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout',
    'TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout',
    'TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff',
    'TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff',
    'TerminalSaturatedSupportSquare.governedCompleted_join_profile_eq_pushout',
    'TerminalSaturatedSupportSquare.side_profile_mem_join',
    'TerminalSaturatedSupportSquare.left_boundary_disposition',
    'TerminalSaturatedSupportSquare.right_boundary_disposition',
    'TerminalSaturatedSupportSquare.side_interface_disposition',
    'TerminalSaturatedSupportSquare.governed_frontier_pushout',
  ].some((local) => name === `${NAMESPACE}.${local}`)),
  `${NAMESPACE}.terminalGateSelected_eq_true_iff`,
  `${NAMESPACE}.terminalWireExternal_eq_true_iff`,
  `${NAMESPACE}.terminalBoundaryWire_eq_true_iff`,
  `${NAMESPACE}.terminalGateHasExternalConsumer_eq_true_iff`,
  `${NAMESPACE}.terminalInterfaceGate_eq_true_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.mem_meetRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.mem_joinRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.records_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.physically_compatible`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_profile_iff`,
]);

const PRIVATE_HELPERS = Object.freeze([
  'nodup_of_listNoDuplicates',
  'nodup_map_injective',
  'terminalGateSelected_append_true_iff',
  'bool_not_eq_false_implies_true',
  'terminalGateSelected_left_false_of_append_false',
  'terminalGateSelected_right_false_of_append_false',
  'terminalWireExternal_left_of_append',
  'terminalWireExternal_right_of_append',
  'terminalBoundaryPorts_append_iff',
  'terminalGateHasExternalConsumer_left_of_append',
  'terminalGateHasExternalConsumer_right_of_append',
  'terminalInterfacePorts_append_iff',
  'terminalGateSelected_function_congr',
  'terminalBoundaryPorts_congr',
  'terminalInterfacePorts_congr',
  'terminalBoundaryFrontierPushout_eq_ports_append',
  'terminalInterfaceFrontierPushout_eq_ports_append',
  'squareJoin_append_same_gates',
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
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|frontierCertificate|pushoutCertificate|compatibilityCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|projectionCompatibleSquare|squareLegitimate|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialFrontierPushout)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalGovernedSupportCompletion',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const boundary = declarationBlock0(source, 'terminalBoundaryFrontierPushout');
  const interfaceFrontier = declarationBlock0(
    source,
    'terminalInterfaceFrontierPushout',
  );
  const profiles = declarationBlock0(source, 'terminalProfileFrontierPushout');
  const governed = declarationBlock0(source, 'terminalGovernedFrontierPushout');
  const joinBoundary = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout',
  );
  const joinInterface = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout',
  );
  const meetProfiles = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff',
  );
  const joinProfiles = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff',
  );
  const leftDisposition = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.left_boundary_disposition',
  );
  const rightDisposition = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.right_boundary_disposition',
  );
  const interfaceDisposition = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.side_interface_disposition',
  );
  const main = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governed_frontier_pushout',
  );

  if (!/allTerminalSupportWires inputs gates\)\.filter/u.test(boundary)
      || !/wire ∈ left\.frontier\.boundary ∨ wire ∈ right\.frontier\.boundary/u.test(boundary)
      || !/terminalWireExternal \(left\.records \+\+ right\.records\) wire = true/u.test(boundary)) {
    failures.push('canonical-boundary-gluing');
  }
  if (!/allFin gates\)\.filter/u.test(interfaceFrontier)
      || !/producer ∈ left\.frontier\.interface ∨[\s\S]*producer ∈ right\.frontier\.interface/u.test(interfaceFrontier)
      || !/terminalGateHasExternalConsumer candidate\.program[\s\S]*left\.records \+\+ right\.records/u.test(interfaceFrontier)
      || !/terminalGateIsGlobalOutput candidate\.directWireWord producer = true/u.test(interfaceFrontier)) {
    failures.push('canonical-interface-gluing');
  }
  if (!/allFin profileWidth\)\.filter/u.test(profiles)
      || !/coordinate ∈ left\.profileCoordinates role ∨[\s\S]*coordinate ∈ right\.profileCoordinates role/u.test(profiles)) {
    failures.push('role-preserving-profile-gluing');
  }
  if (!/boundary := terminalBoundaryFrontierPushout left right/u.test(governed)
      || !/interface := terminalInterfaceFrontierPushout left right/u.test(governed)
      || !/profiles := terminalProfileFrontierPushout left right/u.test(governed)) {
    failures.push('combined-frontier-gluing');
  }
  if (!/governedCompleted candidate \.join\)\.frontier\.boundary =/u.test(joinBoundary)
      || !/=\s*terminalBoundaryFrontierPushout\s/u.test(joinBoundary)) {
    failures.push('join-boundary-law');
  }
  if (!/governedCompleted candidate \.join\)\.frontier\.interface =/u.test(joinInterface)
      || !/=\s*terminalInterfaceFrontierPushout\s/u.test(joinInterface)) {
    failures.push('join-interface-law');
  }
  if (!/governedCompleted candidate \.meet\)\.profileCoordinates role/u.test(meetProfiles)
      || !/governedCompleted candidate \.left\)\.profileCoordinates role ∧/u.test(meetProfiles)
      || !/governedCompleted candidate \.right\)\.profileCoordinates role/u.test(meetProfiles)) {
    failures.push('meet-profile-intersection');
  }
  if (!/governedCompleted candidate \.join\)\.profileCoordinates role/u.test(joinProfiles)
      || !/governedCompleted candidate \.left\)\.profileCoordinates role ∨/u.test(joinProfiles)
      || !/governedCompleted candidate \.right\)\.profileCoordinates role/u.test(joinProfiles)) {
    failures.push('join-profile-union');
  }
  if (!/\.internalized[\s\S]*terminalGateSelected square\.rightRecords gate = true/u.test(leftDisposition)
      || !/\.internalized[\s\S]*terminalGateSelected square\.leftRecords gate = true/u.test(rightDisposition)) {
    failures.push('opposite-side-boundary-internalization');
  }
  if (!/\.internalized[\s\S]*terminalGateHasExternalConsumer candidate\.program[\s\S]*= false[\s\S]*terminalGateIsGlobalOutput candidate\.directWireWord producer = false/u.test(interfaceDisposition)) {
    failures.push('interface-internalization');
  }
  if (!/terminalGovernedFrontierPushout/u.test(main)
      || !/governedCompleted candidate \.meet\)\.profileCoordinates role ↔/u.test(main)
      || !/\.governedCompleted_join_boundary_eq_pushout/u.test(main)
      || !/\.governedCompleted_join_interface_eq_pushout/u.test(main)
      || !/\.governedCompleted_meet_profile_iff/u.test(main)) {
    failures.push('legacy-frontier-pushout-law');
  }
  if (/\b(?:fixedWire|fixedGate|fixedProfile|startCoordinate|endCoordinate|profileOffset)\b/u.test(stripped)) {
    failures.push('hard-coded-frontier');
  }
  return [...new Set(failures)];
}

test('frontier pushout has one computed all-finite interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith('import PNP.ResidualTerminalFrontierPushout\n'), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 39);
  assert.equal(PUBLIC_DECLARATIONS.length, 25);
  assert.equal(REUSED_DECLARATIONS.length, 14);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalFrontierPushout$/mu);
});

test('compiled closure is approved for every frontier-pushout declaration', async () => {
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
});

test('regression covers gluing, internalization, overlap, emptiness, and output retention', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'pushoutSquare',
    'pushoutEmptySquare',
    'pushoutGlobalSquare',
    'terminalBoundaryFrontierPushout',
    'terminalInterfaceFrontierPushout',
    'terminalProfileFrontierPushout',
    'terminalGovernedFrontierPushout',
    'governed_frontier_pushout',
    'left_boundary_disposition',
    'right_boundary_disposition',
    'side_interface_disposition',
    '.internalized',
    '.retained',
    'pushoutProfile0',
    'pushoutProfile1',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact pushout boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-governed-frontier-pushout',
  );
  assert.equal(milestone?.classification,
    'formalized-terminal-governed-frontier-pushout');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite direct-wire candidate/u);
  assert.match(milestone.scope, /computed saturated support square/u);
  assert.match(milestone.nonClaim, /projection compatibility/u);
  assert.match(milestone.nonClaim, /SaturatePositive/u);
  assert.match(docs, /Governed terminal frontier pushout/u);
  assert.match(docs, /not.*SaturatePositive/isu);
});

test('status earns frontier pushout without downstream overclaim', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalFrontierPushoutFormalized',
    'leanResidualTerminalFrontierBoundaryGlueExactFormalized',
    'leanResidualTerminalFrontierInterfaceGlueExactFormalized',
    'leanResidualTerminalFrontierProfileGlueExactFormalized',
    'leanResidualTerminalFrontierInternalizationFormalized',
    'leanResidualTerminalFrontierPushoutAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalFrontierPushoutScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-computed-saturated-support-squares',
  );
  for (const field of [
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 3);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-governed-frontier-pushout',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy equation and remaining proof boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§3',
    'Front_{A∨B}',
    'Front_A',
    'Front_{A∧B}',
    'Front_B',
    'all finite',
    'internalized',
    'projection compatibility',
    'BN2 square legitimacy',
    'SaturatePositive',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-frontier-pushout0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFrontierPushoutAxiomAudit\.lean[\s\S]{0,1800}-eq 39/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFrontierPushout\.lean/u);
});

test('hostile source mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [
      source.replace('(allTerminalSupportWires inputs gates).filter',
        'fixedWire.filter'),
      'canonical-boundary-gluing',
    ],
    [
      source.replace('(allFin gates).filter', 'fixedGate.filter'),
      'canonical-interface-gluing',
    ],
    [
      source.replace('(allFin profileWidth).filter', 'fixedProfile.filter'),
      'role-preserving-profile-gluing',
    ],
    [
      source.replace('profiles := terminalProfileFrontierPushout left right',
        'profiles := left.profileCoordinates'),
      'combined-frontier-gluing',
    ],
    [
      source.replace(
        'frontier.boundary =\n      terminalBoundaryFrontierPushout',
        'frontier.boundary =\n      (square.governedCompleted candidate .left).frontier.boundary ++'),
      'join-boundary-law',
    ],
    [
      source.replace(
        'profileCoordinates role ∧\n        coordinate ∈ (square.governedCompleted candidate .right).profileCoordinates role',
        'profileCoordinates role ∧\n        True'),
      'meet-profile-intersection',
    ],
    [
      source.replace('terminalGateSelected square.rightRecords gate = true',
        'terminalGateSelected square.leftRecords gate = true'),
      'opposite-side-boundary-internalization',
    ],
    [
      source.replace(
        'terminalGateIsGlobalOutput candidate.directWireWord producer = false',
        'True'),
      'interface-internalization',
    ],
    [`${source}\naxiom frontierShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef projectionCompatibleSquare : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`, 'project-axiom'],
    [`${source}\ndef callerCertificate := true\n`, 'caller-or-host-certificate'],
    [`${source}\ntheorem shortcut : True := by native_decide\n`, 'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`, 'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`, 'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
