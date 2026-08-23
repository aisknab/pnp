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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalGovernedSupportCompletion.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalGovernedSupportCompletionAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalGovernedSupportCompletion.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_governed_support_completion.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'allTerminalProfileRoles',
  'mem_allTerminalProfileRoles',
  'terminalProfileCoordinatesForRole',
  'mem_terminalProfileCoordinatesForRole_iff',
  'terminalProfileCoordinatesForRole_nodup',
  'TerminalGovernedFrontier',
  'TerminalGovernedCompletedSupport',
  'completeTerminalGovernedSupport',
  'TerminalGovernedCompletedSupport.physical',
  'TerminalGovernedCompletedSupport.profileCoordinates',
  'TerminalGovernedCompletedSupport.frontier',
  'TerminalGovernedCompletedSupport.Governed',
  'TerminalGovernedCompletedSupport.Compatible',
  'completeTerminalGovernedSupport_records',
  'TerminalGovernedCompletedSupport.frontier_boundary',
  'TerminalGovernedCompletedSupport.frontier_interface',
  'TerminalGovernedCompletedSupport.mem_profileCoordinates_iff',
  'TerminalGovernedCompletedSupport.profileCoordinates_nodup',
  'TerminalGovernedCompletedSupport.mem_own_profile_role_iff',
  'TerminalGovernedCompletedSupport.profile_role_unique',
  'TerminalGovernedCompletedSupport.profileCoordinates_disjoint',
  'TerminalGovernedCompletedSupport.profile_record_covered_iff',
  'TerminalGovernedCompletedSupport.required_mem',
  'TerminalGovernedCompletedSupport.required_profile_mem',
  'completeSaturatedTerminalGovernedSupport',
  'completeSaturatedTerminalGovernedSupport_records',
  'completeSaturatedTerminalGovernedSupport_compatible',
  'TerminalSaturatedSupportSquare.governedCompleted',
  'TerminalSaturatedSupportSquare.governedCompleted_records',
  'TerminalSaturatedSupportSquare.governedCompleted_compatible',
  'TerminalSaturatedSupportSquare.governedCompleted_profile_iff',
  'TerminalSaturatedSupportSquare.governedCompleted_required_mem',
  'TerminalSaturatedSupportSquare.governedCompleted_required_profile_mem',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.allFin_noDuplicates`,
  `${NAMESPACE}.mem_allFin`,
  `${NAMESPACE}.completeTerminalPhysicalSupport`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.terminalSaturateRecords`,
  `${NAMESPACE}.terminalSaturateRecords_closed`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.records_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.physically_compatible`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.mem_allTerminalProfileRoles`,
  `${NAMESPACE}.mem_terminalProfileCoordinatesForRole_iff`,
  `${NAMESPACE}.terminalProfileCoordinatesForRole_nodup`,
  `${NAMESPACE}.completeTerminalGovernedSupport_records`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.frontier_boundary`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.frontier_interface`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.mem_profileCoordinates_iff`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.profileCoordinates_nodup`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.mem_own_profile_role_iff`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.profile_role_unique`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.profileCoordinates_disjoint`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.profile_record_covered_iff`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.required_mem`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.required_profile_mem`,
  `${NAMESPACE}.completeSaturatedTerminalGovernedSupport_records`,
  `${NAMESPACE}.completeSaturatedTerminalGovernedSupport_compatible`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_records`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_compatible`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_required_mem`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_required_profile_mem`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.terminalSaturateRecords_closed`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.records_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.physically_compatible`,
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
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|completionCertificate|frontierCertificate|governanceCertificate|compatibilityCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|frontierPushout|projectionCompatibleSquare|squareLegitimate|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialSupportCompletion)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalSupportSquareClosure',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify([
    'nodup_of_listNoDuplicates',
  ])) failures.push('private-helper-surface');

  const roles = declarationBlock0(source, 'allTerminalProfileRoles');
  const roleCoordinates = declarationBlock0(source, 'terminalProfileCoordinatesForRole');
  const physical = declarationBlock0(
    source,
    'TerminalGovernedCompletedSupport.physical',
  );
  const frontier = declarationBlock0(
    source,
    'TerminalGovernedCompletedSupport.frontier',
  );
  const compatible = declarationBlock0(
    source,
    'TerminalGovernedCompletedSupport.Compatible',
  );
  const covered = declarationBlock0(
    source,
    'TerminalGovernedCompletedSupport.profile_record_covered_iff',
  );
  const saturated = declarationBlock0(
    source,
    'completeSaturatedTerminalGovernedSupport',
  );
  const saturatedCompatible = declarationBlock0(
    source,
    'completeSaturatedTerminalGovernedSupport_compatible',
  );
  const squareCompleted = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governedCompleted',
  );
  const squareCompatible = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governedCompleted_compatible',
  );
  const requiredProfile = declarationBlock0(
    source,
    'TerminalGovernedCompletedSupport.required_profile_mem',
  );

  for (const role of [
    '.carrier', '.origin', '.kernel', '.obligation', '.prefix',
    '.direction', '.saturation', '.budget', '.charge', '.frontier',
  ]) if (!roles.includes(role)) failures.push(`missing-role-${role.slice(1)}`);
  if (!/allFin profileWidth\)\.filter/u.test(roleCoordinates)
      || !/TerminalPrimitiveRecord\.profile coordinate ∈ records/u.test(roleCoordinates)
      || !/system\.profileSystem\.role coordinate = role/u.test(roleCoordinates)) {
    failures.push('computed-profile-partition');
  }
  if (!/completeTerminalPhysicalSupport candidate support\.records/u.test(physical)) {
    failures.push('computed-physical-completion');
  }
  if (!/boundary := support\.physical\.boundary/u.test(frontier)
      || !/interface := support\.physical\.interface/u.test(frontier)
      || !/profiles := support\.profileCoordinates/u.test(frontier)) {
    failures.push('computed-combined-frontier');
  }
  if (!/support\.Governed ∧ support\.physical\.Compatible/u.test(compatible)) {
    failures.push('governed-compatible-conjunction');
  }
  if (!/∃ role, role ∈ allTerminalProfileRoles/u.test(covered)
      || !/mem_own_profile_role_iff/u.test(covered)) {
    failures.push('complete-role-coverage');
  }
  if (!/terminalSaturateRecords system seed/u.test(saturated)
      || !/terminalSaturateRecords_closed system seed/u.test(saturatedCompatible)
      || !/completeTerminalPhysicalSupport_compatible candidate/u.test(saturatedCompatible)) {
    failures.push('saturated-governed-completion');
  }
  if (!/square\.records corner/u.test(squareCompleted)
      || !/square\.records_closed corner/u.test(squareCompatible)
      || !/square\.physically_compatible candidate corner/u.test(squareCompatible)) {
    failures.push('all-square-corners');
  }
  if (!/support\.required_mem governed kind dependent/u.test(requiredProfile)
      || !/mem_own_profile_role_iff/u.test(requiredProfile)) {
    failures.push('required-profile-routing');
  }
  if (/\b(?:fixedProfileTable|fixedFrontierTable|startCoordinate|endCoordinate|profileOffset)\b/u.test(stripped)) {
    failures.push('hard-coded-profile-family');
  }
  return [...new Set(failures)];
}

test('governed completion has one computed all-finite interface', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validateSource0(source), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalGovernedSupportCompletion\n',
  ), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 42);
  assert.equal(PUBLIC_DECLARATIONS.length, 33);
  assert.equal(REUSED_DECLARATIONS.length, 9);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalGovernedSupportCompletion$/mu);
});

test('compiled closure is approved for every governed-completion declaration', async () => {
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

test('regression exercises ten roles, ten rules, and every square corner', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'governedProfile0', 'governedProfile1', 'governedProfile2',
    'governedProfile3', 'governedProfile4', 'governedProfile5',
    'governedProfile6', 'governedProfile7', 'governedProfile8',
    'governedProfile9',
    '.gateSource', '.interfaceConsumer', '.origin', '.kernel',
    '.obligation', '.prefixTail', '.direction', '.saturation',
    '.budget', '.charge',
    'governedCandidate .meet', 'governedCandidate .left',
    'governedCandidate .right', 'governedCandidate .join',
    'governedCompleted_profile_iff', 'profile_record_covered_iff',
    'profileCoordinates_disjoint', 'governedCompleted_required_profile_mem',
    'completeSaturatedTerminalGovernedSupport_compatible',
  ]) assert.match(regression, new RegExp(token.replaceAll('.', '\\.'), 'u'));
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact completion boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-governed-support-completion',
  );
  assert.equal(milestone?.classification,
    'formalized-terminal-governed-support-completion');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite direct-wire candidate/u);
  assert.match(milestone.scope, /ten terminal profile roles/u);
  assert.match(milestone.nonClaim, /dependency system remains explicit/u);
  assert.match(milestone.nonClaim, /projection-compatible square/u);
  assert.match(docs, /Governed terminal support completion/u);
  assert.match(docs, /not.*SaturatePositive/isu);
});

test('status earns governed completion without downstream overclaim', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalSupportCompletionFormalized',
    'leanResidualTerminalGovernedSupportCompletionFormalized',
    'leanResidualTerminalGovernedProfilePartitionFormalized',
    'leanResidualTerminalGovernedSupportCompletionAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalGovernedSupportCompletionScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-finite-seed-lists-and-saturated-support-square-corners',
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
  assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-governed-support-completion',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy anchor and exact remaining boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§2', '§3', 'completed support', 'ten terminal profile roles',
    'computed physical boundary', 'explicit dependency system',
    'frontier pushout', 'projection-compatible square',
    'BN2 square legitimacy', 'SaturatePositive', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-governed-support-completion0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalGovernedSupportCompletionAxiomAudit\.lean[\s\S]{0,1800}-eq 42/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalGovernedSupportCompletion\.lean/u);
});

test('hostile source mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('.frontier]', '.charge]'), 'missing-role-frontier'],
    [
      source.replace('(allFin profileWidth).filter', 'fixedProfileTable.filter'),
      'computed-profile-partition',
    ],
    [
      source.replace(
        'completeTerminalPhysicalSupport candidate support.records',
        'completeTerminalPhysicalSupport candidate callerCertificate',
      ),
      'caller-or-host-certificate',
    ],
    [
      source.replace('profiles := support.profileCoordinates', 'profiles := fixedFrontierTable'),
      'computed-combined-frontier',
    ],
    [
      source.replace('support.Governed ∧ support.physical.Compatible', 'support.Governed'),
      'governed-compatible-conjunction',
    ],
    [
      source.replace('terminalSaturateRecords system seed', 'seed'),
      'saturated-governed-completion',
    ],
    [
      source.replace('square.records_closed corner', 'by exact governanceCertificate'),
      'caller-or-host-certificate',
    ],
    [
      source.replace('support.required_mem governed kind dependent', 'hostLookup'),
      'caller-or-host-certificate',
    ],
    [`${source}\naxiom governedCompletionShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef projectionCompatibleSquare : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`, 'project-axiom'],
    [`${source}\ndef shortcut : True := by native_decide\n`, 'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`, 'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`, 'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
