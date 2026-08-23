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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalProjectionSquare.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalProjectionSquareAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalProjectionSquare.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_projection_square.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalGovernedFrontier.project',
  'TerminalGovernedFrontier.project_boundary',
  'TerminalGovernedFrontier.project_interface',
  'TerminalGovernedFrontier.mem_project_profiles_iff',
  'TerminalGovernedFrontier.project_profiles_nodup',
  'TerminalGovernedFrontier.project_idempotent',
  'terminalProjectedGovernedFrontierPushout',
  'mem_terminalProjectedGovernedFrontierPushout_profiles_iff',
  'TerminalGovernedFrontier.project_pushout',
  'TerminalSaturatedSupportSquare.projectedFrontier',
  'TerminalSaturatedSupportSquare.projectedFrontier_boundary',
  'TerminalSaturatedSupportSquare.projectedFrontier_interface',
  'TerminalSaturatedSupportSquare.mem_projectedFrontier_profiles_iff',
  'TerminalSaturatedSupportSquare.projectedFrontier_profiles_nodup',
  'TerminalSaturatedSupportSquare.forgotten_not_mem_projectedFrontier',
  'TerminalSaturatedSupportSquare.projected_meet_profile_iff',
  'TerminalSaturatedSupportSquare.projected_join_profile_iff',
  'TerminalSaturatedSupportSquare.projected_join_eq_pushout',
  'TerminalSaturatedSupportSquare.ProjectionCompatible',
  'TerminalSaturatedSupportSquare.governed_projection_compatible',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalProfileProjection.Keeps`,
  `${NAMESPACE}.TerminalProfileProjection.Forgets`,
  `${NAMESPACE}.TerminalGovernedFrontier.extensionality`,
  `${NAMESPACE}.terminalBoundaryFrontierPushout`,
  `${NAMESPACE}.terminalInterfaceFrontierPushout`,
  `${NAMESPACE}.terminalProfileFrontierPushout`,
  `${NAMESPACE}.terminalGovernedFrontierPushout`,
  `${NAMESPACE}.mem_terminalProfileFrontierPushout_iff`,
  `${NAMESPACE}.TerminalGovernedCompletedSupport.profileCoordinates_nodup`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governed_frontier_pushout`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const NEW_THEOREMS = Object.freeze(PUBLIC_DECLARATIONS.filter((name) => ![
  `${NAMESPACE}.TerminalGovernedFrontier.project`,
  `${NAMESPACE}.terminalProjectedGovernedFrontierPushout`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.projectedFrontier`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.ProjectionCompatible`,
].includes(name)));

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  `${NAMESPACE}.TerminalGovernedFrontier.extensionality`,
  `${NAMESPACE}.mem_terminalProfileFrontierPushout_iff`,
  `${NAMESPACE}.terminalProfileFrontierPushout_nodup`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governed_frontier_pushout`,
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
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|projectionCertificate|joinCertificate|compatibilityCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|squareLegitimate|bn2SquareLegitimate|sideTightMinimum|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialProjectionSquare)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalFrontierPushout',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (/^private\s+/gmu.test(stripped)) failures.push('private-helper-surface');

  const project = declarationBlock0(source, 'TerminalGovernedFrontier.project');
  const projectedPushout = declarationBlock0(
    source,
    'terminalProjectedGovernedFrontierPushout',
  );
  const projectedCorner = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.projectedFrontier',
  );
  const projectedJoin = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.projected_join_eq_pushout',
  );
  const compatibility = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.ProjectionCompatible',
  );
  const main = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.governed_projection_compatible',
  );

  if (!/boundary := frontier\.boundary/u.test(project)
      || !/interface := frontier\.interface/u.test(project)
      || !/frontier\.profiles role\)\.filter projection\.keep/u.test(project)) {
    failures.push('exact-forgetful-projection');
  }
  if (!/boundary := terminalBoundaryFrontierPushout left right/u.test(projectedPushout)
      || !/interface := terminalInterfaceFrontierPushout left right/u.test(projectedPushout)
      || !/terminalProfileFrontierPushout left right role\)\.filter projection\.keep/u.test(projectedPushout)) {
    failures.push('side-only-projected-pushout');
  }
  if (/\.join|square\./u.test(projectedPushout)) {
    failures.push('projected-pushout-reads-join');
  }
  if (!/governedCompleted candidate corner\)\.frontier\.project projection/u.test(projectedCorner)) {
    failures.push('computed-corner-projection');
  }
  if (!/governed_frontier_pushout/u.test(projectedJoin)
      || !/TerminalGovernedFrontier\.project_pushout/u.test(projectedJoin)) {
    failures.push('join-projection-commutation');
  }
  if (!/projectedFrontier candidate projection \.join =/u.test(compatibility)
      || !/terminalProjectedGovernedFrontierPushout/u.test(compatibility)
      || !/∀ role coordinate/u.test(compatibility)
      || !/projectedFrontier candidate projection \.meet/u.test(compatibility)
      || !/projectedFrontier candidate projection \.left/u.test(compatibility)
      || !/projectedFrontier candidate projection \.right/u.test(compatibility)) {
    failures.push('projection-compatible-square-contract');
  }
  if (!/projected_join_eq_pushout/u.test(main)
      || !/projected_meet_profile_iff/u.test(main)) {
    failures.push('legacy-projection-commutation-law');
  }
  if (/\b(?:fixedCoordinate|fixedRole|fixedProjection|startCoordinate|endCoordinate|profileOffset)\b/u.test(stripped)) {
    failures.push('hard-coded-projection');
  }
  return [...new Set(failures)];
}

test('projection square has one computed all-finite interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith('import PNP.ResidualTerminalProjectionSquare\n'), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 33);
  assert.equal(PUBLIC_DECLARATIONS.length, 20);
  assert.equal(REUSED_DECLARATIONS.length, 13);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalProjectionSquare$/mu);
});

test('compiled closure is approved for every projection-square declaration', async () => {
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

test('regression covers projections, roles, square shapes, and physical invariance', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'projectionKeepAll',
    'projectionForgetAll',
    'projectionAlternating',
    'projectionEmptySquare',
    'projectionIdenticalSquare',
    'projectionDisjointSquare',
    'projectedFrontier_boundary',
    'projectedFrontier_interface',
    'projected_join_eq_pushout',
    'projected_meet_profile_iff',
    'governed_projection_compatible',
    'project_idempotent',
    '.carrier',
    '.origin',
    '.kernel',
    '.obligation',
    '.prefix',
    '.direction',
    '.saturation',
    '.budget',
    '.charge',
    '.frontier',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact projection-square boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-governed-projection-square',
  );
  assert.equal(milestone?.classification,
    'formalized-terminal-governed-projection-square');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite direct-wire candidate/u);
  assert.match(milestone.scope, /every forgetful terminal projection/u);
  assert.match(milestone.nonClaim, /BN2 square legitimacy/u);
  assert.match(milestone.nonClaim, /SaturatePositive/u);
  assert.match(docs, /Governed terminal projection square/u);
});

test('status earns projection commutation without downstream overclaim', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalProjectionSquareFormalized',
    'leanResidualTerminalProjectionPhysicalInvariantFormalized',
    'leanResidualTerminalProjectionProfileExactFormalized',
    'leanResidualTerminalProjectionMeetJoinCommuteFormalized',
    'leanResidualTerminalProjectionPushoutCommuteFormalized',
    'leanResidualTerminalProjectionSquareAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalProjectionSquareScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-computed-saturated-support-squares-and-forgetful-terminal-projections',
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
    ({ id }) => id === 'residual-terminal-governed-projection-square',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy edge and remaining proof boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§3',
    'projection',
    'meet',
    'join',
    'side-only',
    'all finite',
    'BN2 square legitimacy',
    'SaturatePositive',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-projection-square0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalProjectionSquareAxiomAudit\.lean[\s\S]{0,1800}-eq 33/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalProjectionSquare\.lean/u);
});

test('hostile source mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('boundary := frontier.boundary', 'boundary := []'),
      'exact-forgetful-projection'],
    [source.replace('interface := frontier.interface', 'interface := []'),
      'exact-forgetful-projection'],
    [source.replace('(frontier.profiles role).filter projection.keep',
      'frontier.profiles role'), 'exact-forgetful-projection'],
    [source.replace('boundary := terminalBoundaryFrontierPushout left right',
      'boundary := left.frontier.boundary'), 'side-only-projected-pushout'],
    [source.replace('(terminalProfileFrontierPushout left right role).filter projection.keep',
      '(terminalProfileFrontierPushout left right role).filter (fun _ => true)'),
    'side-only-projected-pushout'],
    [source.replace(
      '    profiles := fun role =>\n      (terminalProfileFrontierPushout',
      '    profiles := fun role =>\n      let _forbidden := TerminalSupportSquareCorner.join\n      (terminalProfileFrontierPushout'),
    'projected-pushout-reads-join'],
    [source.replace('TerminalGovernedFrontier.project_pushout _ _ projection',
      'by rfl'), 'join-projection-commutation'],
    [source.replace('projected_join_eq_pushout candidate projection',
      'projected_meet_profile_iff candidate projection'),
    'legacy-projection-commutation-law'],
    [`${source}\naxiom projectionShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef squareLegitimate : Prop := True\n`, 'overclaim'],
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
