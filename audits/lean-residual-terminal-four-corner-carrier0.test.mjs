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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalFourCornerCarrier.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalFourCornerCarrierAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalFourCornerCarrier.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_four_corner_carrier.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalSupportSquareSide',
  'TerminalSupportSquareSide.corner',
  'TerminalSupportSquareSide.oppositeCorner',
  'TerminalFourCornerCarrier',
  'TerminalSaturatedSupportSquare.fourCornerCarrier',
  'TerminalFourCornerCarrier.support',
  'TerminalFourCornerCarrier.extracted',
  'TerminalFourCornerCarrier.projectedFrontier',
  'TerminalFourCornerCarrier.boundaryDisposition?',
  'TerminalFourCornerCarrier.interfaceDisposition?',
  'TerminalFourCornerCarrier.boundaryDisposition?_eq_some_iff',
  'TerminalFourCornerCarrier.interfaceDisposition?_eq_some_iff',
  'TerminalFourCornerCarrier.boundary_nodup',
  'TerminalFourCornerCarrier.interface_nodup',
  'TerminalFourCornerCarrier.profile_nodup',
  'TerminalFourCornerCarrier.extracted_boundary',
  'TerminalFourCornerCarrier.extracted_interface',
  'TerminalFourCornerCarrier.corner_compatible',
  'TerminalFourCornerCarrier.meet_profile_transport',
  'TerminalFourCornerCarrier.side_profile_transport',
  'TerminalFourCornerCarrier.join_profile_transport',
  'TerminalFourCornerCarrier.boundary_retained',
  'TerminalFourCornerCarrier.boundary_internalized',
  'TerminalFourCornerCarrier.interface_retained',
  'TerminalFourCornerCarrier.interface_internalized',
  'TerminalFourCornerCarrier.projection_compatible',
  'TerminalFourCornerCarrier.Compatible',
  'TerminalFourCornerCarrier.complete_transport',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.boundaryDisposition?_eq_some_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interfaceDisposition?_eq_some_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundary_nodup`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interface_nodup`,
  `${NAMESPACE}.TerminalFourCornerCarrier.profile_nodup`,
  `${NAMESPACE}.TerminalFourCornerCarrier.extracted_boundary`,
  `${NAMESPACE}.TerminalFourCornerCarrier.extracted_interface`,
  `${NAMESPACE}.TerminalFourCornerCarrier.corner_compatible`,
  `${NAMESPACE}.TerminalFourCornerCarrier.meet_profile_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.side_profile_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.join_profile_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundary_retained`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundary_internalized`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interface_retained`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interface_internalized`,
  `${NAMESPACE}.TerminalFourCornerCarrier.projection_compatible`,
  `${NAMESPACE}.TerminalFourCornerCarrier.complete_transport`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_compatible`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.side_profile_mem_join`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.left_boundary_disposition`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.right_boundary_disposition`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.side_interface_disposition`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governed_projection_compatible`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  ...REUSED_DECLARATIONS,
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
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|transportCertificate|carrierCertificate|compatibilityCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|squareLegitimate|bn2SquareLegitimate|fourCornerOptimaCarrierCompatible|coherentCompletion|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialCarrierTransport)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalSideTightMinimum',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const privateHelpers = [...stripped.matchAll(/^private\s+(?:def|theorem)\s+([^\s({:]+)/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(privateHelpers) !== JSON.stringify([
    'nodup_of_listNoDuplicates',
  ])) failures.push('private-helper-surface');

  const sides = declarationBlock0(source, 'TerminalSupportSquareSide');
  const carrier = declarationBlock0(source, 'TerminalFourCornerCarrier');
  const constructor = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.fourCornerCarrier',
  );
  const support = declarationBlock0(source, 'TerminalFourCornerCarrier.support');
  const extracted = declarationBlock0(source, 'TerminalFourCornerCarrier.extracted');
  const projected = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.projectedFrontier',
  );
  const boundaryDisposition = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.boundaryDisposition?',
  );
  const interfaceDisposition = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.interfaceDisposition?',
  );
  const meet = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.meet_profile_transport',
  );
  const side = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.side_profile_transport',
  );
  const join = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.join_profile_transport',
  );
  const boundaryRetained = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.boundary_retained',
  );
  const boundaryInternalized = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.boundary_internalized',
  );
  const interfaceRetained = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.interface_retained',
  );
  const interfaceInternalized = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.interface_internalized',
  );
  const compatibility = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.Compatible',
  );
  const main = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.complete_transport',
  );

  if (!/\| left\b/u.test(sides) || !/\| right\b/u.test(sides)) {
    failures.push('two-sided-carrier-index');
  }
  for (const field of ['square', 'candidate', 'projection']) {
    if (!new RegExp(`\\b${field}\\s*:`, 'u').test(carrier)) {
      failures.push('computed-carrier-input');
    }
  }
  if (/\b(?:frontier|extracted|certificate)\s*:/iu.test(carrier)) {
    failures.push('computed-carrier-input');
  }
  if (!/square := square/u.test(constructor)
      || !/candidate := candidate/u.test(constructor)
      || !/projection := projection/u.test(constructor)) {
    failures.push('canonical-carrier-constructor');
  }
  if (!/carrier\.square\.governedCompleted carrier\.candidate corner/u.test(support)) {
    failures.push('computed-corner-support');
  }
  if (!/carrier\.square\.extracted carrier\.candidate corner/u.test(extracted)) {
    failures.push('exact-extracted-corner');
  }
  if (!/carrier\.square\.projectedFrontier carrier\.candidate carrier\.projection corner/u.test(projected)) {
    failures.push('exact-projected-corner');
  }
  if (!/if wire ∈ \(carrier\.support side\.corner\)\.frontier\.boundary then/u.test(boundaryDisposition)
      || !/some \(terminalBoundaryFrontierDisposition/u.test(boundaryDisposition)
      || !/else\s*none/u.test(boundaryDisposition)) {
    failures.push('fail-closed-boundary-disposition');
  }
  if (!/if producer ∈ \(carrier\.support side\.corner\)\.frontier\.interface then/u.test(interfaceDisposition)
      || !/some \(terminalInterfaceFrontierDisposition/u.test(interfaceDisposition)
      || !/else\s*none/u.test(interfaceDisposition)) {
    failures.push('fail-closed-interface-disposition');
  }
  if (!/support \.meet\)[\s\S]*support \.left\)[\s\S]*∧[\s\S]*support \.right\)/u.test(meet)) {
    failures.push('exact-meet-profile-transport');
  }
  if (!/cases side/u.test(side) || !/Or\.inl member/u.test(side)
      || !/Or\.inr member/u.test(side)) {
    failures.push('both-side-profile-transport');
  }
  if (!/support \.join\)[\s\S]*support \.left\)[\s\S]*∨[\s\S]*support \.right\)/u.test(join)) {
    failures.push('exact-join-profile-transport');
  }
  if (!/wire ∈ \(carrier\.support \.join\)\.frontier\.boundary/u.test(boundaryRetained)) {
    failures.push('identity-boundary-retention');
  }
  if (!/carrier\.square\.records side\.oppositeCorner/u.test(boundaryInternalized)) {
    failures.push('opposite-side-internalization');
  }
  if (!/producer ∈ \(carrier\.support \.join\)\.frontier\.interface/u.test(interfaceRetained)) {
    failures.push('identity-interface-retention');
  }
  if (!/terminalGateHasExternalConsumer[\s\S]*= false ∧/u.test(interfaceInternalized)
      || !/terminalGateIsGlobalOutput[\s\S]*= false/u.test(interfaceInternalized)) {
    failures.push('exact-interface-internalization');
  }
  for (const field of [
    'cornerCompatible',
    'extractedBoundary',
    'extractedInterface',
    'boundaryDistinct',
    'interfaceDistinct',
    'profileDistinct',
    'meetProfile',
    'joinProfile',
    'boundaryClassified',
    'interfaceClassified',
    'projectedSquare',
  ]) if (!new RegExp(`\\b${field}\\s*:`, 'u').test(compatibility)) {
    failures.push('complete-carrier-contract');
  }
  for (const theorem of [
    'corner_compatible',
    'extracted_boundary',
    'extracted_interface',
    'boundary_nodup',
    'interface_nodup',
    'profile_nodup',
    'meet_profile_transport',
    'join_profile_transport',
    'boundaryDisposition?_eq_some_iff',
    'interfaceDisposition?_eq_some_iff',
  ]) if (!main.includes(theorem)) failures.push('complete-carrier-construction');
  if (!main.includes('carrier.projection_compatible')) {
    failures.push('complete-carrier-construction');
  }
  if (/\b(?:fixedCorner|fixedCoordinate|coordinateMap|indexPermutation|startCoordinate|endCoordinate)\b/u.test(stripped)) {
    failures.push('hard-coded-carrier');
  }
  return [...new Set(failures)];
}

test('four-corner carrier has one computed all-finite fail-closed interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith('import PNP.ResidualTerminalFourCornerCarrier\n'), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 38);
  assert.equal(PUBLIC_DECLARATIONS.length, 28);
  assert.equal(REUSED_DECLARATIONS.length, 10);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalFourCornerCarrier$/mu);
});

test('compiled closure is approved for every carrier declaration', async () => {
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

test('regression covers four corners, retained and internalized coordinates, profiles, and empty rejection', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'carrierSquare',
    'carrierEmptySquare',
    'carrierExample',
    'carrierEmpty',
    'TerminalSupportSquareSide.left.corner',
    'oppositeCorner',
    'extracted_boundary',
    'extracted_interface',
    'boundary_nodup',
    'interface_nodup',
    'profile_nodup',
    'meet_profile_transport',
    'side_profile_transport',
    'join_profile_transport',
    'boundary_retained',
    'boundary_internalized',
    'interface_retained',
    'interface_internalized',
    'some .retained',
    'some .internalized',
    '= none',
    'projection_compatible',
    'complete_transport',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact carrier boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-four-corner-carrier-transport',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-four-corner-carrier-transport');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite computed saturated terminal support square/u);
  assert.match(milestone.scope, /common ambient coordinates/u);
  assert.match(milestone.nonClaim, /four-corner optimum/u);
  assert.match(milestone.nonClaim, /BN2 square legitimacy/u);
  assert.match(docs, /Checked four-corner carrier transport/u);
});

test('status retains carrier transport after conditional coherent completion', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalFourCornerCarrierTransportFormalized',
    'leanResidualTerminalFourCornerCarrierExactEndpointsFormalized',
    'leanResidualTerminalFourCornerCarrierInjectiveCoordinatesFormalized',
    'leanResidualTerminalFourCornerCarrierProfileTransportFormalized',
    'leanResidualTerminalFourCornerCarrierFailClosedPhysicalTransportFormalized',
    'leanResidualTerminalFourCornerCarrierAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalFourCornerCarrierScope,
    'all-finite-computed-saturated-terminal-support-squares-and-canonical-physical-profile-transport-coordinates',
  );
  assert.equal(status.leanResidualTerminalCoherentFourCornerBasisFormalized, true);
  assert.equal(
    status.leanResidualTerminalCoherentFourCornerBasisScope,
    'conditional-on-exact-mode-appropriate-local-route-silence-not-universal-bn2-square-legitimacy',
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
    ({ id }) => id === 'residual-terminal-four-corner-carrier-transport',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy carrier edge and remaining proof boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§3',
    '§11.1',
    'BN2-CoherentOptimum',
    'fourCornerOptimaCarrierCompatible',
    'common ambient',
    'fail-closed',
    'four-corner optimum',
    'BN2 square legitimacy',
    'SaturatePositive',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-four-corner-carrier0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFourCornerCarrierAxiomAudit\.lean[\s\S]{0,1800}-eq 38/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFourCornerCarrier\.lean/u);
});

test('hostile source mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('  projection : TerminalProfileProjection profileWidth',
      '  projection : TerminalProfileProjection profileWidth\n  transportCertificate : True'),
    'caller-or-host-certificate'],
    [source.replace('carrier.square.governedCompleted carrier.candidate corner',
      'carrier.square.governedCompleted carrier.candidate .join'),
    'computed-corner-support'],
    [source.replace('carrier.square.extracted carrier.candidate corner',
      'carrier.square.extracted carrier.candidate .join'),
    'exact-extracted-corner'],
    [source.replace('carrier.square.projectedFrontier carrier.candidate carrier.projection corner',
      'carrier.square.projectedFrontier carrier.candidate carrier.projection .join'),
    'exact-projected-corner'],
    [source.replace('if wire ∈ (carrier.support side.corner).frontier.boundary then',
      'if true then'), 'fail-closed-boundary-disposition'],
    [source.replace('if producer ∈ (carrier.support side.corner).frontier.interface then',
      'if true then'), 'fail-closed-interface-disposition'],
    [source.replace('coordinate ∈ (carrier.support .left).frontier.profiles role ∧\n        coordinate ∈ (carrier.support .right).frontier.profiles role :=\n  carrier.square.governedCompleted_meet_profile_iff',
      'coordinate ∈ (carrier.support .left).frontier.profiles role ∨\n        coordinate ∈ (carrier.support .right).frontier.profiles role :=\n  carrier.square.governedCompleted_meet_profile_iff'),
    'exact-meet-profile-transport'],
    [source.replace('coordinate ∈ (carrier.support .left).frontier.profiles role ∨\n        coordinate ∈ (carrier.support .right).frontier.profiles role :=\n  carrier.square.governedCompleted_join_profile_iff',
      'coordinate ∈ (carrier.support .left).frontier.profiles role ∧\n        coordinate ∈ (carrier.support .right).frontier.profiles role :=\n  carrier.square.governedCompleted_join_profile_iff'),
    'exact-join-profile-transport'],
    [source.replace('wire ∈ (carrier.support .join).frontier.boundary := by',
      'wire ∈ (carrier.support .left).frontier.boundary := by'),
    'identity-boundary-retention'],
    [source.replace('carrier.square.records side.oppositeCorner',
      'carrier.square.records side.corner'), 'opposite-side-internalization'],
    [source.replace('producer ∈ (carrier.support .join).frontier.interface := by',
      'producer ∈ (carrier.support .left).frontier.interface := by'),
    'identity-interface-retention'],
    [source.replace('carrier.candidate.directWireWord producer = false := by',
      'carrier.candidate.directWireWord producer = true := by'),
    'exact-interface-internalization'],
    [source.replace('  boundaryDistinct : ∀ corner,',
      '  boundaryDuplicatesAllowed : ∀ corner,'), 'complete-carrier-contract'],
    [source.replace('      projectedSquare := carrier.projection_compatible',
      '      projectedSquare := carrier.square.governed_projection_compatible\n        carrier.candidate carrier.projection'),
    'complete-carrier-construction'],
    [`${source}\naxiom carrierShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef fourCornerOptimaCarrierCompatible : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`, 'project-axiom'],
    [`${source}\ndef hostLookup := true\n`, 'caller-or-host-certificate'],
    [`${source}\ntheorem shortcut : True := by native_decide\n`, 'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`,
      'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`, 'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.notEqual(mutation, source, expected);
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
