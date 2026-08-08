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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalFourCornerOptimumCompatibility.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFourCornerOptimumCompatibilityAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFourCornerOptimumCompatibility.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_four_corner_optimum_compatibility.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalSupportWire.ambientIndex',
  'terminalSupportWireAt',
  'terminalSupportWireAt_ambientIndex',
  'TerminalSupportWire.ambientIndex_terminalSupportWireAt',
  'TerminalSupportWire.ambientIndex_injective',
  'TerminalFourCornerCarrier.boundaryIndex?',
  'TerminalFourCornerCarrier.interfaceIndex?',
  'TerminalFourCornerCarrier.boundaryIndex?_eq_some_iff',
  'TerminalFourCornerCarrier.interfaceIndex?_eq_some_iff',
  'TerminalFourCornerCarrier.boundaryIndex?_ambient_get',
  'TerminalFourCornerCarrier.interfaceIndex?_get',
  'TerminalFourCornerCarrier.boundaryAdapter',
  'TerminalFourCornerCarrier.cornerImplementation',
  'TerminalFourCornerCarrier.ambientizeCandidate',
  'TerminalFourCornerCarrier.ambientCandidate',
  'TerminalFourCornerCarrier.localizeCandidate',
  'TerminalFourCornerCarrier.boundaryAdapter_semantics_get',
  'TerminalFourCornerCarrier.ambientizeCandidate_semantics_present',
  'TerminalFourCornerCarrier.ambientizeCandidate_semantics_absent',
  'TerminalFourCornerCarrier.localizeCandidate_semantics',
  'TerminalFourCornerCarrier.localize_ambientize_semantics',
  'TerminalFourCornerCarrier.ambientizeCandidate_gateCount',
  'TerminalFourCornerCarrier.localizeCandidate_gateCount',
  'TerminalFourCornerCarrier.ambientizeCandidate_equivalent',
  'TerminalFourCornerCarrier.localizeCandidate_equivalent',
  'TerminalFourCornerCarrier.localize_ambientize_equivalent',
  'TerminalFourCornerCarrier.ambientImplementation',
  'TerminalFourCornerCarrier.localizeImplementation',
  'TerminalFourCornerCarrier.localizeImplementation_gateCount',
  'TerminalFourCornerCarrier.ambient_referenceMinimum_eq_corner',
  'TerminalFourCornerSizes.at',
  'TerminalProjectionFourCorners.at',
  'TerminalFullFourCornerBasis.at',
  'TerminalQuotientFourCornerBasis.at',
  'TerminalFourCornerCarrier.ambientProfileSystem',
  'TerminalFourCornerCarrier.optimizationCorners',
  'TerminalFourCornerCarrier.optimizationCorners_at',
  'TerminalFourCornerCarrier.optimizationCorners_role',
  'TerminalFourCornerCarrier.optimizationCorners_projection',
  'TerminalFourCornerCarrier.localizeRealization',
  'TerminalFourCornerCarrier.localizeRealization_gateCount',
  'TerminalFourCornerOptimumFamily',
  'TerminalFourCornerCarrier.canonicalOptimumFamily',
  'TerminalFourCornerOptimumFamily.fullLocalRealization',
  'TerminalFourCornerOptimumFamily.quotientLocalRealization',
  'TerminalFourCornerOptimumFamily.Compatible',
  'TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalSupportWireAt_ambientIndex`,
  `${NAMESPACE}.TerminalSupportWire.ambientIndex_terminalSupportWireAt`,
  `${NAMESPACE}.TerminalSupportWire.ambientIndex_injective`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundaryIndex?_eq_some_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interfaceIndex?_eq_some_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundaryIndex?_ambient_get`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interfaceIndex?_get`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundaryAdapter_semantics_get`,
  `${NAMESPACE}.TerminalFourCornerCarrier.ambientizeCandidate_semantics_present`,
  `${NAMESPACE}.TerminalFourCornerCarrier.ambientizeCandidate_semantics_absent`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localizeCandidate_semantics`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localize_ambientize_semantics`,
  `${NAMESPACE}.TerminalFourCornerCarrier.ambientizeCandidate_gateCount`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localizeCandidate_gateCount`,
  `${NAMESPACE}.TerminalFourCornerCarrier.ambientizeCandidate_equivalent`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localizeCandidate_equivalent`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localize_ambientize_equivalent`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localizeImplementation_gateCount`,
  `${NAMESPACE}.TerminalFourCornerCarrier.ambient_referenceMinimum_eq_corner`,
  `${NAMESPACE}.TerminalFourCornerCarrier.optimizationCorners_at`,
  `${NAMESPACE}.TerminalFourCornerCarrier.optimizationCorners_role`,
  `${NAMESPACE}.TerminalFourCornerCarrier.optimizationCorners_projection`,
  `${NAMESPACE}.TerminalFourCornerCarrier.localizeRealization_gateCount`,
  `${NAMESPACE}.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.complete_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.boundary_nodup`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interface_nodup`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalFullBasis_sizes`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalQuotientBasis_sizes`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison_gateCount`,
  `${NAMESPACE}.referenceMinimum_le_of_equivalent`,
  `${NAMESPACE}.referenceMinimumWitness_equivalent`,
  `${NAMESPACE}.equivalentBool_sound`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  ...REUSED_DECLARATIONS.filter((name) => ![
    `${NAMESPACE}.TerminalFourCornerCarrier.boundary_nodup`,
    `${NAMESPACE}.TerminalFourCornerCarrier.interface_nodup`,
    `${NAMESPACE}.referenceMinimumWitness_equivalent`,
    `${NAMESPACE}.equivalentBool_sound`,
  ].includes(name)),
]);

const PRIVATE_HELPERS = Object.freeze([
  'locateMember',
  'memberIndex',
  'get_memberIndex',
  'get_injective_of_nodup',
  'memberIndex_get_of_nodup',
  'Source.liftZeroGates',
  'Source.substituteZeroInputs',
  'Gate.substituteZeroInputs',
  'Program.substituteZeroInputs',
  'DirectWireWord.substituteZeroInputs',
  'Candidate.precomposeZero',
  'Source.eval_liftZeroGates',
  'Source.eval_substituteZeroInputs',
  'Gate.eval_substituteZeroInputs',
  'Program.eval_substituteZeroInputs',
  'Candidate.precomposeZero_semantics',
  'TerminalFourCornerCarrier.boundaryBinding',
  'TerminalFourCornerCarrier.boundaryBinding_eval',
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
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|transportCertificate|carrierCertificate|compatibilityCertificate|observerCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|squareLegitimate|bn2SquareLegitimate|coherentFourCornerBasis|sideTightCompletionExists|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialCarrierTransport)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalFourCornerCarrier',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const privateHelpers = [...stripped.matchAll(
    /^private\s+(?:def|theorem)\s+([^\s({:]+)/gmu,
  )].map((match) => match[1]);
  if (JSON.stringify(privateHelpers) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const ambientIndex = declarationBlock0(source, 'TerminalSupportWire.ambientIndex');
  const decode = declarationBlock0(source, 'terminalSupportWireAt');
  const boundaryQuery = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.boundaryIndex?',
  );
  const interfaceQuery = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.interfaceIndex?',
  );
  const ambientize = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.ambientizeCandidate',
  );
  const localize = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.localizeCandidate',
  );
  const absent = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.ambientizeCandidate_semantics_absent',
  );
  const minimum = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.ambient_referenceMinimum_eq_corner',
  );
  const profileSystem = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.ambientProfileSystem',
  );
  const corners = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.optimizationCorners',
  );
  const family = declarationBlock0(source, 'TerminalFourCornerOptimumFamily');
  const compatible = declarationBlock0(
    source,
    'TerminalFourCornerOptimumFamily.Compatible',
  );
  const main = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible',
  );

  if (!/\.input index => Fin\.castAdd gates index/u.test(ambientIndex)
      || !/\.gate index => Fin\.natAdd inputs index/u.test(ambientIndex)) {
    failures.push('canonical-ambient-coordinate');
  }
  if (!/splitFin TerminalSupportWire\.input TerminalSupportWire\.gate coordinate/u.test(decode)) {
    failures.push('reversible-ambient-coordinate');
  }
  if (!/coordinate : Fin \(inputs \+ gates\)/u.test(boundaryQuery)
      || !/if member : wire ∈ \(carrier\.extracted corner\)\.boundary then/u.test(boundaryQuery)
      || !/some \(memberIndex member\)[\s\S]*else[\s\S]*none/u.test(boundaryQuery)) {
    failures.push('fail-closed-boundary-index');
  }
  if (!/producer : Fin gates/u.test(interfaceQuery)
      || !/if member : producer ∈ \(carrier\.extracted corner\)\.interface then/u.test(interfaceQuery)
      || !/some \(memberIndex member\)[\s\S]*else[\s\S]*none/u.test(interfaceQuery)) {
    failures.push('fail-closed-interface-index');
  }
  if (!/Candidate \(inputs \+ gates\) replacementGates gates/u.test(ambientize)
      || !/\.boundary\.get index\)\.ambientIndex/u.test(ambientize)
      || !/carrier\.interfaceIndex\? corner producer/u.test(ambientize)
      || !/\| none => \.constant false/u.test(ambientize)) {
    failures.push('faithful-ambientization');
  }
  if (!/Candidate \(carrier\.extracted corner\)\.boundary\.length replacementGates/u.test(localize)
      || !/candidate\.precomposeZero \(carrier\.boundaryBinding corner\)/u.test(localize)
      || !/\.interface\.get index/u.test(localize)) {
    failures.push('exact-localization');
  }
  if (!/absent : producer ∉ \(carrier\.extracted corner\)\.interface/u.test(absent)
      || !/=\s*false := by/u.test(absent)
      || !/dif_neg absent/u.test(absent)) {
    failures.push('absent-output-false');
  }
  for (const token of [
    'Nat.le_antisymm',
    'referenceMinimum_le_of_equivalent',
    'ambientizeCandidate_equivalent',
    'localizeCandidate_equivalent',
    'localize_ambientize_equivalent',
    'referenceMinimumWitness_equivalent',
    'equivalentBool_sound',
  ]) if (!minimum.includes(token)) failures.push('bidirectional-minimum-preservation');
  if (!/role := system\.profileSystem\.role/u.test(profileSystem)
      || !/observe := observe/u.test(profileSystem)) {
    failures.push('derived-shared-role');
  }
  if (!/system := carrier\.ambientProfileSystem observe/u.test(corners)
      || !/projection := carrier\.projection/u.test(corners)) {
    failures.push('shared-observer-projection');
  }
  for (const corner of ['meet', 'left', 'right', 'join']) {
    if (!new RegExp(`${corner} := carrier\\.ambientImplementation \\.${corner}`, 'u')
      .test(corners)) failures.push('all-four-ambient-corners');
  }
  if (!/fullBasis : TerminalFullFourCornerBasis/u.test(family)
      || !/quotientBasis : TerminalQuotientFourCornerBasis/u.test(family)) {
    failures.push('paired-optimum-family');
  }
  for (const field of [
    'carrierCompatible',
    'semanticMinimumPreserved',
    'fullSizes',
    'quotientSizes',
    'fullLocalMinimum',
    'quotientLocalMinimum',
    'sharedRole',
    'sharedProjection',
  ]) if (!new RegExp(`\\b${field}\\s*:`, 'u').test(compatible)) {
    failures.push('complete-compatibility-contract');
  }
  for (const token of [
    'carrier.complete_transport',
    'carrier.ambient_referenceMinimum_eq_corner',
    'canonicalFullBasis_sizes',
    'canonicalQuotientBasis_sizes',
    'fullLocalMinimum',
    'quotientLocalMinimum',
    'optimizationCorners_role',
    'optimizationCorners_projection',
  ]) if (!main.includes(token)) failures.push('complete-compatibility-construction');
  if (!/cases corner <;> rfl/gmu.test(main)
      || (main.match(/cases corner <;> rfl/gmu) ?? []).length !== 2) {
    failures.push('all-four-local-optima');
  }
  if (/\b(?:fixedCorner|fixedCoordinate|coordinateMap|indexPermutation|startCoordinate|endCoordinate)\b/u.test(stripped)) {
    failures.push('hard-coded-carrier');
  }
  return [...new Set(failures)];
}

test('four-corner optima use one reversible all-finite common carrier', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFourCornerOptimumCompatibility\n',
  ), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 57);
  assert.equal(PUBLIC_DECLARATIONS.length, 47);
  assert.equal(REUSED_DECLARATIONS.length, 10);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalFourCornerOptimumCompatibility$/mu);
});

test('compiled closure is approved for every optimum-carrier declaration', async () => {
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

test('regression covers all corners, empty carriers, exact coordinates, and both optima', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'optimumCarrier',
    'optimumEmptyCarrier',
    'terminalSupportWireAt',
    'boundaryIndex?',
    'interfaceIndex?',
    '= none',
    'ambientizeCandidate_semantics_present',
    'ambientizeCandidate_semantics_absent',
    '= false',
    'localize_ambientize_semantics',
    'ambient_referenceMinimum_eq_corner',
    'optimizationCorners',
    'projection.keep',
    'canonicalOptimumFamily',
    'fourCornerOptimaCarrierCompatible',
    'fullLocalMinimum',
    'quotientLocalMinimum',
    '.boundary = []',
    '.interface = []',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact optimum-carrier boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-four-corner-optimum-carrier-compatibility',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-four-corner-optimum-carrier-compatibility');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite computed saturated terminal support square/u);
  assert.match(milestone.scope, /one common ambient carrier/u);
  assert.match(milestone.nonClaim, /coherent transport/u);
  assert.match(milestone.nonClaim, /BN2 square legitimacy/u);
  assert.match(docs, /Checked four-corner optimum carrier compatibility/u);
});

test('status retains optimum compatibility after conditional completion', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalFourCornerOptimaCarrierCompatibleFormalized',
    'leanResidualTerminalFourCornerOptimaFaithfulAmbientizationFormalized',
    'leanResidualTerminalFourCornerOptimaReferenceMinimumPreservedFormalized',
    'leanResidualTerminalFourCornerOptimaLocalizedMinimaFormalized',
    'leanResidualTerminalFourCornerOptimaSharedObserverProjectionFormalized',
    'leanResidualTerminalFourCornerOptimaAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalFourCornerOptimaCarrierScope,
    'all-finite-computed-saturated-terminal-support-squares-one-reversible-ambient-carrier-and-shared-observer-projection',
  );
  assert.equal(status.leanResidualTerminalCoherentFourCornerBasisFormalized, true);
  assert.equal(
    status.leanResidualTerminalCoherentFourCornerBasisScope,
    'conditional-on-exact-mode-appropriate-local-route-silence-not-universal-bn2-square-legitimacy',
  );
  for (const field of [
    'leanResidualTerminalSquareLegitimacyFormalized',
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
    ({ id }) => id === 'residual-terminal-four-corner-optimum-carrier-compatibility',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy dependency edge and remaining boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§3',
    '§11.1',
    'fourCornerOptimaCarrierCompatible',
    'common ambient',
    'fail-closed',
    'full and quotient',
    'coherent transport',
    'sideTightCompletionExists',
    'BN2 square legitimacy',
    'SaturatePositive',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-four-corner-optimum-compatibility0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFourCornerOptimumCompatibilityAxiomAudit\.lean[\s\S]{0,1800}-eq 57/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFourCornerOptimumCompatibility\.lean/u);
});

test('hostile optimum-carrier mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('  | .gate index => Fin.natAdd inputs index',
      '  | .gate index => Fin.castAdd inputs index'),
    'canonical-ambient-coordinate'],
    [source.replace('splitFin TerminalSupportWire.input TerminalSupportWire.gate coordinate',
      'splitFin TerminalSupportWire.gate TerminalSupportWire.input coordinate'),
    'reversible-ambient-coordinate'],
    [source.replace('if member : wire ∈ (carrier.extracted corner).boundary then',
      'if true then'), 'fail-closed-boundary-index'],
    [source.replace('if member : producer ∈ (carrier.extracted corner).interface then',
      'if true then'), 'fail-closed-interface-index'],
    [source.replaceAll('| none => .constant false⟩', '| none => .constant true⟩'),
      'faithful-ambientization'],
    [source.replace('candidate.precomposeZero (carrier.boundaryBinding corner)',
      'candidate.precomposeZero (carrier.boundaryBinding .join)'),
    'exact-localization'],
    [source.replace('(absent : producer ∉ (carrier.extracted corner).interface)',
      '(present : producer ∈ (carrier.extracted corner).interface)'),
    'absent-output-false'],
    [source.replaceAll('  apply Nat.le_antisymm', '  apply Nat.le_of_eq'),
      'bidirectional-minimum-preservation'],
    [source.replace('  { role := system.profileSystem.role',
      '  { role := fun _ => .origin'), 'derived-shared-role'],
    [source.replace('    projection := carrier.projection',
      '    projection := { keep := fun _ => true }'),
    'shared-observer-projection'],
    [source.replace('    join := carrier.ambientImplementation .join',
      '    join := carrier.ambientImplementation .meet'),
    'all-four-ambient-corners'],
    [source.replace('  quotientBasis : TerminalQuotientFourCornerBasis',
      '  quotientCertificate : TerminalQuotientFourCornerBasis'),
    'paired-optimum-family'],
    [source.replace('  sharedProjection :', '  alternateProjection :'),
      'complete-compatibility-contract'],
    [source.replace('      sharedProjection := carrier.optimizationCorners_projection observe',
      '      sharedProjection := rfl'), 'complete-compatibility-construction'],
    [`${source}\naxiom optimumCarrierShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef coherentFourCornerBasis : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`, 'project-axiom'],
    [`${source}\ndef observerCertificate := true\n`, 'caller-or-host-certificate'],
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
