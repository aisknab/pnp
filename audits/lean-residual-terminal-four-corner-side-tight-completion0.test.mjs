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
  'lean/PNP/ResidualTerminalFourCornerSideTightCompletion.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFourCornerSideTightCompletionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFourCornerSideTightCompletion.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_four_corner_side_tight_completion.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalOptimumRoutePhase',
  'TerminalFourCornerCarrier.firstOptimumRoute?',
  'TerminalFourCornerCarrier.firstOptimumRoute?_coherence',
  'TerminalFourCornerCarrier.firstOptimumRoute?_quotientPromotion',
  'TerminalFourCornerOptimumRoutedFailure',
  'TerminalFourCornerOptimumRoutedFailure.sound',
  'TerminalFourCornerCarrier.routedFailureOfFirst',
  'TerminalFourCornerCarrier.NoOptimumRoute',
  'TerminalFourCornerCarrier.NoOptimumCoherenceRoute',
  'TerminalFourCornerCarrier.NoOptimumPromotionRoute',
  'TerminalFourCornerCarrier.NoOptimumCoherenceRoutes',
  'TerminalFourCornerCarrier.noOptimumCoherenceRoute_iff_noFailure',
  'TerminalFourCornerCarrier.noOptimumPromotionRoute_iff_noModeMismatch',
  'TerminalFourCornerCarrier.firstOptimumRoute?_sound',
  'TerminalFourCornerCarrier.sideTightCompletionOrFirstRoute',
  'TerminalFourCornerOptimumRoutedFailure.excludesCoherentOptimum',
  'TerminalFourCornerCarrier.sideTightCompletionExists',
  'TerminalFourCornerCarrier.sideTightCompletionExistsEachMode',
  'TerminalFourCornerCarrier.sideTightCompletion_fullValue',
  'TerminalFourCornerCarrier.sideTightCompletion_quotientValue',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumRoute?_coherence`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumRoute?_quotientPromotion`,
  `${NAMESPACE}.TerminalFourCornerOptimumRoutedFailure.sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.noOptimumCoherenceRoute_iff_noFailure`,
  `${NAMESPACE}.TerminalFourCornerCarrier.noOptimumPromotionRoute_iff_noModeMismatch`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumRoute?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletionOrFirstRoute`,
  `${NAMESPACE}.TerminalFourCornerOptimumRoutedFailure.excludesCoherentOptimum`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletionExists`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletionExistsEachMode`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletion_fullValue`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletion_quotientValue`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumModeMismatch?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.noFailure_iff_coherentOptimumTuple`,
  `${NAMESPACE}.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible`,
  `${NAMESPACE}.TerminalFourCornerCarrier.optimumTransportTheta`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonical_numericallySideTight_values`,
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
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|transportCertificate|coherenceCertificate|routeCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|squareLegitimate|bn2SquareLegitimate|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialCoherence)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalFourCornerOptimumCoherence',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const privateHelpers = [...stripped.matchAll(
    /^private\s+(?:structure|inductive|def|theorem)\s+([^\s({:]+)/gmu,
  )].map((match) => match[1]);
  if (privateHelpers.length !== 0) failures.push('private-helper-surface');

  const phase = declarationBlock0(source, 'TerminalOptimumRoutePhase');
  const query = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.firstOptimumRoute?',
  );
  const routed = declarationBlock0(
    source,
    'TerminalFourCornerOptimumRoutedFailure',
  );
  const silence = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.NoOptimumRoute',
  );
  const sound = declarationBlock0(
    source,
    'TerminalFourCornerOptimumRoutedFailure.sound',
  );
  const total = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.sideTightCompletionOrFirstRoute',
  );
  const excludes = declarationBlock0(
    source,
    'TerminalFourCornerOptimumRoutedFailure.excludesCoherentOptimum',
  );
  const completion = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.sideTightCompletionExists',
  );
  const eachMode = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.sideTightCompletionExistsEachMode',
  );
  const fullValue = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.sideTightCompletion_fullValue',
  );
  const quotientValue = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.sideTightCompletion_quotientValue',
  );

  if (!/\| coherence \(mode : TerminalOptimumCoherenceMode\)/u.test(phase)
      || !/\| quotientPromotion/u.test(phase)) {
    failures.push('separate-route-phases');
  }
  if (!/\| \.coherence mode => carrier\.firstOptimumCoherenceFailure\? observe mode/u.test(query)
      || !/\| \.quotientPromotion => carrier\.firstOptimumModeMismatch\? observe/u.test(query)) {
    failures.push('exact-phase-query');
  }
  if (!/failure\s*:\s*TerminalFourCornerOptimumFailure/u.test(routed)
      || !/first\s*:\s*carrier\.firstOptimumRoute\? observe phase = some failure/u.test(routed)) {
    failures.push('proof-bearing-first-route');
  }
  if (!/carrier\.firstOptimumRoute\? observe phase = none/u.test(silence)) {
    failures.push('computed-route-silence');
  }
  if (!/firstOptimumCoherenceFailure\?_sound/u.test(sound)
      || !/firstOptimumModeMismatch\?_sound/u.test(sound)) {
    failures.push('both-route-soundness');
  }
  if (!/Nonempty \(TerminalFourCornerCoherentOptimumTuple/u.test(total)
      || !/Nonempty \(TerminalFourCornerOptimumRoutedFailure/u.test(total)
      || !/cases found : carrier\.firstOptimumCoherenceFailure\?/u.test(total)) {
    failures.push('total-completion-or-route');
  }
  if (!/¬Nonempty \(TerminalFourCornerCoherentOptimumTuple/u.test(excludes)
      || !/rw \[tuple\.noFailure\] at first/u.test(excludes)) {
    failures.push('route-excludes-completion');
  }
  if (!/\(noRoute : carrier\.NoOptimumCoherenceRoute observe mode\)/u.test(completion)
      || !/Nonempty \(TerminalFourCornerCoherentOptimumTuple/u.test(completion)
      || !/noFailure_iff_coherentOptimumTuple/u.test(completion)) {
    failures.push('conditional-side-tight-completion');
  }
  if (!/NoOptimumCoherenceRoutes observe/u.test(eachMode)
      || !/\.full noRoutes\.1/u.test(eachMode)
      || !/\.quotient noRoutes\.2/u.test(eachMode)
      || /NoOptimumPromotionRoute/u.test(eachMode)) {
    failures.push('mode-separated-completions');
  }
  if (!/fullBasis\.sizes\.tightValue\?/u.test(fullValue)
      || !/some \(carrier\.optimizationCorners observe\)\.fullDelta/u.test(fullValue)
      || !/tuple\.fullIncidenceValue/u.test(fullValue)) {
    failures.push('exact-full-value');
  }
  if (!/quotientBasis\.sizes\.tightValue\?/u.test(quotientValue)
      || !/some \(carrier\.optimizationCorners observe\)\.quotientDelta/u.test(quotientValue)
      || !/tuple\.quotientIncidenceValue/u.test(quotientValue)) {
    failures.push('exact-quotient-value');
  }
  if (/\b(?:CritC|SaturatePositive|BCELReady|ZeroSlack|PCCMin|GlobalNoOutcome)\b/u.test(stripped)) {
    failures.push('global-route-overreach');
  }
  if (/\b(?:fixedCoordinate|fixedCorner|coordinateMap|indexPermutation)\b/u.test(stripped)) {
    failures.push('hard-coded-instance');
  }
  return [...new Set(failures)];
}

test('side-tight completion is total under exact local route silence', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every public and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 28);
  assert.equal(PUBLIC_DECLARATIONS.length, 20);
  assert.equal(REUSED_DECLARATIONS.length, 8);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFourCornerSideTightCompletion\n',
  ), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalFourCornerSideTightCompletion$/mu);
});

test('compiled closure is approved for every completion declaration', async () => {
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

test('regression covers both phases, modes, route outcomes, values, and failure classes', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    '.coherence mode',
    '.quotientPromotion',
    'NoOptimumCoherenceRoutes',
    'NoOptimumPromotionRoute',
    'sideTightCompletionExistsEachMode',
    'sideTightCompletion_fullValue',
    'sideTightCompletion_quotientValue',
    'sideTightCompletionOrFirstRoute',
    'semanticMismatch',
    'profileMismatch',
    'chargeProfileMismatch',
    'modeMismatch',
    'openObligation',
    'firstOptimumRoute?_sound',
    'excludesCoherentOptimum',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication pins the exact local route-silence theorem boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-four-corner-side-tight-completion',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-four-corner-side-tight-completion-under-local-route-silence');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite computed terminal support square/u);
  assert.match(milestone.scope, /local route silence/u);
  assert.match(milestone.nonClaim, /BN2 square legitimacy/u);
  assert.match(milestone.nonClaim, /complete global/u);
  assert.match(docs, /BN2-CoherentOptimum/u);
  assert.match(docs, /sideTightCompletionExists/u);
});

test('status earns only the route-silence completion edge', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalFourCornerOptimumLocalRouteClassifierFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSoundnessFormalized',
    'leanResidualTerminalFourCornerOptimumRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumSideTightCompletionUnderRouteSilenceFormalized',
    'leanResidualTerminalFourCornerOptimumExactCompletionValuesFormalized',
    'leanResidualTerminalFourCornerOptimumPromotionFirewallRetained',
    'leanResidualTerminalFourCornerSideTightCompletionAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualTerminalCoherentFourCornerBasisFormalized, true);
  assert.equal(status.leanResidualTerminalSquareLegitimacyFormalized, true);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 3);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-four-corner-side-tight-completion0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFourCornerSideTightCompletionAxiomAudit\.lean[\s\S]{0,1800}-eq 28/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFourCornerSideTightCompletion\.lean/u);
});

test('hostile side-tight-completion mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      '| .coherence mode => carrier.firstOptimumCoherenceFailure? observe mode',
      '| .coherence mode => carrier.firstOptimumModeMismatch? observe'),
    'exact-phase-query'],
    [source.replace(
      '| .quotientPromotion => carrier.firstOptimumModeMismatch? observe',
      '| .quotientPromotion => carrier.firstOptimumCoherenceFailure? observe .full'),
    'exact-phase-query'],
    [source.replace(
      'first : carrier.firstOptimumRoute? observe phase = some failure',
      'first : True'), 'proof-bearing-first-route'],
    [source.replace(
      'carrier.firstOptimumRoute? observe phase = none',
      'True'), 'computed-route-silence'],
    [source.replace(
      'carrier.firstOptimumModeMismatch?_sound observe',
      'carrier.firstOptimumCoherenceFailure?_sound observe .full'),
    'both-route-soundness'],
    [source.replace(
      'cases found : carrier.firstOptimumCoherenceFailure? observe mode with',
      'cases found : carrier.firstOptimumModeMismatch? observe with'),
    'total-completion-or-route'],
    [source.replace(
      'rw [tuple.noFailure] at first',
      'exact fun _ => False.elim (by cases first)'),
    'route-excludes-completion'],
    [source.replace(
      '(noRoute : carrier.NoOptimumCoherenceRoute observe mode)',
      '(noRoute : True)'),
    'conditional-side-tight-completion'],
    [source.replace(
      'carrier.sideTightCompletionExists observe .quotient noRoutes.2',
      'carrier.sideTightCompletionExists observe .full noRoutes.1'),
    'mode-separated-completions'],
    [source.replace('tuple.fullIncidenceValue', 'rfl'), 'exact-full-value'],
    [source.replace('tuple.quotientIncidenceValue', 'rfl'), 'exact-quotient-value'],
    [`${source}\naxiom routeShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef squareLegitimate : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`,
      'project-axiom'],
    [`${source}\ndef callerCertificate := true\n`,
      'caller-or-host-certificate'],
    [`${source}\ntheorem shortcut : True := by native_decide\n`,
      'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`,
      'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`,
      'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.notEqual(mutation, source, expected);
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
