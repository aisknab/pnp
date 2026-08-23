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
  'lean/PNP/ResidualTerminalFourCornerTightBasisMaximum.lean';
const COHERENCE_PATH =
  'lean/PNP/ResidualTerminalFourCornerOptimumCoherence.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFourCornerTightBasisMaximumAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFourCornerTightBasisMaximum.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_four_corner_tight_basis_maximum.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalFourCornerImplementationBasis',
  'TerminalFourCornerImplementationBasis.at',
  'TerminalFourCornerImplementationBasis.sizes',
  'TerminalOptimumCoherenceMode.minimumSizes',
  'TerminalOptimumCoherenceMode.delta',
  'TerminalOptimumCoherenceMode.profileMatchBool',
  'TerminalOptimumCoherenceMode.minimumAt_le_current',
  'BoundedCandidate.implementation',
  'TerminalProjectionFourCorners.minimumImplementationsAt',
  'TerminalProjectionFourCorners.mem_minimumImplementationsAt_sound',
  'TerminalProjectionFourCorners.mem_minimumImplementationsAt_complete',
  'TerminalProjectionFourCorners.mem_minimumImplementationsAt_iff',
  'TerminalProjectionFourCorners.minimumImplementationBases',
  'TerminalProjectionFourCorners.mem_minimumImplementationBases_iff',
  'TerminalFourCornerImplementationBasis.IsTightCoherent',
  'TerminalFourCornerCarrier.tightBasisBool',
  'TerminalFourCornerCarrier.tightBasisBool_eq_true_iff',
  'TerminalFourCornerCarrier.tightBasisFamily',
  'TerminalFourCornerCarrier.mem_tightBasisFamily_sound',
  'TerminalFourCornerCarrier.mem_tightBasisFamily_complete',
  'TerminalFourCornerCarrier.mem_tightBasisFamily_iff',
  'TerminalFourCornerCarrier.canonicalImplementationBasis',
  'TerminalFourCornerCarrier.canonicalImplementationBasis_at',
  'TerminalFourCornerCarrier.canonicalImplementationBasis_sizes',
  'TerminalFourCornerCarrier.canonicalImplementationBasis_isTightCoherent',
  'TerminalFourCornerCarrier.canonicalImplementationBasis_mem_tightFamily',
  'TerminalFourCornerCarrier.tightBasis_incidenceValue_eq_delta',
  'TerminalFourCornerCarrier.tightBasisValues',
  'TerminalFourCornerCarrier.mem_tightBasisValues_eq_delta',
  'signedMaximum?',
  'TerminalFourCornerCarrier.tightBasisMaximum?',
  'TerminalFourCornerCarrier.tightBasisMaximum?_eq_delta',
  'TerminalFourCornerCarrier.tightBasisMaximum?_full',
  'TerminalFourCornerCarrier.tightBasisMaximum?_quotient',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const COHERENCE_EXTENSIONS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.firstBasisCoherenceFailure?`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstBasisCoherenceFailure?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_eq_basis`,
]);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalOptimumCoherenceMode.minimumAt_le_current`,
  `${NAMESPACE}.TerminalProjectionFourCorners.mem_minimumImplementationsAt_sound`,
  `${NAMESPACE}.TerminalProjectionFourCorners.mem_minimumImplementationsAt_complete`,
  `${NAMESPACE}.TerminalProjectionFourCorners.mem_minimumImplementationsAt_iff`,
  `${NAMESPACE}.TerminalProjectionFourCorners.mem_minimumImplementationBases_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasisBool_eq_true_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.mem_tightBasisFamily_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.mem_tightBasisFamily_complete`,
  `${NAMESPACE}.TerminalFourCornerCarrier.mem_tightBasisFamily_iff`,
  `${NAMESPACE}.TerminalFourCornerCarrier.canonicalImplementationBasis_at`,
  `${NAMESPACE}.TerminalFourCornerCarrier.canonicalImplementationBasis_sizes`,
  `${NAMESPACE}.TerminalFourCornerCarrier.canonicalImplementationBasis_isTightCoherent`,
  `${NAMESPACE}.TerminalFourCornerCarrier.canonicalImplementationBasis_mem_tightFamily`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasis_incidenceValue_eq_delta`,
  `${NAMESPACE}.TerminalFourCornerCarrier.mem_tightBasisValues_eq_delta`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasisMaximum?_eq_delta`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasisMaximum?_full`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasisMaximum?_quotient`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstBasisCoherenceFailure?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_eq_basis`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.mem_allBoundedCandidates`,
  `${NAMESPACE}.terminalFullProfileMatchBool_complete`,
  `${NAMESPACE}.terminalQuotientProfileMatchBool_complete`,
  `${NAMESPACE}.terminalFullProfileMinimum_le`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_le`,
  `${NAMESPACE}.TerminalFourCornerSizes.numericallySideTight_iff_eq`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletionExists`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...COHERENCE_EXTENSIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  ...REUSED_DECLARATIONS,
]);

const PRIVATE_HELPERS = Object.freeze([
  'fourCornerProducts',
  'mem_fourCornerProducts_iff',
  'noFailureBool',
  'TerminalFourCornerCarrier.canonicalImplementationBasis_matches',
  'signedMax',
  'foldl_signedMax_eq_of_all_eq',
  'signedMaximum?_eq_some_of_mem_and_all_eq',
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
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|maximumCertificate|coherenceCertificate|routeCertificate|trustFlag)\b/u.test(stripped)) {
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
    'PNP.ResidualTerminalFourCornerSideTightCompletion',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const privateHelpers = [...stripped.matchAll(
    /^private\s+(?:structure|inductive|def|theorem)\s+([^\s({:]+)/gmu,
  )].map((match) => match[1]);
  if (JSON.stringify(privateHelpers) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const cornerList = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.minimumImplementationsAt',
  );
  const cornerComplete = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.mem_minimumImplementationsAt_complete',
  );
  const product = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.minimumImplementationBases',
  );
  const family = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.tightBasisFamily',
  );
  const familyExact = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.mem_tightBasisFamily_iff',
  );
  const canonical = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.canonicalImplementationBasis_isTightCoherent',
  );
  const signed = declarationBlock0(source, 'signedMaximum?');
  const maximum = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.tightBasisMaximum?_eq_delta',
  );
  const quotient = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.tightBasisMaximum?_quotient',
  );

  if (!/allBoundedCandidates inputs outputs \(corners\.at corner\)\.gateCount/u.test(cornerList)
      || !/profileMatchBool corners corner candidate\.implementation/u.test(cornerList)) {
    failures.push('corner-bounded-completeness');
  }
  if (!/candidate\.1\.val == \(mode\.minimumSizes corners\)\.at corner/u.test(cornerList)) {
    failures.push('exact-corner-minimum');
  }
  for (const token of [
    'boundedCandidateOfLE',
    'minimumAt_le_current',
    'mem_allBoundedCandidates',
  ]) if (!cornerComplete.includes(token)) failures.push('corner-completeness-proof');
  for (const corner of ['.meet', '.left', '.right', '.join']) {
    if (!product.includes(`minimumImplementationsAt mode ${corner}`)) {
      failures.push('complete-four-way-product');
    }
  }
  if (!/minimumImplementationBases mode\)\.filter/u.test(family)
      || !/carrier\.tightBasisBool observe mode/u.test(family)) {
    failures.push('coherence-filter');
  }
  if (!/basis ∈ carrier\.tightBasisFamily observe mode ↔/u.test(familyExact)
      || !/basis\.IsTightCoherent carrier observe mode/u.test(familyExact)) {
    failures.push('family-sound-complete');
  }
  if (!/NoOptimumCoherenceRoute observe mode/u.test(canonical)
      || !/firstOptimumCoherenceFailure\?_eq_basis/u.test(canonical)) {
    failures.push('canonical-route-silence');
  }
  if (!/\| \[\] => none/u.test(signed)
      || !/\| head :: tail => some \(tail\.foldl signedMax head\)/u.test(signed)
      || /some 0/u.test(signed)) {
    failures.push('signed-nonempty-maximum');
  }
  if (!/canonicalImplementationBasis_mem_tightFamily/u.test(maximum)
      || !/mem_tightBasisValues_eq_delta/u.test(maximum)
      || !/some \(mode\.delta/u.test(maximum)) {
    failures.push('complete-maximum-equals-delta');
  }
  if (!/\.quotient noRoute/u.test(quotient)
      || !/\.quotientDelta/u.test(quotient)) {
    failures.push('quotient-mode-separated');
  }
  if (/firstOptimumModeMismatch\?|NoOptimumPromotionRoute/u.test(stripped)) {
    failures.push('promotion-firewall-crossed');
  }
  if (/\b(?:fixedCoordinate|fixedCorner|singleCanonicalBasis|singletonFamily)\b/u.test(stripped)) {
    failures.push('hard-coded-family');
  }
  return [...new Set(failures)];
}

test('complete finite tight-basis family and signed maximum are source-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every public extension and reused dependency exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 45);
  assert.equal(PUBLIC_DECLARATIONS.length, 34);
  assert.equal(COHERENCE_EXTENSIONS.length, 3);
  assert.equal(REUSED_DECLARATIONS.length, 8);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFourCornerTightBasisMaximum\n',
  ), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalFourCornerTightBasisMaximum$/mu);
  const coherenceDeclarations = declarations0(await text0(COHERENCE_PATH));
  for (const name of COHERENCE_EXTENSIONS) {
    assert.equal(coherenceDeclarations.includes(name), true, name);
  }
});

test('compiled closure is approved for every tight-basis declaration', async () => {
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

test('regression covers alternate minima, both modes, completeness, and negative maxima', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'tightMaximumSwappedImplementation',
    'tightMaximumSwappedBasis',
    'minimumAt_le_current',
    'mem_minimumImplementationsAt_iff',
    'firstBasisCoherenceFailure?',
    'mem_tightBasisFamily_complete',
    'canonicalImplementationBasis_mem_tightFamily',
    'tightBasisMaximum?_full',
    'tightBasisMaximum?_quotient',
    'signedMaximum? [-5, -2, -9]',
    'signedMaximum? ([] : List Int)',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication pins the complete BN2 tight-basis maximum boundary', async () => {
  const [inventory, publication, docs] = await Promise.all([
    text0(INVENTORY_PATH).then(JSON.parse),
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const byName = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  for (const name of [...PUBLIC_DECLARATIONS, ...COHERENCE_EXTENSIONS]) {
    assert.equal(byName.has(name), true, name);
  }
  for (const name of MILESTONE_THEOREMS) {
    const entry = byName.get(name);
    assert.equal(entry?.kind, 'theorem', name);
    assert.equal(entry.axioms.some((axiom) => axiom.startsWith('PNP.')), false, name);
    assert.equal(entry.axioms.includes('Classical.choice'), false, name);
    assert.equal(entry.axioms.includes('sorryAx'), false, name);
  }
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-four-corner-tight-basis-maximum',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-four-corner-complete-tight-basis-maximum');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /complete finite tight-basis family/u);
  assert.match(milestone.scope, /full or quotient/u);
  assert.match(milestone.nonClaim, /BN2 square legitimacy/u);
  assert.match(milestone.nonClaim, /global no-outcome/u);
  assert.match(docs, /BN2-CoherentOptimum/u);
  assert.match(docs, /negative/u);
});

test('status earns only the local complete-family maximum edge', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalFourCornerArbitraryFamilyCoherenceFormalized',
    'leanResidualTerminalFourCornerExactMinimumFamilyEnumerated',
    'leanResidualTerminalFourCornerTightBasisFamilyComplete',
    'leanResidualTerminalFourCornerSignedTightBasisMaximumFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumEqualsDeltaFormalized',
    'leanResidualTerminalFourCornerTightBasisMaximumAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualTerminalFourCornerOptimumPromotionFirewallRetained, true);
  assert.equal(status.leanResidualTerminalSquareLegitimacyFormalized, true);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 3);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-four-corner-tight-basis-maximum0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFourCornerTightBasisMaximumAxiomAudit\.lean[\s\S]{0,1800}-eq 45/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFourCornerTightBasisMaximum\.lean/u);
});

test('hostile tight-basis mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('(corners.at corner).gateCount).filter',
      '0).filter'), 'corner-bounded-completeness'],
    [source.replace('mode.profileMatchBool corners corner candidate.implementation &&',
      'true &&'), 'corner-bounded-completeness'],
    [source.replace('candidate.1.val == (mode.minimumSizes corners).at corner',
      'candidate.1.val == (corners.at corner).gateCount'),
    'exact-corner-minimum'],
    [source.replace('(corners.minimumImplementationsAt mode .join)',
      '(corners.minimumImplementationsAt mode .meet)'),
    'complete-four-way-product'],
    [source.replace(').filter\n    (carrier.tightBasisBool observe mode)',
      ')'), 'coherence-filter'],
    [source.replace('| [] => none', '| [] => some 0'),
      'signed-nonempty-maximum'],
    [source.replace('some (mode.delta (carrier.optimizationCorners observe))',
      'some 0'), 'complete-maximum-equals-delta'],
    [source.replace('(noRoute : carrier.NoOptimumCoherenceRoute observe mode)',
      '(noRoute : True)'), 'canonical-route-silence'],
    [source.replace('observe .quotient noRoute', 'observe .full noRoute'),
      'quotient-mode-separated'],
    [source.replace('carrier.firstBasisCoherenceFailure? observe mode basis.at',
      'carrier.firstOptimumModeMismatch? observe'), 'promotion-firewall-crossed'],
    [`${source}\naxiom maximumShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef bn2SquareLegitimate : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`,
      'project-axiom'],
    [`${source}\ndef maximumCertificate := true\n`,
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
