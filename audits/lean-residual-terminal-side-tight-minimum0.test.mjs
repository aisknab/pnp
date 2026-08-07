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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalSideTightMinimum.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalSideTightMinimumAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalSideTightMinimum.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_side_tight_minimum.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalFourCornerSizes',
  'TerminalFourCornerSizes.incidenceValue',
  'TerminalFourCornerSizes.ComponentwiseLE',
  'TerminalFourCornerSizes.slack',
  'TerminalFourCornerSizes.NumericallySideTight',
  'TerminalFourCornerSizes.sideTightBool',
  'TerminalFourCornerSizes.tightValue?',
  'TerminalFourCornerSizes.componentwiseLE_refl',
  'TerminalFourCornerSizes.numericallySideTight_iff_eq',
  'TerminalFourCornerSizes.sideTightBool_eq_true_iff',
  'TerminalFourCornerSizes.tightValue?_eq_some_iff',
  'TerminalFourCornerSizes.tightValue?_sound',
  'TerminalFourCornerSizes.tightValue?_complete',
  'TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks',
  'TerminalFullFourCornerBasis',
  'TerminalFullFourCornerBasis.sizes',
  'TerminalProjectionFourCorners.fullMinimumSizes',
  'TerminalProjectionFourCorners.fullMinimumSizes_incidenceValue',
  'TerminalFullFourCornerBasis.minimum_componentwiseLE_sizes',
  'TerminalFullFourCornerBasis.incidenceValue_eq_fullDelta_add_slacks',
  'TerminalProjectionFourCorners.canonicalFullBasis',
  'TerminalProjectionFourCorners.canonicalFullBasis_sizes',
  'TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight',
  'TerminalProjectionFourCorners.canonicalFullBasis_tightValue?',
  'TerminalQuotientFourCornerBasis',
  'TerminalQuotientFourCornerBasis.sizes',
  'TerminalProjectionFourCorners.quotientMinimumSizes',
  'TerminalProjectionFourCorners.quotientMinimumSizes_incidenceValue',
  'TerminalQuotientFourCornerBasis.minimum_componentwiseLE_sizes',
  'TerminalQuotientFourCornerBasis.incidenceValue_eq_quotientDelta_add_slacks',
  'TerminalProjectionFourCorners.canonicalQuotientBasis',
  'TerminalProjectionFourCorners.canonicalQuotientBasis_sizes',
  'TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight',
  'TerminalProjectionFourCorners.canonicalQuotientBasis_tightValue?',
  'TerminalProjectionFourCorners.canonical_numericallySideTight_values',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerSizes.componentwiseLE_refl`,
  `${NAMESPACE}.TerminalFourCornerSizes.numericallySideTight_iff_eq`,
  `${NAMESPACE}.TerminalFourCornerSizes.sideTightBool_eq_true_iff`,
  `${NAMESPACE}.TerminalFourCornerSizes.tightValue?_eq_some_iff`,
  `${NAMESPACE}.TerminalFourCornerSizes.tightValue?_sound`,
  `${NAMESPACE}.TerminalFourCornerSizes.tightValue?_complete`,
  `${NAMESPACE}.TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks`,
  `${NAMESPACE}.TerminalProjectionFourCorners.fullMinimumSizes_incidenceValue`,
  `${NAMESPACE}.TerminalFullFourCornerBasis.minimum_componentwiseLE_sizes`,
  `${NAMESPACE}.TerminalFullFourCornerBasis.incidenceValue_eq_fullDelta_add_slacks`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalFullBasis_sizes`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalFullBasis_tightValue?`,
  `${NAMESPACE}.TerminalProjectionFourCorners.quotientMinimumSizes_incidenceValue`,
  `${NAMESPACE}.TerminalQuotientFourCornerBasis.minimum_componentwiseLE_sizes`,
  `${NAMESPACE}.TerminalQuotientFourCornerBasis.incidenceValue_eq_quotientDelta_add_slacks`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalQuotientBasis_sizes`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalQuotientBasis_tightValue?`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonical_numericallySideTight_values`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalProjectionFourCorners.fullDelta`,
  `${NAMESPACE}.TerminalProjectionFourCorners.quotientDelta`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison_gateCount`,
  `${NAMESPACE}.terminalFullProfileMinimum_le`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_le`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison_gateCount`,
  `${NAMESPACE}.terminalFullProfileMinimum_le`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_le`,
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
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|tightnessCertificate|minimumCertificate|coherenceCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|squareLegitimate|bn2SquareLegitimate|coherentCompletion|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialSideTight)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalProjectionSquare',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const privateHelpers = [...stripped.matchAll(/^private\s+(?:def|theorem)\s+([^\s({:]+)/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(privateHelpers) !== JSON.stringify([
    'intOfNat_eq_minimum_add_slack',
  ])) failures.push('private-helper-surface');

  const sizes = declarationBlock0(source, 'TerminalFourCornerSizes');
  const value = declarationBlock0(source, 'TerminalFourCornerSizes.incidenceValue');
  const order = declarationBlock0(source, 'TerminalFourCornerSizes.ComponentwiseLE');
  const slack = declarationBlock0(source, 'TerminalFourCornerSizes.slack');
  const tight = declarationBlock0(source, 'TerminalFourCornerSizes.NumericallySideTight');
  const recognizer = declarationBlock0(source, 'TerminalFourCornerSizes.sideTightBool');
  const extractor = declarationBlock0(source, 'TerminalFourCornerSizes.tightValue?');
  const identity = declarationBlock0(
    source,
    'TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks',
  );
  const fullBasis = declarationBlock0(source, 'TerminalFullFourCornerBasis');
  const quotientBasis = declarationBlock0(source, 'TerminalQuotientFourCornerBasis');
  const fullMinimum = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.fullMinimumSizes',
  );
  const quotientMinimum = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.quotientMinimumSizes',
  );
  const canonicalFull = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.canonicalFullBasis',
  );
  const canonicalQuotient = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.canonicalQuotientBasis',
  );
  const main = declarationBlock0(
    source,
    'TerminalProjectionFourCorners.canonical_numericallySideTight_values',
  );

  for (const field of ['meet', 'left', 'right', 'join']) {
    if (!new RegExp(`\\b${field}\\s*:\\s*Nat`, 'u').test(sizes)) {
      failures.push('four-named-corners');
    }
    if (!order.includes(`minimum.${field} ≤ sizes.${field}`)) {
      failures.push('componentwise-lower-bound');
    }
    if (!slack.includes(`${field} := sizes.${field} - minimum.${field}`)) {
      failures.push('componentwise-slack');
    }
    if (!tight.includes(`sizes.${field} = minimum.${field}`)) {
      failures.push('exact-tightness');
    }
    if (!recognizer.includes(`sizes.${field} == minimum.${field}`)) {
      failures.push('four-corner-recognizer');
    }
    if (!fullBasis.includes(`${field} : TerminalFullCarrierRealization`)) {
      failures.push('typed-full-basis');
    }
    if (!quotientBasis.includes(`${field} : TerminalQuotientComparison`)) {
      failures.push('typed-quotient-basis');
    }
    if (!fullMinimum.includes(`${field} := terminalFullProfileMinimum`)) {
      failures.push('exact-full-minima');
    }
    if (!quotientMinimum.includes(`${field} := terminalQuotientProfileMinimum`)) {
      failures.push('exact-quotient-minima');
    }
    if (!canonicalFull.includes(`${field} := terminalFullProfileMinimumRealization`)) {
      failures.push('canonical-full-attainment');
    }
    if (!canonicalQuotient.includes(`${field} := terminalQuotientProfileMinimumComparison`)) {
      failures.push('canonical-quotient-attainment');
    }
  }
  if (!/: Int\s*:=/u.test(value)
      || !/Int\.ofNat sizes\.left \+ Int\.ofNat sizes\.right - Int\.ofNat sizes\.meet -\s*Int\.ofNat sizes\.join/u.test(value)) {
    failures.push('signed-incidence-value');
  }
  if (!/if sizes\.sideTightBool minimum then/u.test(extractor)
      || !/some sizes\.incidenceValue/u.test(extractor)
      || !/else\s*none/u.test(extractor)) {
    failures.push('fail-closed-extractor');
  }
  if (!/minimum\.incidenceValue \+ Int\.ofNat \(sizes\.slack minimum\)\.left/u.test(identity)
      || !/Int\.ofNat \(sizes\.slack minimum\)\.right -/u.test(identity)
      || !/Int\.ofNat \(sizes\.slack minimum\)\.meet -/u.test(identity)
      || !/Int\.ofNat \(sizes\.slack minimum\)\.join/u.test(identity)) {
    failures.push('signed-slack-identity');
  }
  if (!/canonicalFullBasis_numericallySideTight/u.test(main)
      || !/canonicalFullBasis_tightValue\?/u.test(main)
      || !/canonicalQuotientBasis_numericallySideTight/u.test(main)
      || !/canonicalQuotientBasis_tightValue\?/u.test(main)) {
    failures.push('canonical-full-quotient-main');
  }
  return [...new Set(failures)];
}

test('side-tight minimum has one exact all-finite fail-closed interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith('import PNP.ResidualTerminalSideTightMinimum\n'), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 43);
  assert.equal(PUBLIC_DECLARATIONS.length, 35);
  assert.equal(REUSED_DECLARATIONS.length, 8);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalSideTightMinimum$/mu);
});

test('compiled closure is approved for every side-tight declaration', async () => {
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

test('regression covers exact values, canonical bases, symmetry, and fail-closed rejection', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'sideTightZeroSizes',
    'sideTightNegativeSizes',
    'sideTightSlackMinimum',
    'sideTightSlackSizes',
    'sideTightLeftLoose',
    'sideTightMeetLoose',
    'sideTightJoinLoose',
    'sideTightCancelingLoose',
    'sideTightConstantCut',
    'sideTightAllZero',
    'sideTightKeepAllCorners',
    'sideTightUnequalSides',
    'sideTightUnequalSidesSwapped',
    'canonicalFullBasis',
    'canonicalQuotientBasis',
    'incidenceValue_eq_minimum_add_slacks',
    'tightValue?_sound',
    'some (-1 : Int)',
    '= none',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact side-tight boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-side-tight-minimum-arithmetic',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-side-tight-minimum-arithmetic');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite terminal projection four-corner family/u);
  assert.match(milestone.scope, /independently attained/u);
  assert.match(milestone.nonClaim, /coherent four-corner basis/u);
  assert.match(milestone.nonClaim, /BN2 square legitimacy/u);
  assert.match(docs, /Side-tight four-corner minimum arithmetic/u);
});

test('status earns numerical arithmetic without coherent-basis overclaim', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalSideTightMinimumArithmeticFormalized',
    'leanResidualTerminalSideTightSignedSlackIdentityFormalized',
    'leanResidualTerminalSideTightFailClosedGateFormalized',
    'leanResidualTerminalSideTightCanonicalFullBasisFormalized',
    'leanResidualTerminalSideTightCanonicalQuotientBasisFormalized',
    'leanResidualTerminalSideTightMinimumAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalSideTightMinimumScope,
    'all-finite-terminal-projection-four-corner-families-and-independently-attained-full-and-quotient-minimum-bases',
  );
  for (const field of [
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalCoherentFourCornerBasisFormalized',
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
    ({ id }) => id === 'residual-terminal-side-tight-minimum-arithmetic',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy arithmetic edge and remaining proof boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§11.1',
    'BN2-CoherentOptimum',
    'tightBasisValueEqualsDelta',
    'sideTightOnlyNoOverclaim',
    'signed',
    'fail-closed',
    'independently attained',
    'coherent four-corner basis',
    'BN2 square legitimacy',
    'SaturatePositive',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-side-tight-minimum0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalSideTightMinimumAxiomAudit\.lean[\s\S]{0,1800}-eq 43/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalSideTightMinimum\.lean/u);
});

test('hostile source mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('  join : Nat\nderiving', 'deriving'), 'four-named-corners'],
    [source.replace('Int.ofNat sizes.right - Int.ofNat sizes.meet',
      'Int.ofNat sizes.right + Int.ofNat sizes.meet'), 'signed-incidence-value'],
    [source.replace('(sizes : TerminalFourCornerSizes) : Int :=',
      '(sizes : TerminalFourCornerSizes) : Nat :='), 'signed-incidence-value'],
    [source.replace('minimum.join ≤ sizes.join', 'minimum.join ≤ minimum.join'),
      'componentwise-lower-bound'],
    [source.replace('join := sizes.join - minimum.join',
      'join := minimum.join - sizes.join'), 'componentwise-slack'],
    [source.replace('sizes.join = minimum.join', 'sizes.join = sizes.join'),
      'exact-tightness'],
    [source.replace('sizes.join == minimum.join', 'true'),
      'four-corner-recognizer'],
    [source.replace('if sizes.sideTightBool minimum then', 'if true then'),
      'fail-closed-extractor'],
    [source.replace('some sizes.incidenceValue', 'some minimum.incidenceValue'),
      'fail-closed-extractor'],
    [source.replace('Int.ofNat (sizes.slack minimum).meet -',
      'Int.ofNat (sizes.slack minimum).meet +'), 'signed-slack-identity'],
    [source.replace('  join : TerminalFullCarrierRealization corners.system corners.join\n', ''),
      'typed-full-basis'],
    [source.replace('  join : TerminalQuotientComparison corners.system corners.projection corners.join\n', ''),
      'typed-quotient-basis'],
    [source.replace('join := terminalFullProfileMinimum corners.system corners.join',
      'join := 0'), 'exact-full-minima'],
    [source.replace('join := terminalQuotientProfileMinimum corners.system corners.projection\n      corners.join',
      'join := 0'), 'exact-quotient-minima'],
    [source.replace('join := terminalFullProfileMinimumRealization corners.system corners.join',
      'join := terminalCurrentFullCarrierRealization corners.system corners.join'),
    'canonical-full-attainment'],
    [source.replace('join := terminalQuotientProfileMinimumComparison corners.system\n      corners.projection corners.join',
      'join := terminalCurrentQuotientComparison corners.system\n      corners.projection corners.join'), 'canonical-quotient-attainment'],
    [source.replace('corners.canonicalQuotientBasis_tightValue?',
      'corners.canonicalFullBasis_tightValue?'), 'canonical-full-quotient-main'],
    [`${source}\naxiom minimumShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef coherentCompletion : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`, 'project-axiom'],
    [`${source}\ndef callerCertificate := true\n`, 'caller-or-host-certificate'],
    [`${source}\ntheorem shortcut : True := by native_decide\n`, 'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`,
      'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`, 'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
