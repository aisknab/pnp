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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalProperSupport.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalProperSupportAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalProperSupport.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_proper_support.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  'allTerminalSupportSeeds',
  'canonicalTerminalSupportSeed',
  'canonicalTerminalSupportSeed_mem',
  'mem_canonicalTerminalSupportSeed_iff',
  'terminalSupportLocalGain',
  'TerminalSupportProper',
  'TerminalSupportPositive',
  'terminalProperPositiveSupportBool',
  'terminalProperPositiveSupportBool_eq_true_iff',
  'TerminalProperPositiveSupport',
  'findTerminalProperPositiveSupport',
  'findTerminalProperPositiveSupport_sound',
  'findTerminalProperPositiveSupport_exists_of_seed',
  'findTerminalProperPositiveSupport_eq_none_iff',
  'findTerminalProperPositiveSupport_unique',
  'TerminalProperPositiveSupport.saturatedRecords',
  'TerminalProperPositiveSupport.extractedSupport',
  'TerminalProperPositiveSupport.saturatedRecords_closed',
  'TerminalProperPositiveSupport.physically_compatible',
  'TerminalProperPositiveSupport.gateCount_bounds',
  'TerminalProperPositiveSupport.extracted_semantics',
  'TerminalProperPositiveSupport.extracted_induced',
  'TerminalProperPositiveSupport.minimumReplacement',
  'TerminalProperPositiveSupport.minimumReplacement_equivalent',
  'TerminalProperPositiveSupport.referenceMinimum_lt_gateCount',
  'TerminalProperPositiveSupport.minimumReplacement_size_lt',
].map((name) => `${NAMESPACE}.${name}`));

// These canonical subset-order helpers were promoted for the later BCEL
// anchor-nucleus construction and are audited at that successor boundary.
const SOURCE_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.terminalListSubsets`,
  `${NAMESPACE}.filter_mem_terminalListSubsets`,
  ...PUBLIC_DECLARATIONS,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.allTerminalPrimitiveRecords`,
  `${NAMESPACE}.mem_allTerminalPrimitiveRecords`,
  `${NAMESPACE}.terminalSaturateRecords`,
  `${NAMESPACE}.terminalSaturateRecords_closed`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_gateCount`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_semantics`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_induced`,
  `${NAMESPACE}.Candidate.referenceMinimumReplacement_equivalent`,
  `${NAMESPACE}.Candidate.referenceMinimumReplacement_size`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.canonicalTerminalSupportSeed_mem`,
  `${NAMESPACE}.mem_canonicalTerminalSupportSeed_iff`,
  `${NAMESPACE}.terminalProperPositiveSupportBool_eq_true_iff`,
  `${NAMESPACE}.findTerminalProperPositiveSupport_sound`,
  `${NAMESPACE}.findTerminalProperPositiveSupport_exists_of_seed`,
  `${NAMESPACE}.findTerminalProperPositiveSupport_eq_none_iff`,
  `${NAMESPACE}.findTerminalProperPositiveSupport_unique`,
  `${NAMESPACE}.TerminalProperPositiveSupport.saturatedRecords_closed`,
  `${NAMESPACE}.TerminalProperPositiveSupport.physically_compatible`,
  `${NAMESPACE}.TerminalProperPositiveSupport.gateCount_bounds`,
  `${NAMESPACE}.TerminalProperPositiveSupport.extracted_semantics`,
  `${NAMESPACE}.TerminalProperPositiveSupport.extracted_induced`,
  `${NAMESPACE}.TerminalProperPositiveSupport.minimumReplacement_equivalent`,
  `${NAMESPACE}.TerminalProperPositiveSupport.referenceMinimum_lt_gateCount`,
  `${NAMESPACE}.TerminalProperPositiveSupport.minimumReplacement_size_lt`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.completeSaturatedTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_gateCount`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_semantics`,
  `${NAMESPACE}.extractSaturatedTerminalSupport_induced`,
  `${NAMESPACE}.Candidate.referenceMinimumReplacement_equivalent`,
  `${NAMESPACE}.Candidate.referenceMinimumReplacement_size`,
]);

const PRIVATE_HELPERS = Object.freeze([
  'terminalProperPositiveDecidable',
  'TerminalProperPositiveSeedResult',
  'firstTerminalProperPositiveSupport',
  'firstTerminalProperPositiveSupport_exists_of_mem',
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
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|dependencyCertificate|saturationCertificate|closureCertificate|searchCertificate|properCertificate|gainCertificate)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|supportCompletion|projectionSquare|squareLegitimate|saturatePositive|bcelReady|completeGainRoute|zeroSlackComplete|pccMinExact|polynomialProperSupportSearch)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalSupportExtraction',
    'PNP.NANDSlack',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(SOURCE_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const seeds = declarationBlock0(source, 'allTerminalSupportSeeds');
  const canonical = declarationBlock0(source, 'canonicalTerminalSupportSeed');
  const canonicalMember = declarationBlock0(source, 'canonicalTerminalSupportSeed_mem');
  const gain = declarationBlock0(source, 'terminalSupportLocalGain');
  const proper = declarationBlock0(source, 'TerminalSupportProper');
  const positive = declarationBlock0(source, 'TerminalSupportPositive');
  const search = declarationBlock0(source, 'findTerminalProperPositiveSupport');
  const complete = declarationBlock0(
    source,
    'findTerminalProperPositiveSupport_exists_of_seed',
  );
  const none = declarationBlock0(
    source,
    'findTerminalProperPositiveSupport_eq_none_iff',
  );
  const closed = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.saturatedRecords_closed',
  );
  const compatible = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.physically_compatible',
  );
  const semantics = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.extracted_semantics',
  );
  const induced = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.extracted_induced',
  );
  const replacement = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.minimumReplacement',
  );
  const replacementEquivalent = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.minimumReplacement_equivalent',
  );
  const replacementStrict = declarationBlock0(
    source,
    'TerminalProperPositiveSupport.minimumReplacement_size_lt',
  );

  if (!/terminalListSubsets[\s\S]*allTerminalPrimitiveRecords/u.test(seeds)) {
    failures.push('complete-seed-enumeration');
  }
  if (!/allTerminalPrimitiveRecords[\s\S]*\.filter select/u.test(canonical)
      || !/filter_mem_terminalListSubsets/u.test(canonicalMember)) {
    failures.push('canonical-selector-coverage');
  }
  if (!/extractSaturatedTerminalSupport candidate system seed[\s\S]*residualSlack extracted\.extractedCandidate\.toImplementation/u.test(gain)) {
    failures.push('exact-saturated-local-gain');
  }
  if (!/0 < extracted\.gateCount ∧ extracted\.gateCount < gates/u.test(proper)) {
    failures.push('nonempty-strict-properness');
  }
  if (!/0 < terminalSupportLocalGain candidate system seed/u.test(positive)) {
    failures.push('strict-positive-gain');
  }
  if (!/firstTerminalProperPositiveSupport candidate system[\s\S]*allTerminalSupportSeeds/u.test(search)) {
    failures.push('searches-full-seed-universe');
  }
  if (!/firstTerminalProperPositiveSupport_exists_of_mem candidate system[\s\S]*governed proper positive/u.test(complete)) {
    failures.push('search-completeness');
  }
  if (!/∀ seed,[\s\S]*seed ∈ allTerminalSupportSeeds[\s\S]*¬\(TerminalSupportProper[\s\S]*TerminalSupportPositive/u.test(none)) {
    failures.push('exact-none-specification');
  }
  if (!/terminalSaturateRecords_closed system support\.seed/u.test(closed)) {
    failures.push('saturated-closure');
  }
  if (!/completeSaturatedTerminalPhysicalSupport_compatible candidate system support\.seed/u.test(compatible)) {
    failures.push('physical-compatibility');
  }
  if (!/extractSaturatedTerminalSupport_semantics candidate system support\.seed/u.test(semantics)
      || !/extractSaturatedTerminalSupport_induced candidate system support\.seed/u.test(induced)) {
    failures.push('exact-open-semantics');
  }
  if (!/referenceMinimumReplacement/u.test(replacement)
      || !/Candidate\.referenceMinimumReplacement_equivalent/u.test(replacementEquivalent)
      || !/Candidate\.referenceMinimumReplacement_size[\s\S]*referenceMinimum_lt_gateCount/u.test(replacementStrict)) {
    failures.push('strict-equivalent-minimum-replacement');
  }
  if (/\b(?:startGate|endGate|gateOffset|selectedInterval|coordinateTable|fixedSeedTable)\b/u.test(stripped)) {
    failures.push('hard-coded-support-family');
  }
  return [...new Set(failures)];
}

test('proper-positive support search has one closed executable interface', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 26 new and 11 reused declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 37);
  assert.equal(PUBLIC_DECLARATIONS.length, 26);
  assert.equal(REUSED_DECLARATIONS.length, 11);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualTerminalProperSupport$/mu);
});

test('compiled closure is approved for every proper-support declaration', async () => {
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

test('regression covers canonical seeds, both search outcomes, exact gain, and replacement', async () => {
  const regression = stripLeanCommentsAndStrings0(await text0(REGRESSION_PATH));
  for (const token of [
    '(allTerminalSupportSeeds 1 3 1 0).length = 32',
    'canonicalTerminalSupportSeed 1 3 1 0 properSeedSelector = properSeed',
    'TerminalSupportProper properCandidate properSaturationSystem properSeed',
    'terminalSupportLocalGain properCandidate properSaturationSystem properSeed = 2',
    'properSearchFound = true',
    'properSearchFirstSeedMatches = true',
    'noProperSearchFound = false',
    'findTerminalProperPositiveSupport_eq_none_iff',
    'properWitness.extracted_semantics',
    'properWitness.minimumReplacement.program.size = 0',
    'properWitness.minimumReplacement_size_lt',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(regression, /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('status earns only governed proper-positive support search', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalProperSupportScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-canonical-primitive-record-seeds-with-exhaustive-reference-minimum-local-gain',
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
    ({ id }) => id === 'residual-terminal-proper-positive-support-search',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy anchor and exact remaining boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§2.2', '§3', '§10', 'g_C(U)', 'proper', 'positive local gain',
    'every Boolean-selected subset', 'exactly when no governed',
    'explicit terminal dependency system', 'not a polynomial algorithm',
    'full profile frontier', 'square legitimacy', 'SaturatePositive',
    'BCELReady', 'ZeroSlack', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-proper-support0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalProperSupportAxiomAudit\.lean[\s\S]{0,1800}-eq 37/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalProperSupport\.lean/u);
});

test('hostile proper-support mutations revoke milestone credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(source.replace(
    'terminalListSubsets\n    (allTerminalPrimitiveRecords inputs gates outputs profileWidth)',
    '[]',
  )).includes('complete-seed-enumeration'), true);
  assert.equal(validateSource0(source.replace(
    '(allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter select',
    '[]',
  )).includes('canonical-selector-coverage'), true);
  assert.equal(validateSource0(source.replace(
    'extractSaturatedTerminalSupport candidate system seed',
    'extractTerminalSupport candidate seed',
  )).includes('exact-saturated-local-gain'), true);
  assert.equal(validateSource0(source.replace(
    'extracted.gateCount < gates',
    'extracted.gateCount ≤ gates',
  )).includes('nonempty-strict-properness'), true);
  assert.equal(validateSource0(source.replace(
    '0 < terminalSupportLocalGain candidate system seed',
    '0 ≤ terminalSupportLocalGain candidate system seed',
  )).includes('strict-positive-gain'), true);
  assert.equal(validateSource0(source.replace(
    '(allTerminalSupportSeeds inputs gates outputs profileWidth) with',
    '[] with',
  )).includes('searches-full-seed-universe'), true);
  assert.equal(validateSource0(source.replace(
    'firstTerminalProperPositiveSupport_exists_of_mem candidate system\n      governed proper positive',
    'firstTerminalProperPositiveSupport_exists_of_mem candidate system\n      [] proper positive',
  )).includes('search-completeness'), true);
  assert.equal(validateSource0(source.replace(
    '∀ seed,\n        seed ∈ allTerminalSupportSeeds',
    '∃ seed,\n        seed ∈ allTerminalSupportSeeds',
  )).includes('exact-none-specification'), true);
  assert.equal(validateSource0(source.replace(
    'terminalSaturateRecords_closed system support.seed',
    'by exact fun _ _ _ _ _ => False.elim (by contradiction)',
  )).includes('saturated-closure'), true);
  assert.equal(validateSource0(source.replace(
    'Candidate.referenceMinimumReplacement_equivalent',
    'Equivalent.refl',
  )).includes('strict-equivalent-minimum-replacement'), true);
  assert.equal(validateSource0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateSource0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-helper-surface'), true);
  assert.equal(validateSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(`${source}\ndef hostLookup := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateSource0(`${source}\ndef fixedSeedTable := []\n`).includes('hard-coded-support-family'), true);
  assert.equal(validateSource0(`${source}\ntheorem squareLegitimate : True := True.intro\n`).includes('overclaim'), true);
  assert.equal(validateSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
