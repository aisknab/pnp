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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalProjectionMinimum.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalProjectionMinimumAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalProjectionMinimum.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_projection_minimum.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.terminalFullProfileMatchBool`,
  `${NAMESPACE}.terminalQuotientProfileMatchBool`,
  `${NAMESPACE}.terminalFullProfileMatchBool_sound`,
  `${NAMESPACE}.terminalFullProfileMatchBool_complete`,
  `${NAMESPACE}.terminalQuotientProfileMatchBool_sound`,
  `${NAMESPACE}.terminalQuotientProfileMatchBool_complete`,
  `${NAMESPACE}.terminalCurrentFullCarrierRealization`,
  `${NAMESPACE}.terminalCurrentQuotientComparison`,
  `${NAMESPACE}.terminalFullProfileMinimumImplementation`,
  `${NAMESPACE}.terminalQuotientProfileMinimumImplementation`,
  `${NAMESPACE}.terminalFullProfileMinimum`,
  `${NAMESPACE}.terminalQuotientProfileMinimum`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison_gateCount`,
  `${NAMESPACE}.terminalFullProfileMinimum_le`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_le`,
  `${NAMESPACE}.terminalFullProfileMinimum_spec`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_spec`,
  `${NAMESPACE}.terminalProjectionMinimum_mono`,
  `${NAMESPACE}.terminalProjectionDefect`,
  `${NAMESPACE}.terminalQuotientMinimum_add_projectionDefect`,
  `${NAMESPACE}.terminalProjectionDefect_eq_zero_iff_minima_eq`,
  `${NAMESPACE}.terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum`,
  `${NAMESPACE}.terminalProfileMinima_eq_of_keepsAll`,
  `${NAMESPACE}.terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum`,
]);

const PRIVATE_HELPERS = Object.freeze([
  'firstProfileCandidate',
  'firstProfileCandidate_sound',
  'firstProfileCandidate_exists_of_mem',
  'firstProfileAt',
  'firstProfileAt_sound',
  'firstProfileAt_exists',
  'scanProfileSizes',
  'scanProfileSizes_sound',
  'scanProfileSizes_exists_of_candidate',
  'scanProfileSizes_minimal',
  'scanProfileSizes_global_minimal',
  'terminalFullProfileScan_exists',
  'terminalQuotientProfileScan_exists',
  'scan_terminalFullProfileMinimumImplementation',
  'scan_terminalQuotientProfileMinimumImplementation',
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalFullProfileMatchBool_complete`,
  `${NAMESPACE}.terminalQuotientProfileMatchBool_complete`,
  `${NAMESPACE}.terminalFullProfileMinimumRealization_gateCount`,
  `${NAMESPACE}.terminalQuotientProfileMinimumComparison_gateCount`,
  `${NAMESPACE}.terminalFullProfileMinimum_le`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_le`,
  `${NAMESPACE}.terminalFullProfileMinimum_spec`,
  `${NAMESPACE}.terminalQuotientProfileMinimum_spec`,
  `${NAMESPACE}.terminalProjectionMinimum_mono`,
  `${NAMESPACE}.terminalQuotientMinimum_add_projectionDefect`,
  `${NAMESPACE}.terminalProjectionDefect_eq_zero_iff_minima_eq`,
  `${NAMESPACE}.terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum`,
  `${NAMESPACE}.terminalProfileMinima_eq_of_keepsAll`,
  `${NAMESPACE}.terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `${NAMESPACE}.${head.name}`);
}

function privateHelpers0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return [...stripped.matchAll(/^private\s+(?:def|theorem)\s+([^\s({:]+)/gmu)]
    .map((match) => match[1]);
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
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|sorry|admit)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|minimumCertificate|projectionSound)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|properSupport|saturatePositive|completeGainRoute|zeroSlackComplete|pccMinExact)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateProjectionMinimumSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualTerminalModeFirewall'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const scan = source.slice(
    source.indexOf('private def firstProfileCandidate'),
    source.indexOf('/-! ## Full and quotient match predicates -/'),
  );
  const fullMatch = declarationBlock0(source, 'terminalFullProfileMatchBool');
  const quotientMatch = declarationBlock0(source, 'terminalQuotientProfileMatchBool');
  const fullMinimum = declarationBlock0(source, 'terminalFullProfileMinimumImplementation');
  const quotientMinimum = declarationBlock0(source, 'terminalQuotientProfileMinimumImplementation');
  const fullLower = declarationBlock0(source, 'terminalFullProfileMinimum_le');
  const quotientLower = declarationBlock0(source, 'terminalQuotientProfileMinimum_le');
  const monotonicity = declarationBlock0(source, 'terminalProjectionMinimum_mono');
  const defect = declarationBlock0(source, 'terminalProjectionDefect');
  const decomposition = declarationBlock0(source, 'terminalQuotientMinimum_add_projectionDefect');
  const liftBoundary = declarationBlock0(
    source, 'terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum',
  );
  const keepsAll = declarationBlock0(source, 'terminalProfileMinima_eq_of_keepsAll');
  const positive = declarationBlock0(
    source, 'terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum',
  );

  if (!/allCandidates inputs gateCount outputs/u.test(scan)
      || !/scanProfileSizes accepts bound/u.test(scan)
      || !/found\.gateCount ≤ gateCount/u.test(scan)
      || !/mem_allCandidates candidate/u.test(scan)) {
    failures.push('complete-bounded-scan');
  }
  if (!/equivalentBool candidate\.candidate current\.candidate[\s\S]*allTrue \(allFin profileWidth\)[\s\S]*system\.observe candidate coordinate[\s\S]*system\.observe current coordinate/u.test(fullMatch)
      || /projection\.keep/u.test(fullMatch)) {
    failures.push('full-match-all-coordinates');
  }
  if (!/equivalentBool candidate\.candidate current\.candidate[\s\S]*projection\.keep coordinate = true[\s\S]*boolEqual[\s\S]*else[\s\S]*true/u.test(quotientMatch)) {
    failures.push('quotient-match-kept-coordinates');
  }
  if (!/scanProfileSizes \(terminalFullProfileMatchBool system current\)[\s\S]*current\.gateCount[\s\S]*\| none => current/u.test(fullMinimum)
      || !/scanProfileSizes[\s\S]*terminalQuotientProfileMatchBool system projection current[\s\S]*current\.gateCount[\s\S]*\| none => current/u.test(quotientMinimum)) {
    failures.push('total-unreachable-fallback');
  }
  if (!/scanProfileSizes_global_minimal[\s\S]*terminalFullProfileMatchBool_complete full/u.test(fullLower)
      || !/scanProfileSizes_global_minimal[\s\S]*terminalQuotientProfileMatchBool_complete comparison/u.test(quotientLower)) {
    failures.push('universal-minimality');
  }
  if (!/terminalQuotientProfileMinimum_le[\s\S]*terminalFullProfileMinimumRealization[\s\S]*\.project/u.test(monotonicity)) {
    failures.push('projection-monotonicity');
  }
  if (!/terminalFullProfileMinimum system current -[\s\S]*terminalQuotientProfileMinimum system projection current/u.test(defect)) {
    failures.push('defect-orientation');
  }
  if (!/terminalQuotientProfileMinimum system projection current \+[\s\S]*terminalProjectionDefect system projection current =[\s\S]*terminalFullProfileMinimum system current/u.test(decomposition)) {
    failures.push('defect-decomposition');
  }
  if (!/TerminalCheckedFullLift comparison[\s\S]*terminalFullProfileMinimum_le\s*\n\s*lift\.fullRealization[\s\S]*lift\.fullRealization_realization/u.test(liftBoundary)) {
    failures.push('zero-defect-checked-lift');
  }
  if (!/checkedFullLift_of_keepsAll keepsAll[\s\S]*terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum/u.test(keepsAll)) {
    failures.push('lossless-projection');
  }
  if (!/0 < terminalProjectionDefect[\s\S]*¬TerminalCheckedFullLift comparison[\s\S]*Nat\.ne_of_gt positive/u.test(positive)) {
    failures.push('positive-defect-firewall');
  }
  return failures;
}

test('terminal projection minima expose the exact executable finite interface', async () => {
  assert.deepEqual(validateProjectionMinimumSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 27 public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, PUBLIC_DECLARATIONS.length);
  assert.equal(PUBLIC_DECLARATIONS.length, 27);
  assert.match(await text0('lean/PNP.lean'), /^import PNP\.ResidualTerminalProjectionMinimum$/mu);
});

test('compiled closure is approved for every projection-minimum declaration', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of PUBLIC_DECLARATIONS) {
    const row = rows.get(name);
    assert.ok(row, name);
    for (const axiom of row.axioms) assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
  }
});

test('regression covers empty, lossless, forgotten, semantic, and minimum cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalProjectionFullMinimum_eq_one',
    'terminalProjectionQuotientMinimum_eq_zero',
    'terminalProjectionForgottenCoordinate_defect_eq_one',
    'terminalFullProfileMinimumRealization_gateCount',
    'terminalQuotientProfileMinimumComparison_gateCount',
    '.realization.equivalent input output',
    'terminalFullProfileMinimum_le',
    'terminalQuotientProfileMinimum_le',
    'terminalProjectionMinimum_mono',
    'terminalProfileMinima_eq_of_keepsAll',
    'terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum',
    'terminalProjectionEmptySystem',
    'terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u);
});

test('status retains the finite terminal projection minimum beneath its earned successor', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualProjectionMinimumFormalized',
    'leanResidualProjectionMinimumAxiomAuditPassed',
    'leanResidualProjectionMinimumExecutableFullScanFormalized',
    'leanResidualProjectionMinimumExecutableQuotientScanFormalized',
    'leanResidualProjectionMinimumAttainmentFormalized',
    'leanResidualProjectionMinimumUniversalLowerBoundsFormalized',
    'leanResidualProjectionMinimumMonotonicityFormalized',
    'leanResidualProjectionDefectDecompositionFormalized',
    'leanResidualProjectionDefectZeroIffCheckedLiftAtMinimumFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualProjectionMinimumScope,
    'all-finite-direct-wire-implementations-with-computed-finite-profile-observers-explicit-projections-and-exhaustive-search-through-the-current-gate-count');
  assert.equal(status.leanResidualProjectionTransferFormalized, true);
  assert.equal(status.leanResidualTerminalSaturationFormalized, true);
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  for (const field of [
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
    ({ id }) => id === 'residual-terminal-projection-minimum',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the legacy anchor and exact downstream boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§5.1', 'Projection Monotonicity', 'exhaustive', 'current gate count',
    'full-profile minimum', 'quotient-profile minimum', 'projection defect',
    'checked full lift', 'proper support', 'SaturatePositive', 'BCEL',
    'polynomial runtime', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-projection-minimum0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalProjectionMinimumAxiomAudit\.lean[\s\S]{0,1800}-eq 27/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalProjectionMinimum\.lean/u);
});

test('hostile mutations revoke scan, profile, defect, and lifting credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateProjectionMinimumSource0(source.replace(
    'allCandidates inputs gateCount outputs',
    '[]',
  )).includes('complete-bounded-scan'), true);
  assert.equal(validateProjectionMinimumSource0(source.replace(
    'if projection.keep coordinate = true then',
    'if projection.keep coordinate = false then',
  )).includes('quotient-match-kept-coordinates'), true);
  assert.equal(validateProjectionMinimumSource0(source.replace(
    'terminalFullProfileMinimum system current -\n    terminalQuotientProfileMinimum system projection current',
    'terminalQuotientProfileMinimum system projection current -\n    terminalFullProfileMinimum system current',
  )).includes('defect-orientation'), true);
  assert.equal(validateProjectionMinimumSource0(source.replace(
    'terminalQuotientProfileMinimum_le\n    ((terminalFullProfileMinimumRealization system current).project',
    'terminalFullProfileMinimum_le\n    (terminalFullProfileMinimumRealization system current',
  )).includes('projection-monotonicity'), true);
  assert.equal(validateProjectionMinimumSource0(source.replace(
    'lift.fullRealization',
    'terminalCurrentFullCarrierRealization system current',
  )).includes('zero-defect-checked-lift'), true);
  assert.equal(validateProjectionMinimumSource0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateProjectionMinimumSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateProjectionMinimumSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateProjectionMinimumSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateProjectionMinimumSource0(`${source}\ndef callerCertificate := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateProjectionMinimumSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
