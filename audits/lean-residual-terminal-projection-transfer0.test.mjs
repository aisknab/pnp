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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalProjectionTransfer.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalProjectionTransferAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalProjectionTransfer.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_projection_transfer.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalProjectionFourCorners`,
  `${NAMESPACE}.TerminalProjectionFourCorners.fullDelta`,
  `${NAMESPACE}.TerminalProjectionFourCorners.quotientDelta`,
  `${NAMESPACE}.TerminalProjectionFourCorners.projectionExcess`,
  `${NAMESPACE}.terminalProjectionDefect_int`,
  `${NAMESPACE}.TerminalProjectionFourCorners.transferIdentity`,
  `${NAMESPACE}.TerminalProjectionFourCorners.constantCutEquation_of_defects`,
  `${NAMESPACE}.TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut`,
]);

const PRIVATE_HELPERS = Object.freeze(['intOfNat_natSub_of_le']);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalProjectionDefect_int`,
  `${NAMESPACE}.TerminalProjectionFourCorners.transferIdentity`,
  `${NAMESPACE}.TerminalProjectionFourCorners.constantCutEquation_of_defects`,
  `${NAMESPACE}.TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut`,
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
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|transferCertificate|projectionSound)\b/u.test(stripped)) {
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

function validateProjectionTransferSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualTerminalProjectionMinimum'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const corners = declarationBlock0(source, 'TerminalProjectionFourCorners');
  const full = declarationBlock0(source, 'TerminalProjectionFourCorners.fullDelta');
  const quotient = declarationBlock0(source, 'TerminalProjectionFourCorners.quotientDelta');
  const excess = declarationBlock0(source, 'TerminalProjectionFourCorners.projectionExcess');
  const cast = declarationBlock0(source, 'terminalProjectionDefect_int');
  const transfer = declarationBlock0(
    source, 'TerminalProjectionFourCorners.transferIdentity',
  );
  const constantCut = declarationBlock0(
    source, 'TerminalProjectionFourCorners.constantCutEquation_of_defects',
  );
  const positive = declarationBlock0(
    source, 'TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut',
  );

  if (!/system\s*:\s*TerminalProfileSystem inputs outputs profileWidth[\s\S]*projection\s*:\s*TerminalProfileProjection profileWidth[\s\S]*meet\s*:\s*Implementation inputs outputs[\s\S]*left\s*:\s*Implementation inputs outputs[\s\S]*right\s*:\s*Implementation inputs outputs[\s\S]*join\s*:\s*Implementation inputs outputs/u.test(corners)
      || /(?:Proof|Certificate|Sound|Valid|Legitimate|Saturated|Proper)/u.test(corners)) {
    failures.push('one-system-one-projection-data-square');
  }
  if (!/: Int\s*:=/u.test(full)
      || !/Minimum corners\.system corners\.left\)[\s\S]*\+[\s\S]*Minimum corners\.system corners\.right\)[\s\S]*-[\s\S]*Minimum corners\.system corners\.meet\)[\s\S]*-[\s\S]*Minimum corners\.system corners\.join\)/u.test(full)) {
    failures.push('signed-full-delta');
  }
  if (!/: Int\s*:=/u.test(quotient)
      || !/Minimum corners\.system corners\.projection[\s\S]*corners\.left\)[\s\S]*\+[\s\S]*corners\.right\)[\s\S]*-[\s\S]*corners\.meet\)[\s\S]*-[\s\S]*corners\.join\)/u.test(quotient)) {
    failures.push('signed-quotient-delta');
  }
  if (!/corners\.quotientDelta - corners\.fullDelta/u.test(excess)) {
    failures.push('projection-excess-orientation');
  }
  if (!/Int\.ofNat \(terminalProjectionDefect[\s\S]*=[\s\S]*Int\.ofNat \(terminalFullProfileMinimum[\s\S]*-[\s\S]*Int\.ofNat \(terminalQuotientProfileMinimum/u.test(cast)
      || !/terminalProjectionMinimum_mono/u.test(cast)
      || !/intOfNat_natSub_of_le/u.test(cast)) {
    failures.push('monotone-defect-cast');
  }
  if (!/Defect corners\.system corners\.projection[\s\S]*corners\.join\)[\s\S]*\+[\s\S]*corners\.meet\)[\s\S]*=[\s\S]*corners\.left\)[\s\S]*\+[\s\S]*corners\.right\)[\s\S]*\+[\s\S]*corners\.projectionExcess/u.test(transfer)
      || (transfer.match(/terminalProjectionDefect_int/gu) ?? []).length !== 4) {
    failures.push('four-corner-transfer-identity');
  }
  for (const premise of ['meetZero', 'leftZero', 'rightZero']) {
    if (!new RegExp(`\\(${premise} : terminalProjectionDefect[\\s\\S]*corners\\.${premise.replace('Zero', '')} = 0\\)`, 'u').test(constantCut)) {
      failures.push('constant-cut-premises');
      break;
    }
  }
  if (!/joinDefect : terminalProjectionDefect[\s\S]*corners\.join = defect/u.test(constantCut)
      || !/corners\.projectionExcess = Int\.ofNat defect/u.test(constantCut)
      || !/corners\.transferIdentity/u.test(constantCut)) {
    failures.push('constant-cut-equation');
  }
  if (!/positive : 0 < defect/u.test(positive)
      || !/0 < corners\.projectionExcess/u.test(positive)
      || !/constantCutEquation_of_defects/u.test(positive)
      || !/Int\.ofNat_lt\.2 positive/u.test(positive)) {
    failures.push('positive-excess-consequence');
  }
  return failures;
}

test('terminal projection transfer exposes the exact signed four-corner interface', async () => {
  assert.deepEqual(validateProjectionTransferSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all eight public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, PUBLIC_DECLARATIONS.length);
  assert.equal(PUBLIC_DECLARATIONS.length, 8);
  assert.match(await text0('lean/PNP.lean'), /^import PNP\.ResidualTerminalProjectionTransfer$/mu);
});

test('compiled closure is approved for every projection-transfer declaration', async () => {
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

test('regression covers signed, zero, lossless, constant-cut, and symmetry cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalProjectionTransfer_fullDelta_eq_neg_one',
    'terminalProjectionTransfer_quotientDelta_eq_zero',
    'terminalProjectionTransfer_projectionExcess_eq_one',
    'terminalProjectionDefect_int',
    '.transferIdentity',
    '.constantCutEquation_of_defects',
    '.projectionExcess_pos_of_constantCut',
    'terminalProjectionTransferAllZero',
    'terminalProjectionTransferLossless',
    'terminalProjectionTransferUnequalSidesSwapped',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u);
});

test('status earns only the bounded terminal projection-transfer edge', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualProjectionTransferFormalized',
    'leanResidualProjectionTransferAxiomAuditPassed',
    'leanResidualProjectionTransferSignedDeltasFormalized',
    'leanResidualProjectionTransferIdentityFormalized',
    'leanResidualProjectionTransferConstantCutFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualProjectionTransferScope,
    'all-finite-direct-wire-four-corner-terminal-profile-families-sharing-one-computed-observer-and-one-explicit-projection');
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
  assert.equal(status.projectSpecificAxiomInventory.length, 3);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-projection-transfer',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the legacy anchor and exact downstream boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§5.2', 'Mode firewall and transfer identity', 'signed integers',
    'four corners', 'constant-cut', 'proper support', 'SaturatePositive',
    'BCEL', 'ZeroSlack', 'polynomial runtime', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-projection-transfer0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalProjectionTransferAxiomAudit\.lean[\s\S]{0,1800}-eq 8/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalProjectionTransfer\.lean/u);
});

test('hostile mutations revoke signed transfer and constant-cut credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateProjectionTransferSource0(source.replace(
    ': Int :=\n  Int.ofNat (terminalFullProfileMinimum',
    ': Nat :=\n  terminalFullProfileMinimum',
  )).includes('signed-full-delta'), true);
  assert.equal(validateProjectionTransferSource0(source.replace(
    'corners.quotientDelta - corners.fullDelta',
    'corners.fullDelta - corners.quotientDelta',
  )).includes('projection-excess-orientation'), true);
  assert.equal(validateProjectionTransferSource0(source.replace(
    'corners.meet) -\n    Int.ofNat (terminalFullProfileMinimum corners.system corners.join)',
    'corners.join) -\n    Int.ofNat (terminalFullProfileMinimum corners.system corners.meet)',
  )).includes('signed-full-delta'), true);
  assert.equal(validateProjectionTransferSource0(source.replace(
    'projection : TerminalProfileProjection profileWidth',
    'leftProjection : TerminalProfileProjection profileWidth\n  rightProjection : TerminalProfileProjection profileWidth',
  )).includes('one-system-one-projection-data-square'), true);
  assert.equal(validateProjectionTransferSource0(source.replace(
    '(terminalProjectionMinimum_mono system projection current)',
    '(Nat.zero_le _)',
  )).includes('monotone-defect-cast'), true);
  assert.equal(validateProjectionTransferSource0(source.replace(
    'corners.left = 0)',
    'corners.left = defect)',
  )).includes('constant-cut-premises'), true);
  assert.equal(validateProjectionTransferSource0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateProjectionTransferSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateProjectionTransferSource0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-helper-surface'), true);
  assert.equal(validateProjectionTransferSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateProjectionTransferSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateProjectionTransferSource0(`${source}\ndef callerCertificate := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateProjectionTransferSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
