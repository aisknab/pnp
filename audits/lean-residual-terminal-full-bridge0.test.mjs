import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/ResidualTerminalFullBridge.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalFullBridgeAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalFullBridge.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_full_bridge.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalFullRealization`,
  `${NAMESPACE}.terminalize`,
  `${NAMESPACE}.terminalize_implementation`,
  `${NAMESPACE}.terminalize_gateCount`,
  `${NAMESPACE}.TerminalFullRealization.realize`,
  `${NAMESPACE}.TerminalFullRealization.realize_gateCount`,
  `${NAMESPACE}.TerminalFullRealization.realize_equivalent`,
  `${NAMESPACE}.TerminalFullRealization.realize_semantics`,
  `${NAMESPACE}.IsTerminalFullMinimum`,
  `${NAMESPACE}.referenceMinimumTerminalFullRealization`,
  `${NAMESPACE}.referenceMinimumTerminalFullRealization_gateCount`,
  `${NAMESPACE}.terminalFullMinimum`,
  `${NAMESPACE}.terminalFullMinimum_eq_referenceMinimum`,
  `${NAMESPACE}.terminalFullMinimum_spec`,
  `${NAMESPACE}.isTerminalFullMinimum_iff_eq_terminalFullMinimum`,
  `${NAMESPACE}.isTerminalFullMinimum_iff_eq_referenceMinimum`,
  `${NAMESPACE}.WholeSpanResidualWitness`,
  `${NAMESPACE}.referenceMinimumWholeSpanWitnessOfPositive`,
  `${NAMESPACE}.WholeSpanResidualWitness.strictEquivalentGain`,
  `${NAMESPACE}.WholeSpanResidualWitness.strictResidualDescent`,
  `${NAMESPACE}.residualSlack_pos_iff_exists_wholeSpanResidualWitness`,
  `${NAMESPACE}.residualSlack_eq_zero_iff_no_wholeSpanResidualWitness`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalize_implementation`,
  `${NAMESPACE}.terminalize_gateCount`,
  `${NAMESPACE}.TerminalFullRealization.realize_equivalent`,
  `${NAMESPACE}.TerminalFullRealization.realize_semantics`,
  `${NAMESPACE}.referenceMinimumTerminalFullRealization_gateCount`,
  `${NAMESPACE}.terminalFullMinimum_eq_referenceMinimum`,
  `${NAMESPACE}.terminalFullMinimum_spec`,
  `${NAMESPACE}.isTerminalFullMinimum_iff_eq_terminalFullMinimum`,
  `${NAMESPACE}.isTerminalFullMinimum_iff_eq_referenceMinimum`,
  `${NAMESPACE}.WholeSpanResidualWitness.strictResidualDescent`,
  `${NAMESPACE}.residualSlack_pos_iff_exists_wholeSpanResidualWitness`,
  `${NAMESPACE}.residualSlack_eq_zero_iff_no_wholeSpanResidualWitness`,
  `${NAMESPACE}.StrictEquivalentGain.strictResidualDescent`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `${NAMESPACE}.${head.name}`);
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
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) {
    failures.push('assumption-declaration');
  }
  if (hasPrivateLeanDeclaration0(source)) {
    failures.push('private-declaration');
  }
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|polynomialGainGenerator|completeGainRoute|pccminPolynomialExact|zeroSlackComplete)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateBridgeSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualGainStopping'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }

  const realization = declarationBlock0(source, 'TerminalFullRealization');
  const terminalize = declarationBlock0(source, 'terminalize');
  const minimum = declarationBlock0(source, 'IsTerminalFullMinimum');
  const minimumSpec = declarationBlock0(source, 'terminalFullMinimum_spec');
  const bridge = declarationBlock0(source, 'terminalFullMinimum_eq_referenceMinimum');
  const witness = declarationBlock0(source, 'WholeSpanResidualWitness');
  const descent = declarationBlock0(
    source, 'WholeSpanResidualWitness.strictResidualDescent',
  );
  const positive = declarationBlock0(
    source, 'residualSlack_pos_iff_exists_wholeSpanResidualWitness',
  );
  const zero = declarationBlock0(
    source, 'residualSlack_eq_zero_iff_no_wholeSpanResidualWitness',
  );

  if (!/implementation\s*:\s*Implementation inputs outputs[\s\S]*Equivalent implementation\.candidate\.program[\s\S]*implementation\.candidate\.directWireWord[\s\S]*current\.candidate\.program current\.candidate\.directWireWord/u.test(realization)) {
    failures.push('whole-semantics-realization');
  }
  if (!/implementation := current[\s\S]*Equivalent\.refl current\.candidate\.program[\s\S]*current\.candidate\.directWireWord/u.test(terminalize)) {
    failures.push('exact-terminalization');
  }
  if (!/∃ realization : TerminalFullRealization current,[\s\S]*realization\.implementation\.gateCount = gateCount[\s\S]*∀ realization : TerminalFullRealization current,[\s\S]*gateCount ≤ realization\.implementation\.gateCount/u.test(minimum)) {
    failures.push('independent-universal-minimum');
  }
  if (/referenceMinimum/u.test(stripLeanCommentsAndStrings0(minimum))) {
    failures.push('minimum-defined-by-reference');
  }
  if (!/IsTerminalFullMinimum current \(terminalFullMinimum current\)[\s\S]*referenceMinimumTerminalFullRealization current[\s\S]*referenceMinimum_le_of_equivalent/u.test(minimumSpec)) {
    failures.push('minimum-specification');
  }
  if (!/terminalFullMinimum current = referenceMinimum current/u.test(bridge)) {
    failures.push('terminal-mu-bridge');
  }
  if (!/realization\s*:\s*TerminalFullRealization current[\s\S]*realization\.implementation\.gateCount < current\.gateCount/u.test(witness)) {
    failures.push('strict-whole-span-witness');
  }
  if (!/residualSlack witness\.realization\.implementation < residualSlack current[\s\S]*strictEquivalentGain\.strictResidualDescent/u.test(descent)) {
    failures.push('strict-residual-descent');
  }
  if (!/0 < residualSlack current ↔ Nonempty \(WholeSpanResidualWitness current\)/u.test(positive)) {
    failures.push('positive-whole-span-equivalence');
  }
  if (!/residualSlack current = 0 ↔[\s\S]*¬Nonempty \(WholeSpanResidualWitness current\)/u.test(zero)) {
    failures.push('zero-whole-span-absence');
  }
  return failures;
}

test('terminal full-carrier bridge exposes the exact whole-semantics interface', async () => {
  assert.deepEqual(validateBridgeSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 22 public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, 22);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualTerminalFullBridge$/mu);
});

test('compiled closure is empty for every terminal full-carrier declaration', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(
    inventory.declarations.map((entry) => [entry.name, entry]),
  );
  for (const name of PUBLIC_DECLARATIONS) {
    assert.deepEqual(rows.get(name)?.axioms, [], name);
  }
});

test('regression covers boundary arities, exact terminalization, a strict witness, and stopping', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalZeroGateIdentityImplementation',
    'terminalRedundantWholeSpanWitness',
    'terminalize',
    'terminalFullMinimum_spec',
    'isTerminalFullMinimum_iff_eq_referenceMinimum',
    'residualSlack_pos_iff_exists_wholeSpanResidualWitness',
    'strictResidualDescent',
    'residualSlack_eq_zero_iff_no_wholeSpanResidualWitness',
    'terminalEmptyImplementation',
    'duplicatedIdentityImplementation',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(
    stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u,
  );
});

test('status retains the direct-wire terminal full-mode bridge', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  for (const field of [
    'leanResidualTerminalFullBridgeFormalized',
    'leanResidualTerminalFullBridgeAxiomAuditPassed',
    'leanResidualTerminalizationExactFormalized',
    'leanResidualTerminalFullMinimumSpecificationFormalized',
    'leanResidualTerminalMuBridgeFormalized',
    'leanResidualWholeSpanPositiveWitnessIffFormalized',
    'leanResidualWholeSpanStrictDescentFormalized',
    'leanResidualWholeSpanZeroAbsenceIffFormalized',
    'leanResidualTerminalQuotientCarrierFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalFullBridgeScope,
    'all-finite-direct-wire-implementations-with-complete-multi-output-semantics-and-exhaustive-reference-minimum-witnesses',
  );
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalSaturationFormalized',
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
    ({ id }) => id === 'residual-terminal-full-carrier-bridge',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the manuscript bridge and exact downstream boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§8',
    'RW-MuBridge',
    'whole implementation',
    'every input',
    'every output',
    'independent minimum specification',
    'quotient carrier',
    'proper supports',
    'BCEL',
    'ZeroSlack',
    'polynomial runtime',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-full-bridge0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalFullBridgeAxiomAudit\.lean[\s\S]{0,1200}does not depend on any axioms[\s\S]{0,300}-eq 22/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalFullBridge\.lean/u);
});

test('hostile mutations revoke partial semantics, fake minima, non-strict gains, closure, and scope credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateBridgeSource0(source.replace(
    'implementation.candidate.directWireWord\n      current.candidate.program',
    'current.candidate.directWireWord\n      current.candidate.program',
  )).includes('whole-semantics-realization'), true);
  assert.equal(validateBridgeSource0(source.replace(
    '∀ realization : TerminalFullRealization current,\n      gateCount ≤ realization.implementation.gateCount',
    '∀ _realization : TerminalFullRealization current,\n      True',
  )).includes('independent-universal-minimum'), true);
  assert.equal(validateBridgeSource0(source.replace(
    'referenceMinimum_le_of_equivalent current',
    'Nat.zero_le',
  )).includes('minimum-specification'), true);
  assert.equal(validateBridgeSource0(source.replace(
    'terminalFullMinimum current = referenceMinimum current',
    'terminalFullMinimum current = terminalFullMinimum current',
  )).includes('terminal-mu-bridge'), true);
  assert.equal(validateBridgeSource0(source.replace(
    'realization.implementation.gateCount < current.gateCount',
    'realization.implementation.gateCount ≤ current.gateCount',
  )).includes('strict-whole-span-witness'), true);
  assert.equal(validateBridgeSource0(source.replace(
    'residualSlack witness.realization.implementation < residualSlack current',
    'residualSlack witness.realization.implementation ≤ residualSlack current',
  )).includes('strict-residual-descent'), true);
  assert.equal(validateBridgeSource0(source.replace(
    '0 < residualSlack current ↔ Nonempty (WholeSpanResidualWitness current)',
    'True ↔ Nonempty (WholeSpanResidualWitness current)',
  )).includes('positive-whole-span-equivalence'), true);
  assert.equal(validateBridgeSource0(source.replace(
    '¬Nonempty (WholeSpanResidualWitness current)',
    'True',
  )).includes('zero-whole-span-absence'), true);
  assert.equal(validateBridgeSource0(`import PNP.ZeroSlack\n${source}`)
    .includes('closed-import'), true);
  assert.equal(validateBridgeSource0(`${source}\naxiom hidden : True\n`)
    .includes('assumption-declaration'), true);
  assert.equal(validateBridgeSource0(`${source}\nprivate theorem hidden : True := True.intro\n`)
    .includes('private-declaration'), true);
  assert.equal(validateBridgeSource0(`${source}\nexample : True := True.intro\n`)
    .includes('unaudited-declaration-form'), true);
  assert.equal(validateBridgeSource0(`${source}\ntheorem hidden : True := by native_decide\n`)
    .includes('forbidden-shortcut'), true);
  assert.equal(validateBridgeSource0(`${source}\ndef hostLookup := true\n`)
    .includes('caller-or-host-certificate'), true);
  assert.equal(validateBridgeSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`)
    .includes('overclaim'), true);
});
