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
const CNF_PATH = 'lean/PNP/Concrete/CNF.lean';
const WORK_INPUT_PATH = 'lean/PNP/Concrete/CNFWorkInput.lean';
const VERIFIER_PATH = 'lean/PNP/Concrete/CNFVerifier.lean';
const CNF_AUDIT_PATH = 'lean-audit/PNPConcreteCNFAxiomAudit.lean';
const WORK_INPUT_AUDIT_PATH = 'lean-audit/PNPConcreteCNFWorkInputAxiomAudit.lean';
const VERIFIER_AUDIT_PATH = 'lean-audit/PNPConcreteCNFVerifierAxiomAudit.lean';

const CNF_TOKEN_HEADS = new Set(['bits', 'ofBits', 'ofBits_bits']);
const WORK_INPUT_TOKEN_HEADS = new Set(['workSymbol', 'workSymbol_first_second']);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function cnfFullName0(name) {
  if (CNF_TOKEN_HEADS.has(name)) return `PNP.Concrete.CNFToken.${name}`;
  return `PNP.Concrete.${name}`;
}

function workInputFullName0(name) {
  if (WORK_INPUT_TOKEN_HEADS.has(name)) return `PNP.Concrete.CNFToken.${name}`;
  return `PNP.Concrete.${name}`;
}

function verifierFullName0(name) {
  if (name === 'size_pair_normalized') return 'PNP.Concrete.BitString.size_pair_normalized';
  return `PNP.Concrete.${name}`;
}

function publicHeads0(source, qualify) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) => ({
    kind,
    name: qualify(name),
  }));
}

function validateClosedSource0(label, source, expectedImports) {
  const failures = [];
  if (JSON.stringify(imports0(source)) !== JSON.stringify(expectedImports)) failures.push(`${label}-imports`);
  if (hasLeanAssumptionDeclaration0(source)) failures.push(`${label}-assumption`);
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push(`${label}-unaudited-form`);
  if (/\b(?:sorry|admit|unsafe|native_decide)\b/u.test(stripLeanCommentsAndStrings0(source))) {
    failures.push(`${label}-shortcut`);
  }
  return failures;
}

function validateCNF0(source) {
  const failures = validateClosedSource0('cnf', source, ['PNP.Concrete.Complexity']);
  const compact = compact0(source);
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(compact.includes('inductive CNFToken where | f | t | sep | finish deriving BEq, DecidableEq, Repr'),
    'cnf-four-token-alphabet');
  require0(compact.includes('def bits : CNFToken → BitString | .f => [false, false] | .t => [true, true] | .sep => [false, true] | .finish => [true, false]'),
    'cnf-token-bit-code');
  require0(compact.includes('def checkEncodedCertificate (encodedFormula certificate : BitString) : Bool := match decodeEncodedCNF encodedFormula with | none => false | some formula => match decodeAssignmentCertificate certificate with | none => false | some assignment => checkCNF formula assignment'),
    'cnf-executable-encoded-checker');
  require0(compact.includes('def CNFSAT : Language := fun encodedFormula => ∃ formula, decodeEncodedCNF encodedFormula = some formula ∧ formula.Satisfiable'),
    'cnf-language-semantics');
  require0(compact.includes('theorem checkEncodedCertificate_eq_true_iff'),
    'cnf-checker-correctness');
  require0(compact.includes('theorem decodeEncodedCNF_canonical'),
    'cnf-canonical-formula-decoder');
  require0(compact.includes('theorem decodeAssignmentCertificate_canonical'),
    'cnf-canonical-certificate-decoder');
  require0(compact.includes('def cnfCertificateBound : NatPolynomial := NatPolynomial.linear 2 2'),
    'cnf-linear-certificate-bound');
  require0(compact.includes('theorem cnfSAT_iff_bounded_encoded_certificate'),
    'cnf-bounded-certificate-characterization');
  require0(!/\b(?:oracle|precompose|externalEncoder)\b/u.test(compact), 'cnf-no-oracle');
  return failures;
}

function validateWorkInput0(source) {
  const failures = validateClosedSource0('cnf-work-input', source,
    ['PNP.Concrete.CNF', 'PNP.Concrete.WorkInput']);
  const compact = compact0(source);
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(compact.includes('def pairedTokenLayout (formulaTokens assignmentTokens : List CNFToken) : List WorkSymbol :='),
    'work-input-explicit-layout');
  require0(compact.includes('def paddedFormulaTokenBits (tokens : List CNFToken) : BitString := encodeTokenPairs tokens ++ [false]'),
    'work-input-formula-pad');
  require0(compact.includes('def assignmentCertificateTokenBits (tokens : List CNFToken) : BitString := encodeTokenPairs tokens ++ CNFToken.finish.bits'),
    'work-input-certificate-finish');
  for (const theorem of [
    'encodeWorkRight_pairedTokenLayout',
    'packWorkSymbols_paired_flat_tokens',
    'packWorkSymbols_encoded_cnf_assignment',
    'pairedWorkTape_encoded_cnf_assignment',
  ]) require0(compact.includes(`theorem ${theorem}`), `work-input-missing:${theorem}`);
  require0(compact.includes('BitString.pair (encodeFormula formula) (encodeAssignmentCertificate assignment)'),
    'work-input-literal-canonical-pair');
  return failures;
}

function validateVerifier0(source) {
  const failures = validateClosedSource0('cnf-verifier', source, ['PNP.Concrete.CNF']);
  const compact = compact0(source);
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(compact.includes('def cnfPairInputBound : NatPolynomial := NatPolynomial.linear 6 6'),
    'verifier-pair-bound');
  require0(compact.includes('def cnfVerifierRuntimeBound (rawBound : NatPolynomial) : NatPolynomial := NatPolynomial.substitute rawBound cnfPairInputBound'),
    'verifier-runtime-substitution');
  require0(compact.includes('{ program := { inputMode := .paired decision := .machine rawMachine rawBound }'),
    'verifier-direct-paired-machine');
  require0(compact.includes('(BitString.pair input certificate) ≠ .timeout'),
    'verifier-bounded-totality');
  require0(compact.includes('(BitString.pair input certificate) = .accept ↔ checkEncodedCertificate input certificate = true'),
    'verifier-raw-correctness');
  require0(compact.includes('theorem cnf_inNP_of_rawMachine'), 'verifier-in-np-bridge');
  require0(!/\b(?:precompose|FunctionProgram|externalEncoder|oracle)\b/u.test(compact),
    'verifier-no-preprocessor');
  return failures;
}

test('concrete CNF semantics, raw layout, and verifier bridge are closed and shortcut-free', async () => {
  const [cnf, workInput, verifier] = await Promise.all([
    text0(CNF_PATH), text0(WORK_INPUT_PATH), text0(VERIFIER_PATH),
  ]);
  assert.deepEqual(validateCNF0(cnf), []);
  assert.deepEqual(validateWorkInput0(workInput), []);
  assert.deepEqual(validateVerifier0(verifier), []);
});

test('axiom transcripts cover every public CNF-layer head exactly once', async () => {
  const [cnf, workInput, verifier, cnfAudit, workInputAudit, verifierAudit] = await Promise.all([
    text0(CNF_PATH),
    text0(WORK_INPUT_PATH),
    text0(VERIFIER_PATH),
    text0(CNF_AUDIT_PATH),
    text0(WORK_INPUT_AUDIT_PATH),
    text0(VERIFIER_AUDIT_PATH),
  ]);
  const surfaces = [
    [publicHeads0(cnf, cnfFullName0), cnfAudit, 80],
    [publicHeads0(workInput, workInputFullName0), workInputAudit, 20],
    [publicHeads0(verifier, verifierFullName0), verifierAudit, 8],
  ];
  for (const [heads, audit, count] of surfaces) {
    const names = heads.map(({ name }) => name);
    assert.equal(heads.length, count);
    assert.deepEqual(printed0(audit), names);
    assert.equal(new Set(names).size, count);
    assert.deepEqual(imports0(audit), ['PNP']);
  }
});

test('PNP root reaches each completed CNF layer without activating a root claim', async () => {
  const [root, main] = await Promise.all([text0('lean/PNP.lean'), text0('lean/PNP/Main.lean')]);
  for (const moduleName of [
    'PNP.Concrete.CNF',
    'PNP.Concrete.CNFVerifier',
    'PNP.Concrete.CNFWorkInput',
  ]) assert.equal(imports0(root).includes(moduleName), true, moduleName);
  assert.doesNotMatch(main, /\b(?:theorem|axiom|def)\s+p_eq_np\b/u);
});

test('package and workflow enforce the fast CNF audit and all three exact transcripts', async () => {
  const [packageText, workflow] = await Promise.all([
    text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.match(packageText, /audits\/lean-concrete-cnf0\.test\.mjs/u);
  assert.match(workflow, /audits\/lean-concrete-cnf0\.test\.mjs/u);
  for (const [audit, count] of [
    ['PNPConcreteCNFAxiomAudit.lean', 80],
    ['PNPConcreteCNFWorkInputAxiomAudit.lean', 20],
    ['PNPConcreteCNFVerifierAxiomAudit.lean', 8],
  ]) {
    const start = workflow.indexOf(audit);
    assert.notEqual(start, -1, audit);
    assert.match(workflow.slice(start, start + 700),
      new RegExp(`grep -Fc 'does not depend on any axioms'\\)\" -eq ${count}\\b`, 'u'));
  }
});

test('bounded work-machine differential regression is reviewable and explicitly opt-in', async () => {
  const [regression, readme, packageText, workflow] = await Promise.all([
    text0('lean-regression/PNPConcreteCNFWorkExhaustive.lean'),
    text0('lean-regression/README.md'),
    text0('package.json'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.match(regression, /def samples : List BitString := bitsThrough 8/u);
  assert.match(regression, /#guard samples\.length == 511/u);
  assert.match(regression, /#guard findMismatch samples samples == none/u);
  assert.match(readme, /261,121/u);
  assert.doesNotMatch(packageText, /PNPConcreteCNFWorkExhaustive/u);
  assert.doesNotMatch(workflow, /PNPConcreteCNFWorkExhaustive/u);
});

test('legacy SAT is a non-authoritative label, not an axiom or concrete-CNF alias', async () => {
  const source = await text0('lean/PNP/Complexity.lean');
  assert.match(source, /^def SAT : Language := \{ name := "SAT" \}$/mu);
  assert.doesNotMatch(source, /^\s*axiom\s+SAT\b/mu);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(source), /CNFSAT/u);
});

test('static audit rejects semantic shortcuts and transcript drift', async () => {
  const [cnf, workInput, verifier, cnfAudit] = await Promise.all([
    text0(CNF_PATH), text0(WORK_INPUT_PATH), text0(VERIFIER_PATH), text0(CNF_AUDIT_PATH),
  ]);
  assert.equal(validateCNF0(`${cnf}\naxiom hidden : True\n`).includes('cnf-assumption'), true);
  assert.equal(validateCNF0(cnf.replace('NatPolynomial.linear 2 2', 'NatPolynomial.linear 0 0'))
    .includes('cnf-linear-certificate-bound'), true);
  assert.equal(validateWorkInput0(workInput.replace('encodeTokenPairs tokens ++ [false]', '[false]'))
    .includes('work-input-formula-pad'), true);
  assert.equal(validateVerifier0(verifier.replace('inputMode := .paired', 'inputMode := .inputOnly'))
    .includes('verifier-direct-paired-machine'), true);
  assert.equal(validateVerifier0(`${verifier}\ndef oracle := true\n`).includes('verifier-no-preprocessor'), true);
  assert.notDeepEqual(printed0(cnfAudit).slice(0, -1),
    publicHeads0(cnf, cnfFullName0).map(({ name }) => name));
});
